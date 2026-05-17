/- Port of examples/dexter2/Dexter2CPMM.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Examples.Dexter2.Dexter2FA12
import ConCert.Examples.FA2.FA2LegacyInterface
import ConCert.Examples.FA2.FA2Token

namespace ConCert.Examples.Dexter2.CPMM

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

abbrev UpdateTokenPoolInternal : Type :=
  List ConCert.Examples.FA2.BalanceOfResponse

abbrev TokenId : Type := ConCert.Examples.FA2.TokenId
abbrev BakerAddress : Type := Option Base.Address

structure AddLiquidityParam where
  owner : Base.Address
  minLqtMinted : Nat
  maxTokensDeposited : Nat
  add_deadline : Nat
  deriving Serializable

structure RemoveLiquidityParam where
  liquidity_to : Base.Address
  lqtBurned : Nat
  minXtzWithdrawn : Nat
  minTokensWithdrawn : Nat
  remove_deadline : Nat
  deriving Serializable

structure XtzToTokenParam where
  tokens_to : Base.Address
  minTokensBought : Nat
  xtt_deadline : Nat
  deriving Serializable

structure TokenToXtzParam where
  xtz_to : Base.Address
  tokensSold : Nat
  minXtzBought : Nat
  ttx_deadline : Nat
  deriving Serializable

structure TokenToTokenParam where
  outputDexterContract : Base.Address
  to_ : Base.Address
  minTokensBought_ : Nat
  tokensSold_ : Nat
  ttt_deadline : Nat
  deriving Serializable

structure SetBakerParam where
  baker : BakerAddress
  freezeBaker_ : Bool
  deriving Serializable

inductive DexterMsg where
  | AddLiquidity (param : @AddLiquidityParam Base)
  | RemoveLiquidity (param : @RemoveLiquidityParam Base)
  | XtzToToken (param : @XtzToTokenParam Base)
  | TokenToXtz (param : @TokenToXtzParam Base)
  | SetBaker (param : @SetBakerParam Base)
  | SetManager (new_manager : Base.Address)
  | SetLqtAddress (new_lqt_address : Base.Address)
  | UpdateTokenPool
  | TokenToToken (param : @TokenToTokenParam Base)
  deriving Serializable

abbrev Msg : Type := ConCert.Examples.FA2.FA2ReceiverMsg DexterMsg

structure State where
  tokenPool : Nat
  xtzPool : Nat
  lqtTotal : Nat
  selfIsUpdatingTokenPool : Bool
  freezeBaker : Bool
  manager : Base.Address
  tokenAddress : Base.Address
  tokenId : TokenId
  lqtAddress : Base.Address
  deriving Serializable

structure Setup where
  lqtTotal_ : Nat
  manager_ : Base.Address
  tokenAddress_ : Base.Address
  tokenId_ : TokenId
  deriving Serializable

abbrev Error : Type := Nat
def default_error : Error := 1
abbrev CPMMResult : Type := Result (@State Base × List (@ActionBody Base)) Error

def amount_to_N (amount : Amount) : Nat := amount.toNat
def N_to_amount (amount : Nat) : Amount := Int.ofNat amount

def checked_sub (n m : Nat) : Result Nat Error :=
  if n < m then .Err default_error else .Ok (n - m)

def checked_div (n m : Nat) : Result Nat Error :=
  if m == 0 then .Err default_error else .Ok (n / m)

def ceildiv (n m : Nat) : Result Nat Error :=
  if n % m == 0 then
    checked_div n m
  else
    match checked_div n m with
    | .Ok res => .Ok (res + 1)
    | .Err e => .Err e

def ceildiv_ (n m : Nat) : Nat :=
  if n % m == 0 then n / m else n / m + 1

def non_zero_amount (amt : Amount) : Bool := decide (0 < amt)

def call_liquidity_token
    (addr : Base.Address) (amt : Nat) (msg : @ConCert.Examples.Dexter2.FA12.Msg Base) :
    @ActionBody Base :=
  .act_call addr (N_to_amount amt) (serialize msg)

def mint_or_burn
    (null_address : Base.Address) (state : @State Base)
    (target : Base.Address) (quantity : Int) :
    Result (@ActionBody Base) Error :=
  if Base.address_eqb state.lqtAddress null_address then
    .Err default_error
  else
    let msg : @ConCert.Examples.Dexter2.FA12.Msg Base :=
      .msg_mint_or_burn { quantity := quantity, target := target }
    .Ok (call_liquidity_token state.lqtAddress 0 msg)

def call_to_token
    (token_addr : Base.Address) (amt : Nat) (msg : @ConCert.Examples.FA2.Msg Base) :
    @ActionBody Base :=
  .act_call token_addr (N_to_amount amt) (serialize msg)

def token_transfer
    (state : @State Base) (from_ to_ : Base.Address) (amount : Nat) :
    @ActionBody Base :=
  let dst : @ConCert.Examples.FA2.TransferDestination Base :=
    { to_ := to_, dst_token_id := state.tokenId, amount := amount }
  let transfer : @ConCert.Examples.FA2.Transfer Base :=
    { from_ := from_, txs := [dst], sender_callback_addr := none }
  call_to_token state.tokenAddress 0 (.msg_transfer [transfer])

def xtz_transfer (to_ : Base.Address) (amount : Nat) :
    Result (@ActionBody Base) Error :=
  if Base.address_is_contract to_ then
    .Err default_error
  else
    .Ok (.act_transfer to_ (N_to_amount amount))

def add_liquidity
    (null_address : Base.Address) (chain : Chain)
    (ctx : @ContractCallContext Base) (state : @State Base)
    (param : @AddLiquidityParam Base) : CPMMResult :=
  if state.selfIsUpdatingTokenPool then
    .Err default_error
  else if param.add_deadline <= chain.current_slot then
    .Err default_error
  else
    match checked_div (amount_to_N ctx.ctx_amount * state.lqtTotal) state.xtzPool with
    | .Err e => .Err e
    | .Ok lqt_minted =>
        match ceildiv (amount_to_N ctx.ctx_amount * state.tokenPool) state.xtzPool with
        | .Err e => .Err e
        | .Ok tokens_deposited =>
            if param.maxTokensDeposited < tokens_deposited then
              .Err default_error
            else if lqt_minted < param.minLqtMinted then
              .Err default_error
            else
              let new_state :=
                { state with
                  lqtTotal := state.lqtTotal + lqt_minted,
                  tokenPool := state.tokenPool + tokens_deposited,
                  xtzPool := state.xtzPool + amount_to_N ctx.ctx_amount }
              let op_token :=
                token_transfer state ctx.ctx_from ctx.ctx_contract_address tokens_deposited
              match mint_or_burn null_address state param.owner (Int.ofNat lqt_minted) with
              | .Ok op_lqt => .Ok (new_state, [op_token, op_lqt])
              | .Err e => .Err e

def remove_liquidity
    (null_address : Base.Address) (chain : Chain)
    (ctx : @ContractCallContext Base) (state : @State Base)
    (param : @RemoveLiquidityParam Base) : CPMMResult :=
  if state.selfIsUpdatingTokenPool then
    .Err default_error
  else if param.remove_deadline <= chain.current_slot then
    .Err default_error
  else if non_zero_amount ctx.ctx_amount then
    .Err default_error
  else
    match checked_div (param.lqtBurned * state.xtzPool) state.lqtTotal with
    | .Err e => .Err e
    | .Ok xtz_withdrawn =>
        match checked_div (param.lqtBurned * state.tokenPool) state.lqtTotal with
        | .Err e => .Err e
        | .Ok tokens_withdrawn =>
            if xtz_withdrawn < param.minXtzWithdrawn then
              .Err default_error
            else if tokens_withdrawn < param.minTokensWithdrawn then
              .Err default_error
            else
              match checked_sub state.lqtTotal param.lqtBurned with
              | .Err e => .Err e
              | .Ok new_lqtPool =>
                  match checked_sub state.tokenPool tokens_withdrawn with
                  | .Err e => .Err e
                  | .Ok new_tokenPool =>
                      match checked_sub state.xtzPool xtz_withdrawn with
                      | .Err e => .Err e
                      | .Ok new_xtzPool =>
                          match mint_or_burn null_address state ctx.ctx_from
                              (-(Int.ofNat param.lqtBurned)) with
                          | .Err e => .Err e
                          | .Ok op_lqt =>
                              let op_token :=
                                token_transfer state ctx.ctx_contract_address
                                  param.liquidity_to tokens_withdrawn
                              match xtz_transfer param.liquidity_to xtz_withdrawn with
                              | .Err e => .Err e
                              | .Ok op_xtz =>
                                  .Ok
                                    ({ state with
                                      tokenPool := new_tokenPool,
                                      xtzPool := new_xtzPool,
                                      lqtTotal := new_lqtPool },
                                    [op_lqt, op_token, op_xtz])

def xtz_to_token
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (param : @XtzToTokenParam Base) : CPMMResult :=
  if state.selfIsUpdatingTokenPool then
    .Err default_error
  else if param.xtt_deadline <= _chain.current_slot then
    .Err default_error
  else
    let paid := amount_to_N ctx.ctx_amount
    match checked_div (paid * 997 * state.tokenPool)
        (state.xtzPool * 1000 + paid * 997) with
    | .Err e => .Err e
    | .Ok tokens_bought =>
        if tokens_bought < param.minTokensBought then
          .Err default_error
        else
          match checked_sub state.tokenPool tokens_bought with
          | .Err e => .Err e
          | .Ok new_tokenPool =>
              let new_state :=
                { state with
                  xtzPool := state.xtzPool + paid,
                  tokenPool := new_tokenPool }
              let op := token_transfer state ctx.ctx_contract_address
                param.tokens_to tokens_bought
              .Ok (new_state, [op])

def token_to_xtz
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (param : @TokenToXtzParam Base) : CPMMResult :=
  if state.selfIsUpdatingTokenPool then
    .Err default_error
  else if param.ttx_deadline <= chain.current_slot then
    .Err default_error
  else if non_zero_amount ctx.ctx_amount then
    .Err default_error
  else
    match checked_div (param.tokensSold * 997 * state.xtzPool)
        (state.tokenPool * 1000 + param.tokensSold * 997) with
    | .Err e => .Err e
    | .Ok xtz_bought =>
        if xtz_bought < param.minXtzBought then
          .Err default_error
        else
          match checked_sub state.xtzPool xtz_bought with
          | .Err e => .Err e
          | .Ok new_xtzPool =>
              let op_token :=
                token_transfer state ctx.ctx_from ctx.ctx_contract_address param.tokensSold
              match xtz_transfer param.xtz_to xtz_bought with
              | .Err e => .Err e
              | .Ok op_tez =>
                  let new_state :=
                    { state with
                      tokenPool := state.tokenPool + param.tokensSold,
                      xtzPool := new_xtzPool }
                  .Ok (new_state, [op_token, op_tez])

def default_
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) : CPMMResult :=
  if state.selfIsUpdatingTokenPool then
    .Err default_error
  else
    .Ok ({ state with xtzPool := state.xtzPool + amount_to_N ctx.ctx_amount }, [])

def set_baker
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (param : @SetBakerParam Base) : CPMMResult :=
  if state.selfIsUpdatingTokenPool then
    .Err default_error
  else if non_zero_amount ctx.ctx_amount then
    .Err default_error
  else if !(Base.address_eqb ctx.ctx_from state.manager) then
    .Err default_error
  else if state.freezeBaker then
    .Err default_error
  else
    .Ok ({ state with freezeBaker := param.freezeBaker_ },
      set_delegate_call param.baker)

def set_manager
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (new_manager : Base.Address) : CPMMResult :=
  if state.selfIsUpdatingTokenPool then
    .Err default_error
  else if non_zero_amount ctx.ctx_amount then
    .Err default_error
  else if !(Base.address_eqb ctx.ctx_from state.manager) then
    .Err default_error
  else
    .Ok ({ state with manager := new_manager }, [])

def set_lqt_address
    (null_address : Base.Address) (_chain : Chain)
    (ctx : @ContractCallContext Base) (state : @State Base)
    (new_lqt_address : Base.Address) : CPMMResult :=
  if state.selfIsUpdatingTokenPool then
    .Err default_error
  else if non_zero_amount ctx.ctx_amount then
    .Err default_error
  else if !(Base.address_eqb ctx.ctx_from state.manager) then
    .Err default_error
  else if !(Base.address_eqb state.lqtAddress null_address) then
    .Err default_error
  else
    .Ok ({ state with lqtAddress := new_lqt_address }, [])

def update_token_pool
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) : CPMMResult :=
  if !(Base.address_eqb ctx.ctx_from ctx.ctx_origin) then
    .Err default_error
  else if non_zero_amount ctx.ctx_amount then
    .Err default_error
  else if state.selfIsUpdatingTokenPool then
    .Err default_error
  else
    let balance_of_request : ConCert.Examples.FA2.BalanceOfRequest :=
      { owner := ctx.ctx_contract_address, bal_req_token_id := state.tokenId }
    let balance_of_param : ConCert.Examples.FA2.BalanceOfParam :=
      { bal_requests := [balance_of_request],
        bal_callback := { blob := none, return_addr := ctx.ctx_contract_address } }
    let op := call_to_token state.tokenAddress 0 (.msg_balance_of balance_of_param)
    .Ok ({ state with selfIsUpdatingTokenPool := true }, [op])

def update_token_pool_internal
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (token_pool : UpdateTokenPoolInternal) : CPMMResult :=
  if (!state.selfIsUpdatingTokenPool) ||
      !(Base.address_eqb ctx.ctx_from state.tokenAddress) then
    .Err default_error
  else if non_zero_amount ctx.ctx_amount then
    .Err default_error
  else
    match token_pool with
    | [] => .Err default_error
    | x :: _ =>
        .Ok ({ state with tokenPool := x.balance, selfIsUpdatingTokenPool := false }, [])

def call_to_other_token
    (token_addr : Base.Address) (amount : Nat)
    (msg : @ConCert.Examples.FA2.FA2ReceiverMsg Base DexterMsg) :
    @ActionBody Base :=
  .act_call token_addr (N_to_amount amount) (serialize msg)

def token_to_token
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (param : @TokenToTokenParam Base) : CPMMResult :=
  if state.selfIsUpdatingTokenPool then
    .Err default_error
  else if non_zero_amount ctx.ctx_amount then
    .Err default_error
  else if param.ttt_deadline <= chain.current_slot then
    .Err default_error
  else
    match checked_div (param.tokensSold_ * 997 * state.xtzPool)
        (state.tokenPool * 1000 + param.tokensSold_ * 997) with
    | .Err e => .Err e
    | .Ok xtz_bought =>
        match checked_sub state.xtzPool xtz_bought with
        | .Err e => .Err e
        | .Ok new_xtzPool =>
            let new_state :=
              { state with
                tokenPool := state.tokenPool + param.tokensSold_,
                xtzPool := new_xtzPool }
            let op1 :=
              token_transfer state ctx.ctx_from ctx.ctx_contract_address param.tokensSold_
            let xtzToTokenParam : @XtzToTokenParam Base :=
              { tokens_to := param.to_,
                minTokensBought := param.minTokensBought_,
                xtt_deadline := param.ttt_deadline }
            let op2 :=
              call_to_other_token param.outputDexterContract xtz_bought
                (.other_msg (.XtzToToken xtzToTokenParam))
            .Ok (new_state, [op1, op2])

def receive
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base))
    (chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) : CPMMResult :=
  match maybe_msg with
  | some (.other_msg (.AddLiquidity param)) =>
      add_liquidity null_address chain ctx state param
  | some (.other_msg (.RemoveLiquidity param)) =>
      remove_liquidity null_address chain ctx state param
  | some (.other_msg (.SetBaker param)) =>
      set_baker set_delegate_call chain ctx state param
  | some (.other_msg (.SetManager new_manager)) =>
      set_manager chain ctx state new_manager
  | some (.other_msg (.SetLqtAddress new_lqt_address)) =>
      set_lqt_address null_address chain ctx state new_lqt_address
  | none =>
      default_ chain ctx state
  | some (.other_msg .UpdateTokenPool) =>
      update_token_pool chain ctx state
  | some (.other_msg (.XtzToToken param)) =>
      xtz_to_token chain ctx state param
  | some (.other_msg (.TokenToXtz param)) =>
      token_to_xtz chain ctx state param
  | some (.other_msg (.TokenToToken param)) =>
      token_to_token chain ctx state param
  | some (.receive_balance_of_param responses) =>
      update_token_pool_internal chain ctx state responses
  | _ =>
      .Err default_error

def init
    (null_address : Base.Address) (_chain : Chain)
    (_ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  .Ok
    { tokenPool := 0,
      xtzPool := 0,
      lqtTotal := setup.lqtTotal_,
      selfIsUpdatingTokenPool := false,
      freezeBaker := false,
      manager := setup.manager_,
      tokenAddress := setup.tokenAddress_,
      tokenId := setup.tokenId_,
      lqtAddress := null_address }

def contract
    (null_address : Base.Address)
    (set_delegate_call : BakerAddress → List (@ActionBody Base)) :
    @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init null_address,
    receive := receive null_address set_delegate_call }

end ConCert.Examples.Dexter2.CPMM
