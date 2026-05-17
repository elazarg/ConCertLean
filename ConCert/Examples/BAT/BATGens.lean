/- Port of examples/bat/BATGens.v over the local-chain backend. -/

import ConCert.Execution.Test.TraceGens
import ConCert.Examples.BAT.BAT
import ConCert.Examples.BAT.BATPrinters
import ConCert.Examples.EIP20.EIP20TokenGens

namespace ConCert.Examples.BAT.Gens

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.LocalBlockchain
open ConCert.Execution.Test.TestUtils
open ConCert.Execution.Test.TraceGens
open ConCert.Execution.ResultMonad
open ConCert.Examples.BAT

abbrev TestBase := ConCert.Execution.Test.TraceGens.TestBase
abbrev TestAddress := ConCert.Execution.Test.TraceGens.TestAddress
abbrev TestAction := ConCert.Execution.Test.TraceGens.TestAction
abbrev TestLocalChainBuilder := ConCert.Execution.Test.TraceGens.TestLocalChainBuilder
abbrev TestAddBlockError := ConCert.Execution.Test.TraceGens.TestAddBlockError

local instance : ChainBase := TestBase

def trace_length : Nat := 20
def creator_addr : TestAddress := fixedUser10
def fund_addr : TestAddress := fixedUser10
def bat_fund_addr : TestAddress := fixedUser11
def holder2 : TestAddress := fixedLocalAddress 12 (by decide)
def holder3 : TestAddress := fixedLocalAddress 13 (by decide)
def holder4 : TestAddress := fixedLocalAddress 14 (by decide)
def bat_contract_addr : TestAddress := fixedContractBase

def accounts : List TestAddress :=
  [creator_addr, bat_fund_addr, holder2, holder3, holder4]

def accounts_total_balance : Nat := 300
def bat_addr_refundable : Bool := false
def bat_addr_fundable : Bool := false
def eip20_transactions_before_finalized : Bool := false

def gAccount : G TestAddress :=
  Plausible.Gen.elements accounts (by simp [accounts])

def account_balance (env : @Environment TestBase) (addr : TestAddress) :
    Amount :=
  env.env_account_balances addr

def bat_call (caller : TestAddress) (amount : Amount) (msg : @Msg TestBase) :
    TestAction :=
  { act_origin := caller,
    act_from := caller,
    act_body := .act_call bat_contract_addr amount (serialize msg) }

def bat_setup : @Setup TestBase :=
  { batFund := 20,
    fundDeposit_ := fund_addr,
    batFundDeposit_ := bat_fund_addr,
    fundingStart_ := 0,
    fundingEnd_ := 10,
    tokenExchangeRate_ := 3,
    tokenCreationCap_ := 100,
    tokenCreationMin_ := 30 }

def initial_bat_header : @BlockHeader TestBase :=
  nextBlockHeader (lc_initial AddrSize) creator_addr (accounts_total_balance : Amount)

def initial_bat_actions : List TestAction :=
  [ transferAction creator_addr bat_fund_addr 25,
    transferAction creator_addr holder2 25,
    transferAction creator_addr holder3 25,
    transferAction creator_addr holder4 25,
    { act_origin := creator_addr,
      act_from := creator_addr,
      act_body := create_deployment 0
        (Original.contract (Base := TestBase)) bat_setup } ]

def bat_chain_result : Result TestLocalChainBuilder TestAddBlockError :=
  add_block AddrSize DepthFirst (lcb_initial AddrSize)
    initial_bat_header initial_bat_actions

def get_bat_state (cb : TestLocalChainBuilder) : Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase)
    (lc_to_env AddrSize cb.lcb_lc) bat_contract_addr

def get_bat_state_from_env
    (env : @Environment TestBase) : Option (@State TestBase) :=
  ConCert.Execution.Test.TestUtils.get_contract_state
    (Base := TestBase) (S := @State TestBase) env bat_contract_addr

def address_ne (a b : TestAddress) : Bool :=
  !(TestBase.address_eqb a b)

def is_fundable_account (env : @Environment TestBase) (addr : TestAddress) :
    Bool :=
  0 < account_balance env addr &&
    (bat_addr_fundable || address_ne addr bat_fund_addr)

def is_refundable_account (_state : @State TestBase)
    (p : TestAddress × TokenValue) : Bool :=
  0 < p.2 && (bat_addr_refundable || address_ne p.1 bat_fund_addr)

def get_fundable_accounts (env : @Environment TestBase) : List TestAddress :=
  accounts.filter (is_fundable_account env)

def get_refundable_accounts (state : @State TestBase) : List TestAddress :=
  ((FMap.elements (balances state)).filter (is_refundable_account state)).map Prod.fst

def gFundableAccount (env : @Environment TestBase) : GOpt TestAddress :=
  elems_opt (get_fundable_accounts env)

def gRefundableAccount (state : @State TestBase) : GOpt TestAddress :=
  elems_opt (get_refundable_accounts state)

def remaining_tokens (state : @State TestBase) : Nat :=
  state.tokenCreationCap - total_supply state

def max_funding_amount (state : @State TestBase) : Nat :=
  if state.tokenExchangeRate == 0 then
    0
  else
    remaining_tokens state / state.tokenExchangeRate

def gCreateTokens (env : @Environment TestBase) (state : @State TestBase) :
    GOpt (TestAddress × Amount × @Msg TestBase) := (do
  let current_slot := env.current_slot + 1
  if state.isFinalized ||
      current_slot < state.fundingStart ||
      state.fundingEnd < current_slot ||
      state.tokenExchangeRate == 0 ||
      remaining_tokens state < state.tokenExchangeRate then
    return none
  else
    match ← gFundableAccount env with
    | none => return none
    | some from_addr =>
        let upper := Nat.min (account_balance env from_addr).toNat
          (max_funding_amount state)
        if h : 1 ≤ upper then
          let value ← chooseNatBetween 1 upper h
          return some (from_addr, Int.ofNat value, .create_tokens)
        else
          return none :
    G (Option (TestAddress × Amount × @Msg TestBase)))

def gCreateTokensInvalid (env : @Environment TestBase)
    (_state : @State TestBase) :
    GOpt (TestAddress × Amount × @Msg TestBase) := (do
  match ← gFundableAccount env with
  | none => return none
  | some from_addr =>
      let upper := (account_balance env from_addr).toNat
      if h : 1 ≤ upper then
        let value ← chooseNatBetween 1 upper h
        return some (from_addr, Int.ofNat value, .create_tokens)
      else
        return none :
    G (Option (TestAddress × Amount × @Msg TestBase)))

def gRefund (env : @Environment TestBase) (state : @State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  let current_slot := env.current_slot + 1
  if state.isFinalized ||
      current_slot ≤ state.fundingEnd ||
      state.tokenCreationMin ≤ total_supply state then
    return none
  else
    match ← gRefundableAccount state with
    | none => return none
    | some from_addr => return some (from_addr, .refund) :
    G (Option (TestAddress × @Msg TestBase)))

def gRefundInvalid (_env : @Environment TestBase)
    (_state : @State TestBase) : G (TestAddress × @Msg TestBase) := do
  let from_addr ← gAccount
  return (from_addr, .refund)

def gFinalize (env : @Environment TestBase) (state : @State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  let current_slot := env.current_slot + 1
  if state.isFinalized ||
      total_supply state < state.tokenCreationMin ||
      (current_slot ≤ state.fundingEnd &&
        !(total_supply state == state.tokenCreationCap)) then
    return none
  else
    return some (state.fundDeposit, .finalize) :
    G (Option (TestAddress × @Msg TestBase)))

def gFinalizeInvalid (_env : @Environment TestBase)
    (_state : @State TestBase) : G (TestAddress × @Msg TestBase) := do
  let from_addr ← gAccount
  return (from_addr, .finalize)

def gTransfer (env : @Environment TestBase) (state : @State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  if eip20_transactions_before_finalized || state.isFinalized then
    let p ← ConCert.Examples.EIP20.EIP20Token.Gens.gTransfer env state.token_state
    return some (p.1, .tokenMsg p.2)
  else
    return none :
    G (Option (TestAddress × @Msg TestBase)))

def gApprove (state : @State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  if eip20_transactions_before_finalized || state.isFinalized then
    match ← ConCert.Examples.EIP20.EIP20Token.Gens.gApprove state.token_state with
    | some (caller, msg) => return some (caller, .tokenMsg msg)
    | none => return none
  else
    return none :
    G (Option (TestAddress × @Msg TestBase)))

def gTransferFrom (state : @State TestBase) :
    GOpt (TestAddress × @Msg TestBase) := (do
  if eip20_transactions_before_finalized || state.isFinalized then
    match ← ConCert.Examples.EIP20.EIP20Token.Gens.gTransferFrom state.token_state with
    | some (caller, msg) => return some (caller, .tokenMsg msg)
    | none => return none
  else
    return none :
    G (Option (TestAddress × @Msg TestBase)))

def gBATGeneratedMsg (env : @Environment TestBase) (state : @State TestBase) :
    GOpt (TestAddress × Amount × @Msg TestBase) := (do
  let choice ← chooseNatBetween 0 5 (by decide)
  match choice with
  | 0 =>
      match ← gTransfer env state with
      | some (caller, msg) => return some (caller, 0, msg)
      | none => return none
  | 1 =>
      match ← gTransferFrom state with
      | some (caller, msg) => return some (caller, 0, msg)
      | none => return none
  | 2 =>
      match ← gApprove state with
      | some (caller, msg) => return some (caller, 0, msg)
      | none => return none
  | 3 => gCreateTokens env state
  | 4 =>
      match ← gRefund env state with
      | some (caller, msg) => return some (caller, 0, msg)
      | none => return none
  | _ =>
      match ← gFinalize env state with
      | some (caller, msg) => return some (caller, 0, msg)
      | none => return none :
    G (Option (TestAddress × Amount × @Msg TestBase)))

def gBATGeneratedInvalidMsg
    (env : @Environment TestBase) (state : @State TestBase) :
    GOpt (TestAddress × Amount × @Msg TestBase) := (do
  let choice ← chooseNatBetween 0 5 (by decide)
  match choice with
  | 0 =>
      let p ← ConCert.Examples.EIP20.EIP20Token.Gens.gTransfer env state.token_state
      return some (p.1, 0, .tokenMsg p.2)
  | 1 =>
      match ← ConCert.Examples.EIP20.EIP20Token.Gens.gTransferFrom state.token_state with
      | some (caller, msg) => return some (caller, 0, .tokenMsg msg)
      | none => return none
  | 2 =>
      match ← ConCert.Examples.EIP20.EIP20Token.Gens.gApprove state.token_state with
      | some (caller, msg) => return some (caller, 0, .tokenMsg msg)
      | none => return none
  | 3 => gCreateTokensInvalid env state
  | 4 =>
      let p ← gRefundInvalid env state
      return some (p.1, 0, p.2)
  | _ =>
      let p ← gFinalizeInvalid env state
      return some (p.1, 0, p.2) :
    G (Option (TestAddress × Amount × @Msg TestBase)))

def gBATActionValid (env : @Environment TestBase) : GOpt TestAction := (do
  match get_bat_state_from_env env with
  | none => return none
  | some state =>
      match ← gBATGeneratedMsg env state with
      | none => return none
      | some (caller, value, msg) => return some (bat_call caller value msg) :
    G (Option TestAction))

def gBATActionInvalid (env : @Environment TestBase) : GOpt TestAction := (do
  match get_bat_state_from_env env with
  | none => return none
  | some state =>
      match ← gBATGeneratedInvalidMsg env state with
      | none => return none
      | some (caller, value, msg) => return some (bat_call caller value msg) :
    G (Option TestAction))

def gBATAction (env : @Environment TestBase) : GOpt TestAction := (do
  let choice ← chooseNatBetween 0 999 (by decide)
  if choice < 65 then
    gBATActionInvalid env
  else
    match ← gBATActionValid env with
    | some act =>
        if choice < 70 then
          let caller := act.act_from
          match act.act_body with
          | .act_call to_ _ msg =>
              let upper := (account_balance env caller).toNat
              let amount ← chooseNatBetween 0 upper (Nat.zero_le upper)
              return some
                { act with act_body := .act_call to_ (Int.ofNat amount) msg }
          | _ => return none
        else
          return some act
    | none => gBATActionInvalid env :
    G (Option TestAction))

def gBATSetup : G (@Setup TestBase) := do
  let fundingStart ← chooseNatBetween 0 (trace_length - 1) (by decide)
  let fundingEnd ← chooseNatBetween 0 (trace_length - 1) (by decide)
  let exchangeRate ← chooseNatBetween 1 accounts_total_balance (by decide)
  let initSupply ← chooseNatBetween 0 accounts_total_balance (Nat.zero_le _)
  let tokenMin ← chooseNatBetween 0 accounts_total_balance (Nat.zero_le _)
  let tokenCap ← chooseNatBetween 0 accounts_total_balance (Nat.zero_le _)
  return {
    batFund := initSupply,
    fundDeposit_ := fund_addr,
    batFundDeposit_ := bat_fund_addr,
    fundingStart_ := fundingStart,
    fundingEnd_ := fundingEnd,
    tokenExchangeRate_ := exchangeRate,
    tokenCreationCap_ := tokenCap,
    tokenCreationMin_ := tokenMin }

def addBATActionBlockResult (cb : TestLocalChainBuilder) (act : TestAction) :
    Result TestLocalChainBuilder TestAddBlockError :=
  let header := nextBlockHeader cb.lcb_lc creator_addr 0
  add_block AddrSize DepthFirst cb header [act]

def tryAddBATActionBlock (cb : TestLocalChainBuilder) (act : TestAction) :
    Option TestLocalChainBuilder :=
  match addBATActionBlockResult cb act with
  | .Ok cb' => some cb'
  | .Err _ => none

def gBATTrace (cb : TestLocalChainBuilder) : Nat → G TestLocalChainBuilder
  | 0 => return cb
  | n + 1 => do
      match ← gBATAction (lc_to_env AddrSize cb.lcb_lc) with
      | none => return cb
      | some act =>
          match tryAddBATActionBlock cb act with
          | some cb' => gBATTrace cb' n
          | none => gBATTrace cb n

def gBATChainBuilder (length : Nat) : G TestLocalChainBuilder := do
  match bat_chain_result with
  | .Ok cb => gBATTrace cb length
  | .Err _ => genFailure "initial BAT chain deployment failed"

end ConCert.Examples.BAT.Gens
