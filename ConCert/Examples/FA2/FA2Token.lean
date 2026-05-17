/- Port of examples/fa2/FA2Token.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Examples.FA2.FA2LegacyInterface
import ConCert.Utils.Extras

namespace ConCert.Examples.FA2

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.Containers
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Utils.Extras

variable [Base : ChainBase]

inductive FA2ReceiverMsg (Msg' : Type) where
  | receive_balance_of_param (responses : List BalanceOfResponse)
  | receive_total_supply_param (responses : List TotalSupplyResponse)
  | receive_metadata_callback (metadata : List TokenMetadata)
  | receive_is_operator (response : IsOperatorResponse)
  | receive_permissions_descriptor (permissions : PermissionsDescriptor)
  | other_msg (msg : Msg')
  deriving Serializable

inductive FA2TransferHook (Msg' : Type) where
  | transfer_hook (param : TransferDescriptorParam)
  | hook_other_msg (msg : Msg')
  deriving Serializable

inductive Msg where
  | msg_transfer (transfers : List Transfer)
  | msg_set_transfer_hook (param : SetHookParam)
  | msg_receive_hook_transfer (param : TransferDescriptorParam)
  | msg_balance_of (param : BalanceOfParam)
  | msg_total_supply (param : TotalSupplyParam)
  | msg_token_metadata (param : TokenMetadataParam)
  | msg_permissions_descriptor (callback : Callback PermissionsDescriptor)
  | msg_update_operators (updates : List UpdateOperator)
  | msg_is_operator (param : IsOperatorParam)
  | msg_create_tokens (token_id : TokenId)
  deriving Serializable

structure TokenLedger where
  fungible : Bool
  balances : AddressMap.AddrMap (Base := Base) Nat
  deriving Serializable

structure State where
  fa2_owner : Base.Address
  assets : FMap TokenId TokenLedger
  operators : FMap Base.Address (FMap Base.Address OperatorTokens)
  permission_policy : PermissionsDescriptor
  tokens : FMap TokenId TokenMetadata
  transfer_hook_addr : Option Base.Address
  deriving Serializable

structure Setup where
  setup_total_supply : List (TokenId × Nat)
  setup_tokens : FMap TokenId TokenMetadata
  initial_permission_policy : PermissionsDescriptor
  transfer_hook_addr_ : Option Base.Address
  deriving Serializable

abbrev Error : Type := Nat
def default_error : Error := 1

def address_balance
    (token_id : TokenId) (addr : Base.Address) (state : @State Base) : Nat :=
  match FMap.find token_id state.assets with
  | some ledger => with_default 0 (FMap.find addr ledger.balances)
  | none => 0

def address_has_sufficient_asset_balance
    (token_id : TokenId) (owner : Base.Address) (transaction_amount : Nat)
    (state : @State Base) : Result Unit Error :=
  if transaction_amount ≤ address_balance token_id owner state then
    .Ok ()
  else
    .Err default_error

def policy_disallows_operator_transfer (policy : PermissionsDescriptor) : Bool :=
  match policy.descr_operator with
  | .operator_transfer_permitted => false
  | .operator_transfer_denied => true

def policy_disallows_self_transfer (policy : PermissionsDescriptor) : Bool :=
  match policy.descr_self with
  | .self_transfer_permitted => false
  | .self_transfer_denied => true

def get_owner_operator_tokens
    (owner operator : Base.Address) (state : @State Base) : Option OperatorTokens :=
  match FMap.find owner state.operators with
  | none => none
  | some operator_tokens => FMap.find operator operator_tokens

def try_single_transfer
    (_caller : Base.Address) (params : Transfer) (state : @State Base) :
    Result (@State Base) Error :=
  if !(params.txs.length == 1) then
    .Err default_error
  else
    match params.txs.head? with
    | none => .Err default_error
    | some transfer_dst =>
        match FMap.find transfer_dst.dst_token_id state.assets with
        | none => .Err default_error
        | some ledger =>
            let current_owner_balance :=
              address_balance transfer_dst.dst_token_id params.from_ state
            let new_balances :=
              FMap.add params.from_ (current_owner_balance - transfer_dst.amount)
                ledger.balances
            let new_balances :=
              FMap.partial_alter
                (fun balance => some (with_default 0 balance + transfer_dst.amount))
                transfer_dst.to_ new_balances
            let new_ledger := { ledger with balances := new_balances }
            .Ok
              { state with
                assets := FMap.add transfer_dst.dst_token_id new_ledger state.assets }

def transfer_check_permissions
    (caller : Base.Address) (params : Transfer)
    (policy : PermissionsDescriptor) (state : @State Base) :
    Result Unit Error :=
  if !(params.txs.length == 1) then
    .Err default_error
  else
    match params.txs.head? with
    | none => .Err default_error
    | some transfer_dst =>
        match address_has_sufficient_asset_balance transfer_dst.dst_token_id
            params.from_ transfer_dst.amount state with
        | .Err e => .Err e
        | .Ok _ =>
            match FMap.find transfer_dst.dst_token_id state.tokens with
            | none => .Err default_error
            | some _ =>
                if Base.address_eqb caller params.from_ then
                  throwIf (policy_disallows_self_transfer policy) default_error
                else
                  match throwIf (policy_disallows_operator_transfer policy)
                      default_error with
                  | .Err e => .Err e
                  | .Ok _ =>
                      match FMap.find params.from_ state.operators with
                      | none => .Err default_error
                      | some operators_map =>
                          match FMap.find caller operators_map with
                          | none => .Err default_error
                          | some .all_tokens => .Ok ()
                          | some (.some_tokens token_ids) =>
                              if token_ids.any (fun id => id == transfer_dst.dst_token_id) then
                                .Ok ()
                              else
                                .Err default_error

def try_transfer
    (caller : Base.Address) (transfers : List Transfer) (state : @State Base) :
    Result (@State Base) Error :=
  transfers.foldl
    (fun stateResult params =>
      match stateResult with
      | .Err e => .Err e
      | .Ok state =>
          match transfer_check_permissions caller params state.permission_policy state with
          | .Err e => .Err e
          | .Ok _ => try_single_transfer caller params state)
    (.Ok state)

def mk_transfer_dst_descr (tr_dst : TransferDestination) :
    TransferDestinationDescriptor :=
  { transfer_dst_descr_to_ := some tr_dst.to_,
    transfer_dst_descr_token_id := tr_dst.dst_token_id,
    transfer_dst_descr_amount := tr_dst.amount }

def mk_transfer_descr (tr : Transfer) : TransferDescriptor :=
  { transfer_descr_from_ := some tr.from_,
    transfer_descr_txs := tr.txs.map mk_transfer_dst_descr }

def mk_transfer_descr_param
    (caller caddr : Base.Address) (batch : List TransferDescriptor) :
    TransferDescriptorParam :=
  { transfer_descr_fa2 := caddr,
    transfer_descr_batch := batch,
    transfer_descr_operator := caller }

def call_transfer_hook
    (caller : Base.Address) (caddr : Base.Address)
    (transfer_hook_addr : Base.Address) (transfers : List Transfer)
    (_state : @State Base) : @ActionBody Base :=
  let transfer_descr_param :=
    mk_transfer_descr_param caller caddr (transfers.map mk_transfer_descr)
  let hook_msg : FA2TransferHook Unit := .transfer_hook transfer_descr_param
  .act_call transfer_hook_addr 0 (serialize hook_msg)

private def optionAddressEq (a b : Option Base.Address) : Bool :=
  match a, b with
  | none, none => true
  | some a, some b => Base.address_eqb a b
  | _, _ => false

private def insertTransferDescriptorGroup
    (descr : TransferDescriptor)
    (groups : List (Option Base.Address × List TransferDescriptor)) :
    List (Option Base.Address × List TransferDescriptor) :=
  match groups with
  | [] => [(descr.transfer_descr_from_, [descr])]
  | (from_, descrs) :: rest =>
      if optionAddressEq descr.transfer_descr_from_ from_ then
        (from_, descr :: descrs) :: rest
      else
        (from_, descrs) :: insertTransferDescriptorGroup descr rest

def group_transfer_descriptors
    (params : List TransferDescriptor) : List (List TransferDescriptor) :=
  (params.foldr insertTransferDescriptorGroup []).map Prod.snd

def collectSomeActions
    (acts : List (Option (@ActionBody Base))) : List (@ActionBody Base) :=
  acts.foldr
    (fun actOpt acc =>
      match actOpt with
      | some act => act :: acc
      | none => acc)
    []

def handle_transfer
    (caller : Base.Address) (caddr : Base.Address)
    (transfers : List Transfer) (state : @State Base) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match state.transfer_hook_addr with
  | some transfer_hook_addr =>
      .Ok (state, [call_transfer_hook caller caddr transfer_hook_addr transfers state])
  | none =>
      let transfer_descr_param :=
        mk_transfer_descr_param caller caddr (transfers.map mk_transfer_descr)
      let self_transfer_act :=
        .act_call caddr 0 (serialize (Msg.msg_receive_hook_transfer transfer_descr_param))
      let mk_sender_hook_act (trx : Transfer) : Option (@ActionBody Base) :=
        match trx.sender_callback_addr with
        | none => none
        | some callback_addr =>
            let descr :=
              mk_transfer_descr_param caller caddr [mk_transfer_descr trx]
            some (.act_call callback_addr 0
              (serialize (FA2TokenSender.tokens_sent descr)))
      let sender_hook_acts := collectSomeActions (transfers.map mk_sender_hook_act)
      if sender_hook_acts.length == 0 then
        match try_transfer caller transfers state with
        | .Ok new_state => .Ok (new_state, [])
        | .Err e => .Err e
      else
        .Ok (state, sender_hook_acts ++ [self_transfer_act])

def mk_transfer_destination_from_descr
    (dst_descr : TransferDestinationDescriptor) : Option TransferDestination := do
  let to_ ← dst_descr.transfer_dst_descr_to_
  some
    { to_ := to_,
      dst_token_id := dst_descr.transfer_dst_descr_token_id,
      amount := dst_descr.transfer_dst_descr_amount }

def mk_transfer_from_descr (descr : TransferDescriptor) : Option Transfer := do
  let from_ ← descr.transfer_descr_from_
  let txs_list ←
    descr.transfer_descr_txs.foldr
      (fun dst_descr acc_opt => do
        let acc ← acc_opt
        let tx_dst ← mk_transfer_destination_from_descr dst_descr
        some (tx_dst :: acc))
      (some [])
  some { from_ := from_, txs := txs_list, sender_callback_addr := none }

def handle_transfer_hook_receive
    (caller : Base.Address) (param : TransferDescriptorParam)
    (self_addr : Base.Address) (state : @State Base) :
    Result (@State Base) Error :=
  let callerAllowed :=
    match state.transfer_hook_addr with
    | some hook_addr => Base.address_eqb caller hook_addr || Base.address_eqb caller self_addr
    | none => Base.address_eqb caller self_addr
  if !callerAllowed then
    .Err default_error
  else
    let transferResult : Result (List Transfer) Error :=
      param.transfer_descr_batch.foldr
        (fun descr accResult =>
          match accResult with
          | .Err e => .Err e
          | .Ok acc =>
              match mk_transfer_from_descr descr with
              | none => .Err default_error
              | some transfer => .Ok (transfer :: acc))
        (.Ok [])
    match transferResult with
    | .Err e => .Err e
    | .Ok transfers => try_transfer param.transfer_descr_operator transfers state

def get_balance_of_callback
    (param : BalanceOfParam) (state : @State Base) : @ActionBody Base :=
  let responses :=
    param.bal_requests.map (fun bal_req =>
      { request := bal_req,
        balance := address_balance bal_req.bal_req_token_id bal_req.owner state })
  let responseMsg : FA2ReceiverMsg Unit := .receive_balance_of_param responses
  .act_call param.bal_callback.return_addr 0 (serialize responseMsg)

def token_id_balance (token_id : TokenId) (state : @State Base) : Nat :=
  match FMap.find token_id state.assets with
  | some ledger => ((FMap.elements ledger.balances).map (fun p : Base.Address × Nat => p.2)).sum
  | none => 0

def get_total_supply_callback
    (param : TotalSupplyParam) (state : @State Base) : @ActionBody Base :=
  let responses :=
    param.supply_param_token_ids.map (fun token_id =>
      { supply_resp_token_id := token_id,
        total_supply := token_id_balance token_id state })
  let responseMsg : FA2ReceiverMsg Unit := .receive_total_supply_param responses
  .act_call param.supply_param_callback.return_addr 0 (serialize responseMsg)

def update_operators
    (caller : Base.Address) (updates : List UpdateOperator) (state : @State Base) :
    Result (@State Base) Error :=
  match throwIf (policy_disallows_operator_transfer state.permission_policy) default_error with
  | .Err e => .Err e
  | .Ok _ =>
      let execAdd (params : OperatorParam)
          (stateResult : Result (@State Base) Error) : Result (@State Base) Error :=
        match stateResult with
        | .Err e => .Err e
        | .Ok state_ =>
            if !(Base.address_eqb caller params.op_param_owner) then
              .Err default_error
            else
              let operator_tokens : FMap Base.Address OperatorTokens :=
                with_default FMap.empty (FMap.find caller state_.operators)
              let operator_tokens :=
                FMap.add params.op_param_operator params.op_param_tokens operator_tokens
              .Ok
                { state_ with
                  operators := FMap.add caller operator_tokens state_.operators }
      let execUpdate
          (stateResult : Result (@State Base) Error) (op : UpdateOperator) :
          Result (@State Base) Error :=
        match op with
        | .add_operator params => execAdd params stateResult
        | .remove_operator params => execAdd params stateResult
      updates.foldl execUpdate (.Ok state)

def natListEq : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => x == y && natListEq xs ys
  | _, _ => false

def operator_tokens_eqb (a b : OperatorTokens) : Bool :=
  match a, b with
  | .all_tokens, .all_tokens => true
  | .some_tokens a', .some_tokens b' => natListEq a' b'
  | _, _ => false

def get_is_operator_response_callback
    (params : IsOperatorParam) (state : @State Base) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  match throwIf (policy_disallows_operator_transfer state.permission_policy) default_error with
  | .Err e => .Err e
  | .Ok _ =>
      let operator_params := params.is_operator_operator
      let operator_tokens_opt :=
        get_owner_operator_tokens operator_params.op_param_owner
          operator_params.op_param_operator state
      let is_operator_result :=
        match operator_tokens_opt with
        | some op_tokens => operator_tokens_eqb op_tokens operator_params.op_param_tokens
        | none => false
      let response : IsOperatorResponse :=
        { operator := operator_params, is_operator := is_operator_result }
      let responseMsg : FA2ReceiverMsg Unit := .receive_is_operator response
      .Ok (state, [.act_call params.is_operator_callback.return_addr 0
        (serialize responseMsg)])

def get_permissions_descriptor_callback
    (caller : Base.Address) (state : @State Base) : @ActionBody Base :=
  let responseMsg : FA2ReceiverMsg Unit :=
    .receive_permissions_descriptor state.permission_policy
  .act_call caller 0 (serialize responseMsg)

def try_set_transfer_hook
    (caller : Base.Address) (params : SetHookParam) (state : @State Base) :
    Result (@State Base) Error :=
  match throwIf (!(Base.address_eqb caller state.fa2_owner)) default_error with
  | .Err e => .Err e
  | .Ok _ =>
      .Ok
        { state with
          transfer_hook_addr := some params.hook_addr,
          permission_policy := params.hook_permissions_descriptor }

def get_token_metadata_callback
    (param : TokenMetadataParam) (state : @State Base) : @ActionBody Base :=
  let metadata_list :=
    param.metadata_token_ids.foldr
      (fun id acc =>
        match FMap.find id state.tokens with
        | some metadata => metadata :: acc
        | none => acc)
      []
  let responseMsg : FA2ReceiverMsg Unit := .receive_metadata_callback metadata_list
  .act_call param.metadata_callback.return_addr 0 (serialize responseMsg)

def try_create_tokens
    (caller : Base.Address) (amount : Amount) (tokenid : TokenId)
    (state : @State Base) : Result (@State Base) Error :=
  match FMap.find tokenid state.assets with
  | none => .Err default_error
  | some ledger =>
      if amount ≤ 0 then
        .Err default_error
      else
        let minted := (amount * 100).toNat
        let caller_bal := with_default 0 (FMap.find caller ledger.balances)
        let new_balances := FMap.add caller (caller_bal + minted) ledger.balances
        let new_ledger := { ledger with balances := new_balances }
        .Ok { state with assets := FMap.add tokenid new_ledger state.assets }

def receive
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @State Base) (maybe_msg : Option Msg) :
    Result (@State Base × List (@ActionBody Base)) Error :=
  let sender := ctx.ctx_from
  let caddr := ctx.ctx_contract_address
  if 0 < ctx.ctx_amount then
    match maybe_msg with
    | some (.msg_create_tokens tokenid) =>
        without_actions (Base := Base)
          (try_create_tokens sender ctx.ctx_amount tokenid state)
    | _ => .Err default_error
  else
    match maybe_msg with
    | some (.msg_transfer transfers) =>
        handle_transfer sender caddr transfers state
    | some (.msg_receive_hook_transfer param) =>
        without_actions (Base := Base)
          (handle_transfer_hook_receive sender param caddr state)
    | some (.msg_is_operator params) =>
        get_is_operator_response_callback params state
    | some (.msg_balance_of params) =>
        .Ok (state, [get_balance_of_callback params state])
    | some (.msg_total_supply params) =>
        .Ok (state, [get_total_supply_callback params state])
    | some (.msg_permissions_descriptor _) =>
        .Ok (state, [get_permissions_descriptor_callback sender state])
    | some (.msg_token_metadata param) =>
        .Ok (state, [get_token_metadata_callback param state])
    | some (.msg_update_operators updates) =>
        without_actions (Base := Base) (update_operators sender updates state)
    | some (.msg_set_transfer_hook params) =>
        without_actions (Base := Base) (try_set_transfer_hook sender params state)
    | _ =>
        .Err default_error

def map_values_FMap {A B C : Type} [Ord A] [LawfulOrd A]
    (f : B → C) (m : FMap A B) : FMap A C :=
  FMap.of_list ((FMap.elements m).map (fun p => (p.1, f p.2)))

def init (_chain : Chain) (ctx : @ContractCallContext Base) (setup : @Setup Base) :
    Result (@State Base) Error :=
  let assets' :=
    map_values_FMap (fun _ => ({ fungible := false, balances := FMap.empty } : TokenLedger))
      setup.setup_tokens
  .Ok
    { permission_policy := setup.initial_permission_policy,
      fa2_owner := ctx.ctx_from,
      transfer_hook_addr := setup.transfer_hook_addr_,
      assets := assets',
      operators := FMap.empty,
      tokens := setup.setup_tokens }

def contract : @Contract Base (@Setup Base) Msg (@State Base) Error _ _ _ _ :=
  { init := init, receive := receive }

end ConCert.Examples.FA2
