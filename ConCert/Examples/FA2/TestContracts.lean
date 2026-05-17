/- Port of examples/fa2/TestContracts.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.ContractCommon
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Examples.FA2.FA2LegacyInterface
import ConCert.Examples.FA2.FA2Token

namespace ConCert.Examples.FA2.TestContracts

open ConCert.Execution.BlockchainBase
open ConCert.Execution.ContractCommon
open ConCert.Execution.ResultMonad
open ConCert.Execution.SerializableBase
open ConCert.Examples.FA2

variable [Base : ChainBase]

inductive FA2ClientMsg where
  | Call_fa2_is_operator (param : IsOperatorParam)
  | Call_fa2_balance_of_param (responses : List BalanceOfResponse)
  | Call_fa2_total_supply_param (responses : List TotalSupplyResponse)
  | Call_fa2_metadata_callback (metadata : List TokenMetadata)
  | Call_fa2_permissions_descriptor (permissions : PermissionsDescriptor)
  deriving Serializable

abbrev ClientMsg : Type := FA2ReceiverMsg FA2ClientMsg

structure ClientState where
  fa2_caddr : Base.Address
  bit : Nat
  deriving Serializable

structure ClientSetup where
  fa2_caddr_ : Base.Address
  deriving Serializable

abbrev ClientError : Type := Nat
def default_client_error : ClientError := 0

def client_init
    (_chain : Chain) (_ctx : @ContractCallContext Base) (setup : @ClientSetup Base) :
    Result (@ClientState Base) ClientError :=
  .Ok { fa2_caddr := setup.fa2_caddr_, bit := 0 }

def client_receive
    (_chain : Chain) (_ctx : @ContractCallContext Base)
    (state : @ClientState Base) (maybe_msg : Option ClientMsg) :
    Result (@ClientState Base × List (@ActionBody Base)) ClientError :=
  match maybe_msg with
  | some (.receive_is_operator _) =>
      .Ok ({ state with bit := 42 }, [])
  | some (.other_msg (.Call_fa2_is_operator is_op_param)) =>
      .Ok
        ({ state with bit := 2 },
          [ActionBody.act_call state.fa2_caddr 0
            (serialize (Msg.msg_is_operator is_op_param))])
  | _ =>
      .Err default_client_error

def client_contract :
    @Contract Base (@ClientSetup Base) ClientMsg (@ClientState Base) ClientError _ _ _ _ :=
  { init := client_init, receive := client_receive }

inductive FA2TransferHookMsg where
  | set_permission_policy (permissions : PermissionsDescriptor)
  deriving Serializable

abbrev TransferHookMsg : Type := FA2TransferHook FA2TransferHookMsg

structure HookState where
  hook_owner : Base.Address
  hook_fa2_caddr : Base.Address
  hook_policy : PermissionsDescriptor
  deriving Serializable

structure HookSetup where
  hook_fa2_caddr_ : Base.Address
  hook_policy_ : PermissionsDescriptor
  deriving Serializable

abbrev HookError : Type := Nat
def default_hook_error : HookError := 0

def hook_init
    (_chain : Chain) (ctx : @ContractCallContext Base) (setup : @HookSetup Base) :
    Result (@HookState Base) HookError :=
  .Ok
    { hook_owner := ctx.ctx_from,
      hook_fa2_caddr := setup.hook_fa2_caddr_,
      hook_policy := setup.hook_policy_ }

def check_transfer_permissions
    (tr : TransferDescriptor) (operator : Base.Address) (state : @HookState Base) :
    Result Unit HookError :=
  match tr.transfer_descr_from_ with
  | none => .Err default_hook_error
  | some from_ =>
      if Base.address_eqb from_ operator then
        if policy_disallows_self_transfer state.hook_policy then
          .Err default_hook_error
        else
          .Ok ()
      else if policy_disallows_operator_transfer state.hook_policy then
        .Err default_hook_error
      else
        .Ok ()

def on_hook_receive_transfer
    (caller : Base.Address) (param : TransferDescriptorParam)
    (state : @HookState Base) :
    Result (List (@ActionBody Base)) HookError :=
  if !(Base.address_eqb caller state.hook_fa2_caddr) then
    .Err default_hook_error
  else if !(Base.address_eqb param.transfer_descr_fa2 state.hook_fa2_caddr) then
    .Err default_hook_error
  else
    let checked : Result Unit HookError :=
      param.transfer_descr_batch.foldr
        (fun tr acc =>
          match acc with
          | .Err e => .Err e
          | .Ok _ => check_transfer_permissions tr param.transfer_descr_operator state)
        (.Ok ())
    match checked with
    | .Err e => .Err e
    | .Ok _ =>
        .Ok
          [ActionBody.act_call caller 0
            (serialize (Msg.msg_receive_hook_transfer param))]

def try_update_permission_policy
    (caller : Base.Address) (new_policy : PermissionsDescriptor)
    (state : @HookState Base) :
    Result (@HookState Base) HookError :=
  match throwIf (!(Base.address_eqb caller state.hook_owner)) default_hook_error with
  | .Err e => .Err e
  | .Ok _ => .Ok { state with hook_policy := new_policy }

def hook_receive
    (_chain : Chain) (ctx : @ContractCallContext Base)
    (state : @HookState Base) (maybe_msg : Option TransferHookMsg) :
    Result (@HookState Base × List (@ActionBody Base)) HookError :=
  let sender := ctx.ctx_from
  match maybe_msg with
  | some (.transfer_hook param) =>
      match on_hook_receive_transfer sender param state with
      | .Ok acts => .Ok (state, acts)
      | .Err e => .Err e
  | some (.hook_other_msg (.set_permission_policy policy)) =>
      without_actions (Base := Base) (try_update_permission_policy sender policy state)
  | _ =>
      .Err default_hook_error

def hook_contract :
    @Contract Base (@HookSetup Base) TransferHookMsg (@HookState Base) HookError _ _ _ _ :=
  { init := hook_init, receive := hook_receive }

end ConCert.Examples.FA2.TestContracts
