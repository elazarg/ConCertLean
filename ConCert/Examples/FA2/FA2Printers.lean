/- Port of examples/fa2/FA2Printers.v as string renderers. -/

import ConCert.Execution.Test.ChainPrinters
import ConCert.Examples.FA2.FA2Token
import ConCert.Examples.FA2.TestContracts

namespace ConCert.Examples.FA2.Printers

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.Test.ChainPrinters
open ConCert.Execution.Test.TestUtils
open ConCert.Examples.FA2

variable [Base : ChainBase]

def string_of_callback {A : Type} (showAddr : Base.Address → String)
    (cb : @Callback Base A) : String :=
  "return_addr=" ++ showAddr cb.return_addr

def string_of_operator_tokens : OperatorTokens → String
  | .all_tokens => "all_tokens"
  | .some_tokens token_ids => "some_tokens " ++ toString token_ids

def string_of_operator_param (showAddr : Base.Address → String)
    (p : @OperatorParam Base) : String :=
  "operator_param{owner=" ++ showAddr p.op_param_owner ++ sep ++
    "operator=" ++ showAddr p.op_param_operator ++ sep ++
    "tokens=" ++ string_of_operator_tokens p.op_param_tokens ++ "}"

def string_of_update_operator (showAddr : Base.Address → String) :
    @UpdateOperator Base → String
  | .add_operator param => "add_operator " ++ string_of_operator_param showAddr param
  | .remove_operator param => "remove_operator " ++ string_of_operator_param showAddr param

def string_of_transfer_destination (showAddr : Base.Address → String)
    (dst : @TransferDestination Base) : String :=
  "transfer_destination{to=" ++ showAddr dst.to_ ++ sep ++
    "token_id=" ++ toString dst.dst_token_id ++ sep ++
    "amount=" ++ toString dst.amount ++ "}"

def string_of_transfer (showAddr : Base.Address → String)
    (tr : @Transfer Base) : String :=
  "transfer{from=" ++ showAddr tr.from_ ++ sep ++
    "txs=[" ++ String.intercalate sep
      (tr.txs.map (string_of_transfer_destination showAddr)) ++ "]}"

def string_of_self_policy : SelfTransferPolicy → String
  | .self_transfer_permitted => "self_transfer_permitted"
  | .self_transfer_denied => "self_transfer_denied"

def string_of_operator_policy : OperatorTransferPolicy → String
  | .operator_transfer_permitted => "operator_transfer_permitted"
  | .operator_transfer_denied => "operator_transfer_denied"

def string_of_owner_policy : OwnerTransferPolicy → String
  | .owner_no_op => "owner_no_op"
  | .optional_owner_hook => "optional_owner_hook"
  | .required_owner_hook => "required_owner_hook"

def string_of_permissions_descriptor (p : PermissionsDescriptor) : String :=
  "permissions{self=" ++ string_of_self_policy p.descr_self ++ sep ++
    "operator=" ++ string_of_operator_policy p.descr_operator ++ sep ++
    "sender=" ++ string_of_owner_policy p.descr_sender ++ sep ++
    "receiver=" ++ string_of_owner_policy p.descr_receiver ++ "}"

def string_of_msg (showAddr : Base.Address → String) : @Msg Base → String
  | .msg_transfer transfers =>
      "transfer [" ++ String.intercalate sep
        (transfers.map (string_of_transfer showAddr)) ++ "]"
  | .msg_set_transfer_hook param =>
      "set_transfer_hook " ++ showAddr param.hook_addr
  | .msg_receive_hook_transfer _ => "receive_hook_transfer"
  | .msg_balance_of param =>
      "balance_of(" ++ toString param.bal_requests.length ++ " requests)"
  | .msg_total_supply param =>
      "total_supply(" ++ toString param.supply_param_token_ids.length ++ " ids)"
  | .msg_token_metadata param =>
      "token_metadata(" ++ toString param.metadata_token_ids.length ++ " ids)"
  | .msg_permissions_descriptor _ => "permissions_descriptor"
  | .msg_update_operators updates =>
      "update_operators [" ++ String.intercalate sep
        (updates.map (string_of_update_operator showAddr)) ++ "]"
  | .msg_is_operator _ => "is_operator"
  | .msg_create_tokens tokenid => "create_tokens " ++ toString tokenid

def string_of_ledger (showAddr : Base.Address → String) (ledger : @TokenLedger Base) :
    String :=
  "TokenLedger{fungible=" ++ toString ledger.fungible ++ sep ++
    "balances=" ++ string_of_FMap showAddr toString ledger.balances ++ "}"

def string_of_state (showAddr : Base.Address → String) (s : @State Base) :
    String :=
  "FA2State{owner=" ++ showAddr s.fa2_owner ++ sep ++
    "assets=" ++ string_of_FMap toString (string_of_ledger showAddr) s.assets ++
    sep ++ "operators=" ++ toString (FMap.elements s.operators).length ++ sep ++
    "policy=" ++ string_of_permissions_descriptor s.permission_policy ++ "}"

def string_of_serialized_msg
    (v : ConCert.Execution.SerializableBase.SerializedValue) : String :=
  string_of_serialized_value v

end ConCert.Examples.FA2.Printers
