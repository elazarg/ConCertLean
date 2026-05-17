/- Port of examples/fa2/FA2LegacyInterface.v. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive

namespace ConCert.Examples.FA2

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

abbrev TokenId : Type := Nat

structure Callback (A : Type) where
  blob : Option A
  return_addr : Base.Address
  deriving Serializable

structure TransferDestination where
  to_ : Base.Address
  dst_token_id : TokenId
  amount : Nat
  deriving Serializable

structure Transfer where
  from_ : Base.Address
  txs : List TransferDestination
  sender_callback_addr : Option Base.Address
  deriving Serializable

structure BalanceOfRequest where
  owner : Base.Address
  bal_req_token_id : TokenId
  deriving Serializable

structure BalanceOfResponse where
  request : BalanceOfRequest
  balance : Nat
  deriving Serializable

structure BalanceOfParam where
  bal_requests : List BalanceOfRequest
  bal_callback : Callback (List BalanceOfResponse)
  deriving Serializable

structure TotalSupplyResponse where
  supply_resp_token_id : TokenId
  total_supply : Nat
  deriving Serializable

structure TotalSupplyParam where
  supply_param_token_ids : List TokenId
  supply_param_callback : Callback (List TotalSupplyResponse)
  deriving Serializable

structure TokenMetadata where
  metadata_token_id : TokenId
  metadata_decimals : Nat
  deriving Serializable

structure TokenMetadataParam where
  metadata_token_ids : List TokenId
  metadata_callback : Callback (List TokenMetadata)
  deriving Serializable

inductive OperatorTokens where
  | all_tokens
  | some_tokens (token_ids : List TokenId)
  deriving Serializable

structure OperatorParam where
  op_param_owner : Base.Address
  op_param_operator : Base.Address
  op_param_tokens : OperatorTokens
  deriving Serializable

inductive UpdateOperator where
  | add_operator (param : OperatorParam)
  | remove_operator (param : OperatorParam)
  deriving Serializable

structure IsOperatorResponse where
  operator : OperatorParam
  is_operator : Bool
  deriving Serializable

structure IsOperatorParam where
  is_operator_operator : OperatorParam
  is_operator_callback : Callback IsOperatorResponse
  deriving Serializable

inductive SelfTransferPolicy where
  | self_transfer_permitted
  | self_transfer_denied
  deriving Serializable

inductive OperatorTransferPolicy where
  | operator_transfer_permitted
  | operator_transfer_denied
  deriving Serializable

inductive OwnerTransferPolicy where
  | owner_no_op
  | optional_owner_hook
  | required_owner_hook
  deriving Serializable

structure PermissionsDescriptor where
  descr_self : SelfTransferPolicy
  descr_operator : OperatorTransferPolicy
  descr_receiver : OwnerTransferPolicy
  descr_sender : OwnerTransferPolicy
  descr_custom : Option Base.Address
  deriving Serializable

structure TransferDestinationDescriptor where
  transfer_dst_descr_to_ : Option Base.Address
  transfer_dst_descr_token_id : TokenId
  transfer_dst_descr_amount : Nat
  deriving Serializable

structure TransferDescriptor where
  transfer_descr_from_ : Option Base.Address
  transfer_descr_txs : List TransferDestinationDescriptor
  deriving Serializable

structure TransferDescriptorParam where
  transfer_descr_fa2 : Base.Address
  transfer_descr_batch : List TransferDescriptor
  transfer_descr_operator : Base.Address
  deriving Serializable

inductive FA2TokenReceiver where
  | tokens_received (param : TransferDescriptorParam)
  deriving Serializable

inductive FA2TokenSender where
  | tokens_sent (param : TransferDescriptorParam)
  deriving Serializable

structure SetHookParam where
  hook_addr : Base.Address
  hook_permissions_descriptor : PermissionsDescriptor
  deriving Serializable

end ConCert.Examples.FA2
