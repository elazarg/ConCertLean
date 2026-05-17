/- Port of examples/fa2/FA2Interface.v.

This older FA2 interface shape is kept under `FA2.Interface` to avoid name
collisions with the already-ported `FA2LegacyInterface` module used by the
executable token. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Containers
import ConCert.Execution.Serializable
import ConCert.Execution.SerializableDerive
import ConCert.Execution.SerializableInstances

namespace ConCert.Examples.FA2.Interface

open ConCert.Execution.BlockchainBase
open ConCert.Execution.Containers
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

abbrev TokenId : Type := Nat

structure Callback (A : Type) where
  blob : Option A
  return_addr : Base.Address
  deriving Serializable

def callback_addr {A : Type} (c : @Callback Base A) : Base.Address :=
  c.return_addr

structure TransferDestination where
  to_ : Base.Address
  dst_token_id : TokenId
  amount : Nat
  deriving Serializable

structure Transfer where
  from_ : Base.Address
  txs : List (@TransferDestination Base)
  deriving Serializable

structure BalanceOfRequest where
  owner : Base.Address
  bal_req_token_id : TokenId
  deriving Serializable

structure BalanceOfResponse where
  request : @BalanceOfRequest Base
  balance : Nat
  deriving Serializable

structure BalanceOfParam where
  bal_requests : List (@BalanceOfRequest Base)
  bal_callback : @Callback Base (List (@BalanceOfResponse Base))
  deriving Serializable

structure TokenMetadata where
  metadata_token_id : TokenId
  metadata_token_info : FMap String Nat
  deriving Serializable

structure OperatorParam where
  op_param_owner : Base.Address
  op_param_operator : Base.Address
  op_param_token_id : TokenId
  deriving Serializable

inductive UpdateOperator where
  | add_operator (param : @OperatorParam Base)
  | remove_operator (param : @OperatorParam Base)
  deriving Serializable

structure TransferDestinationDescriptor where
  transfer_dst_descr_to_ : Option Base.Address
  transfer_dst_descr_token_id : TokenId
  transfer_dst_descr_amount : Nat
  deriving Serializable

structure TransferDescriptor where
  transfer_descr_from_ : Option Base.Address
  transfer_descr_txs : List (@TransferDestinationDescriptor Base)
  deriving Serializable

structure TransferDescriptorParam where
  transfer_descr_fa2 : Base.Address
  transfer_descr_batch : List (@TransferDescriptor Base)
  transfer_descr_operator : Base.Address
  deriving Serializable

inductive FA2TokenReceiver where
  | tokens_received (param : @TransferDescriptorParam Base)
  deriving Serializable

inductive FA2TokenSender where
  | tokens_sent (param : @TransferDescriptorParam Base)
  deriving Serializable

end ConCert.Examples.FA2.Interface
