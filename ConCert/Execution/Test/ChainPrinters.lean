/- Port of execution/test/ChainPrinters.v.

   The original derives `Show` instances for chain types via QuickChick's
   `Derive Show` Ltac; this port provides simple stringification shells. -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Serializable
import ConCert.Execution.ChainedList
import ConCert.Execution.Test.TestUtils

namespace ConCert.Execution.Test.ChainPrinters

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.Test.TestUtils

def sep : String := ", "

variable [Base : ChainBase]

def string_of_serialized_type : SerializedType → String
  | .ser_unit         => "unit"
  | .ser_int          => "int"
  | .ser_bool         => "bool"
  | .ser_pair a b     => "(" ++ string_of_serialized_type a ++ " * " ++ string_of_serialized_type b ++ ")"
  | .ser_list a       => "list " ++ string_of_serialized_type a

def ex_serialized_type : SerializedType :=
  .ser_pair (.ser_list (.ser_list .ser_bool)) .ser_int

def string_of_interp_type : (st : SerializedType) → interp_type st → String
  | .ser_unit => fun _ => "()"
  | .ser_int => fun i => toString (show Int from i)
  | .ser_bool => fun b => toString (show Bool from b)
  | .ser_pair a b => fun p =>
      "(" ++ string_of_interp_type a p.1 ++ sep ++ string_of_interp_type b p.2 ++ ")"
  | .ser_list a => fun xs =>
      "[" ++ String.intercalate sep (xs.map (string_of_interp_type a)) ++ "]"

def string_of_serialized_value (v : SerializedValue) : String :=
  string_of_interp_type v.ser_value_type v.ser_value

def string_of_result {A E : Type} (showA : A → String) (showE : E → String) :
    ConCert.Execution.ResultMonad.Result A E → String
  | .Ok a => "Ok(" ++ showA a ++ ")"
  | .Err e => "Err(" ++ showE e ++ ")"

def string_of_address {Base : ChainBase} (showAddr : Base.Address → String)
    (addr : Base.Address) : String :=
  showAddr addr

def string_of_local_address {bound : Nat}
    (addr : ConCert.Execution.BoundedN bound) : String :=
  toString addr.val ++ "%" ++ toString bound

def string_of_chain (chain : Chain) : String :=
  "Chain{height=" ++ toString chain.chain_height ++ sep
    ++ "slot=" ++ toString chain.current_slot ++ sep
    ++ "finalized=" ++ toString chain.finalized_height ++ "}"

def string_of_block_header (showAddr : Base.Address → String)
    (header : @BlockHeader Base) : String :=
  "BlockHeader{height=" ++ toString header.block_height ++ sep
    ++ "slot=" ++ toString header.block_slot ++ sep
    ++ "finalized=" ++ toString header.block_finalized_height ++ sep
    ++ "reward=" ++ toString header.block_reward ++ sep
    ++ "creator=" ++ showAddr header.block_creator ++ "}"

def string_of_action_body (showAddr : Base.Address → String) :
    @ActionBody Base → String
  | .act_transfer to_ amount =>
      "transfer(to=" ++ showAddr to_ ++ sep ++ "amount=" ++ toString amount ++ ")"
  | .act_call to_ amount msg =>
      "call(to=" ++ showAddr to_ ++ sep ++ "amount=" ++ toString amount
        ++ sep ++ "msg=" ++ string_of_serialized_value msg ++ ")"
  | .act_deploy amount _ setup =>
      "deploy(amount=" ++ toString amount
        ++ sep ++ "setup=" ++ string_of_serialized_value setup ++ ")"

def string_of_action (showAddr : Base.Address → String) (act : @Action Base) : String :=
  "Action{origin=" ++ showAddr act.act_origin ++ sep
    ++ "from=" ++ showAddr act.act_from ++ sep
    ++ "body=" ++ string_of_action_body (Base := Base) showAddr act.act_body ++ "}"

def string_of_action_evaluation_error (showAddr : Base.Address → String) :
    @ConCert.Execution.BlockchainBuilder.ActionEvaluationError Base → String
  | .amount_negative amount => "amount_negative(" ++ toString amount ++ ")"
  | .amount_too_high amount => "amount_too_high(" ++ toString amount ++ ")"
  | .no_such_contract addr => "no_such_contract(" ++ showAddr addr ++ ")"
  | .too_many_contracts => "too_many_contracts"
  | .init_failed err => "init_failed(" ++ string_of_serialized_value err ++ ")"
  | .receive_failed err => "receive_failed(" ++ string_of_serialized_value err ++ ")"
  | .deserialization_failed val =>
      "deserialization_failed(" ++ string_of_serialized_value val ++ ")"
  | .internal_error => "internal_error"

def string_of_add_block_error (showAddr : Base.Address → String) :
    @ConCert.Execution.BlockchainBuilder.AddBlockError Base → String
  | .invalid_header header =>
      "invalid_header(" ++ string_of_block_header (Base := Base) showAddr header ++ ")"
  | .invalid_root_action act =>
      "invalid_root_action(" ++ string_of_action (Base := Base) showAddr act ++ ")"
  | .origin_from_mismatch act =>
      "origin_from_mismatch(" ++ string_of_action (Base := Base) showAddr act ++ ")"
  | .action_evaluation_depth_exceeded => "action_evaluation_depth_exceeded"
  | .action_evaluation_error act err =>
      "action_evaluation_error("
        ++ string_of_action (Base := Base) showAddr act ++ sep
        ++ string_of_action_evaluation_error (Base := Base) showAddr err ++ ")"

end ConCert.Execution.Test.ChainPrinters
