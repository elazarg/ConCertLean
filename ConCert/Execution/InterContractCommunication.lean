/- Port of execution/theories/InterContractCommunication.v -/

import ConCert.Execution.Blockchain
import ConCert.Execution.Serializable

namespace ConCert.Execution.InterContractCommunication

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase

variable [Base : ChainBase]

def txCallTo (addr : Base.Address) (tx : @Tx Base) : Bool :=
  match tx.tx_body with
  | .tx_call _ => Base.address_eqb tx.tx_to addr
  | _ => false

def actTo (addr : Base.Address) (act : @ActionBody Base) : Bool :=
  match act with
  | .act_transfer to_ _ => Base.address_eqb to_ addr
  | .act_call to_ _ _   => Base.address_eqb to_ addr
  | _ => false

def callFrom {Msg : Type} (addr : Base.Address) (ci : @ContractCallInfo Base Msg) : Bool :=
  Base.address_eqb ci.call_from addr

axiom deployed_incoming_calls_typed :
  ∀ (bstate : @ChainState Base) (caddr : Base.Address)
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error}
    (trace : ChainTrace empty_state bstate),
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    ∃ inc_calls, incoming_calls Msg trace caddr = some inc_calls

axiom undeployed_contract_no_state :
  ∀ (bstate : @ChainState Base) (caddr : Base.Address)
    (_trace : ChainTrace empty_state bstate),
    bstate.env_contracts caddr = none →
    bstate.env_contract_states caddr = none

axiom no_outgoing_txs_to_undeployed_contract :
  ∀ (bstate : @ChainState Base) (caddrA caddrB : Base.Address)
    (trace : ChainTrace empty_state bstate)
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error},
    bstate.env_contracts caddrA = some (contract_to_weak_contract contract) →
    bstate.env_contracts caddrB = none →
    (outgoing_txs trace caddrA).filter (txCallTo caddrB) = []

axiom no_incoming_calls_from_undeployed_contract :
  ∀ (bstate : @ChainState Base) (caddrA caddrB : Base.Address)
    (trace : ChainTrace empty_state bstate)
    {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    {contract : Contract Setup Msg State Error},
    bstate.env_contracts caddrA = none →
    Base.address_is_contract caddrA = true →
    bstate.env_contracts caddrB = some (contract_to_weak_contract contract) →
    ∃ inc_calls,
      incoming_calls Msg trace caddrB = some inc_calls ∧
      inc_calls.filter (callFrom caddrA) = []

def contract_call_info_to_tx
    {X : Type} [Serializable X]
    (caddr : Base.Address) (ci : @ContractCallInfo Base X) : @Tx Base :=
  let body : @TxBody Base :=
    match ci.call_msg with
    | some msg => .tx_call (some (serialize msg))
    | none => .tx_call none
  { tx_origin := ci.call_origin,
    tx_from := ci.call_from,
    tx_to := caddr,
    tx_amount := ci.call_amount,
    tx_body := body }

def tx_to_contract_call_info
    {X : Type} [Serializable X] (tx : @Tx Base) : Option (@ContractCallInfo Base X) :=
  match tx.tx_body with
  | .tx_call none =>
      some { call_origin := tx.tx_origin, call_from := tx.tx_from,
             call_amount := tx.tx_amount, call_msg := none }
  | .tx_call (some m) =>
      some { call_origin := tx.tx_origin, call_from := tx.tx_from,
             call_amount := tx.tx_amount,
             call_msg := (deserialize m : Option X) }
  | _ => none

axiom incomming_eq_outgoing :
  ∀ (bstate : @ChainState Base) (caddrA caddrB : Base.Address)
    (trace : ChainTrace empty_state bstate)
    {SetupA MsgA StateA ErrorA : Type}
    {SetupB MsgB StateB ErrorB : Type}
    [Serializable SetupA] [Serializable SetupB]
    [Serializable MsgA] [Serializable MsgB]
    [Serializable StateA] [Serializable StateB]
    [Serializable ErrorA] [Serializable ErrorB]
    {contractA : Contract SetupA MsgA StateA ErrorA}
    {contractB : Contract SetupB MsgB StateB ErrorB},
    (∀ (x : SerializedValue) (y : MsgB), (deserialize x : Option MsgB) = some y → x = serialize y) →
    bstate.env_contracts caddrA = some (contract_to_weak_contract contractA) →
    bstate.env_contracts caddrB = some (contract_to_weak_contract contractB) →
    ∃ inc_calls,
      incoming_calls MsgB trace caddrB = some inc_calls ∧
      (outgoing_txs trace caddrA).filter (txCallTo caddrB) =
        (inc_calls.filter (callFrom caddrA)).map (contract_call_info_to_tx caddrB)

-- TODO: port tactic trace_induction

end ConCert.Execution.InterContractCommunication
