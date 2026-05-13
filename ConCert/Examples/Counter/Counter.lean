/- Port of examples/counter/Counter.v. -/

import ConCert.Utils.Automation
import ConCert.Utils.Extras
import ConCert.Execution.Serializable
import ConCert.Execution.Blockchain
import ConCert.Execution.ResultMonad

namespace ConCert.Examples.Counter

open ConCert.Execution.BlockchainBase
open ConCert.Execution.SerializableBase
open ConCert.Execution.ResultMonad

variable [BaseTypes : ChainBase]

structure State where
  count : Int
  owner : BaseTypes.Address

inductive Msg where
  | Inc (i : Int)
  | Dec (i : Int)

abbrev Error : Type := Nat
def default_error : Error := 1

def increment (n : Int) (st : @State BaseTypes) : @State BaseTypes :=
  { st with count := st.count + n }

def decrement (n : Int) (st : @State BaseTypes) : @State BaseTypes :=
  { st with count := st.count - n }

def counter (st : @State BaseTypes) (msg : Msg) : Result (@State BaseTypes) Error :=
  match msg with
  | .Inc i =>
    if 0 < i then .Ok (increment i st) else .Err default_error
  | .Dec i =>
    if 0 < i then .Ok (decrement i st) else .Err default_error

def counter_receive
    (_chain : Chain) (_ctx : @ContractCallContext BaseTypes)
    (state : @State BaseTypes) (msg : Option Msg)
    : Result (@State BaseTypes × List (@ActionBody BaseTypes)) Error :=
  match msg with
  | some m =>
    match counter state m with
    | .Ok res => .Ok (res, [])
    | .Err e  => .Err e
  | none => .Err default_error

def counter_init
    (_chain : Chain) (ctx : @ContractCallContext BaseTypes)
    (init_value : Int)
    : Result (@State BaseTypes) Error :=
  .Ok { count := init_value, owner := ctx.ctx_from }

/-- Encode/decode via product `(Int × Address)`. -/
private def state_serialize (s : @State BaseTypes) : SerializedValue :=
  serialize ((s.count, s.owner))

private def state_deserialize (v : SerializedValue) : Option (@State BaseTypes) :=
  (deserialize v : Option (Int × BaseTypes.Address)).map
    (fun p => { count := p.1, owner := p.2 })

axiom state_deserialize_serialize :
  ∀ (s : @State BaseTypes), state_deserialize (state_serialize s) = some s

instance State_serializable : Serializable (@State BaseTypes) where
  serialize  := state_serialize
  deserialize := state_deserialize
  deserialize_serialize := state_deserialize_serialize

/-- Encode `Msg` via a tagged Int (positive tag for Inc, zero/negative for Dec
    distinguished by sign on a Sum). -/
private def msg_serialize (m : Msg) : SerializedValue :=
  match m with
  | .Inc i => serialize (Sum.inl i : Sum Int Int)
  | .Dec i => serialize (Sum.inr i : Sum Int Int)

private def msg_deserialize (v : SerializedValue) : Option Msg :=
  (deserialize v : Option (Sum Int Int)).map (fun s =>
    match s with | .inl i => .Inc i | .inr i => .Dec i)

axiom msg_deserialize_serialize :
  ∀ (m : Msg), msg_deserialize (msg_serialize m) = some m

instance Msg_serializable : Serializable Msg where
  serialize  := msg_serialize
  deserialize := msg_deserialize
  deserialize_serialize := msg_deserialize_serialize

def counter_contract : @Contract BaseTypes Int Msg (@State BaseTypes) Error _ _ _ _ :=
  { init := counter_init, receive := counter_receive }

axiom counter_correct
    {prev_state next_state : @State BaseTypes} {msg : Msg} :
    counter prev_state msg = .Ok next_state →
    match msg with
    | .Inc n => prev_state.count < next_state.count ∧
                next_state.count = prev_state.count + n
    | .Dec n => prev_state.count > next_state.count ∧
                next_state.count = prev_state.count - n

def opt_msg_to_number : Option Msg → Int
  | some (.Inc i) => i
  | some (.Dec i) => -i
  | _ => 0

axiom receive_produces_no_calls
    {chain : Chain} {ctx : @ContractCallContext BaseTypes} {cstate : @State BaseTypes}
    {msg : Option Msg} {new_cstate : @State BaseTypes} {acts : List (@ActionBody BaseTypes)} :
    counter_receive chain ctx cstate msg = .Ok (new_cstate, acts) →
    acts = []

def sum_inc_dec (l : List (@ContractCallInfo BaseTypes Msg)) : Int :=
  ConCert.Utils.Extras.sumZ (fun c => opt_msg_to_number c.call_msg) l

axiom counter_safe
    (block_state : @ChainState BaseTypes) (counter_addr : BaseTypes.Address)
    (trace : ChainTrace empty_state block_state) :
    block_state.env_contracts counter_addr = some (contract_to_weak_contract counter_contract) →
    ∃ (cstate : @State BaseTypes) (call_info : List (@ContractCallInfo BaseTypes Msg))
      (deploy_info : @DeploymentInfo BaseTypes Int),
      incoming_calls Msg trace counter_addr = some call_info ∧
      contract_state block_state.toEnvironment counter_addr = some cstate ∧
      deployment_info Int trace counter_addr = some deploy_info ∧
      deploy_info.deployment_setup + sum_inc_dec call_info = cstate.count

end ConCert.Examples.Counter
