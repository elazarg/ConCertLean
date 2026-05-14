/- Port of examples/counter/Counter.v. -/

import ConCert.Utils.Automation
import ConCert.Utils.Extras
import ConCert.Execution.Serializable
import ConCert.Execution.Blockchain
import ConCert.Execution.ResultMonad

namespace ConCert.Examples.Counter

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.SerializableBase
open ConCert.Execution.SerializableInstances
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

/-- Encode/decode using Rocq `Derive Ser`'s constructor-tag wire shape. -/
private def state_serialize (s : @State BaseTypes) : SerializedValue :=
  serialize_constructor2 0 s.count s.owner

private def state_deserialize (v : SerializedValue) : Option (@State BaseTypes) :=
  (deserialize_constructor2 0 v : Option (Int × BaseTypes.Address)).map
    (fun p => { count := p.1, owner := p.2 })

theorem state_deserialize_serialize :
  ∀ (s : @State BaseTypes), state_deserialize (state_serialize s) = some s := by
  intro s
  cases s
  simp [state_deserialize, state_serialize, deserialize_serialize_constructor2]

instance State_serializable : Serializable (@State BaseTypes) where
  serialize  := state_serialize
  deserialize := state_deserialize
  deserialize_serialize := state_deserialize_serialize

/-- Encode `Msg` using Rocq `Derive Ser`'s constructor-tag wire shape. -/
private def msg_serialize (m : Msg) : SerializedValue :=
  match m with
  | .Inc i => serialize_constructor1 0 i
  | .Dec i => serialize_constructor1 1 i

private def msg_deserialize (v : SerializedValue) : Option Msg :=
  match (deserialize_constructor1 0 v : Option Int) with
  | some i => some (.Inc i)
  | none =>
    match (deserialize_constructor1 1 v : Option Int) with
    | some i => some (.Dec i)
    | none => none

omit BaseTypes in
theorem msg_deserialize_serialize :
  ∀ (m : Msg), msg_deserialize (msg_serialize m) = some m := by
  intro m
  cases m <;> simp [msg_deserialize, msg_serialize,
    deserialize_constructor1_serialize_constructor1]

instance Msg_serializable : Serializable Msg where
  serialize  := msg_serialize
  deserialize := msg_deserialize
  deserialize_serialize := msg_deserialize_serialize

def counter_contract : @Contract BaseTypes Int Msg (@State BaseTypes) Error _ _ _ _ :=
  { init := counter_init, receive := counter_receive }

theorem counter_correct
    {prev_state next_state : @State BaseTypes} {msg : Msg} :
    counter prev_state msg = .Ok next_state →
    (match msg with
    | .Inc n => prev_state.count < next_state.count ∧
                next_state.count = prev_state.count + n
    | .Dec n => prev_state.count > next_state.count ∧
                next_state.count = prev_state.count - n) := by
  intro h
  cases msg with
  | Inc i =>
      unfold counter at h
      by_cases hi : 0 < i
      · simp [hi] at h
        cases h
        simp [increment]
        omega
      · simp [hi] at h
  | Dec i =>
      unfold counter at h
      by_cases hi : 0 < i
      · simp [hi] at h
        cases h
        simp [decrement]
        omega
      · simp [hi] at h

def opt_msg_to_number : Option Msg → Int
  | some (.Inc i) => i
  | some (.Dec i) => -i
  | _ => 0

theorem receive_produces_no_calls
    {chain : Chain} {ctx : @ContractCallContext BaseTypes} {cstate : @State BaseTypes}
    {msg : Option Msg} {new_cstate : @State BaseTypes} {acts : List (@ActionBody BaseTypes)} :
    counter_receive chain ctx cstate msg = .Ok (new_cstate, acts) →
    acts = [] := by
  intro h
  cases msg with
  | none =>
      simp [counter_receive] at h
  | some m =>
      simp [counter_receive] at h
      cases hc : counter cstate m with
      | Ok res =>
          simp [hc] at h
          cases h
          assumption
      | Err e =>
          simp [hc] at h

def sum_inc_dec (l : List (@ContractCallInfo BaseTypes Msg)) : Int :=
  ConCert.Utils.Extras.sumZ (fun c => opt_msg_to_number c.call_msg) l

theorem counter_safe
    (block_state : @ChainState BaseTypes) (counter_addr : BaseTypes.Address)
    (trace : ChainTrace empty_state block_state) :
    block_state.env_contracts counter_addr = some (contract_to_weak_contract counter_contract) →
    ∃ (cstate : @State BaseTypes) (call_info : List (@ContractCallInfo BaseTypes Msg))
      (deploy_info : @DeploymentInfo BaseTypes Int),
      incoming_calls Msg trace counter_addr = some call_info ∧
      contract_state block_state.toEnvironment counter_addr = some cstate ∧
      deployment_info Int trace counter_addr = some deploy_info ∧
      deploy_info.deployment_setup + sum_inc_dec call_info = cstate.count := by
  intro hdeployed
  let P : Nat → Nat → Nat → BaseTypes.Address → @DeploymentInfo BaseTypes Int →
          @State BaseTypes → Amount → List (@ActionBody BaseTypes) →
          List (@ContractCallInfo BaseTypes Msg) → List (@Tx BaseTypes) → Prop :=
    fun _ _ _ _ dep cstate _ _ inc_calls _ =>
      dep.deployment_setup + sum_inc_dec inc_calls = cstate.count
  have hcases : ContractInductionCases counter_contract
      (fun _ _ _ _ _ _ => True) (fun _ _ => True) (fun _ _ _ _ _ => True) P := by
    refine
      { establish_facts := ?_, add_block_case := ?_, init_case := ?_,
        outgoing_act_case := ?_, nonrecursive_call_case := ?_,
        recursive_call_case := ?_, permute_case := ?_ }
    · intro _ _ step _ _
      cases step with
      | step_block => trivial
      | step_action _ _ _ _ eval _ =>
          cases eval <;> try trivial
          intro _ _ _; trivial
      | step_action_invalid => trivial
      | step_permute => trivial
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ ih _
      exact ih
    · intro chain ctx setup result _ hinit _
      simp [P, counter_contract, counter_init, sum_inc_dec] at hinit ⊢
      cases hinit
      simp [ConCert.Utils.Extras.sumZ]
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _
      exact ih
    · intro chain ctx dep_info prev_state msg _ prev_inc_calls _ new_state new_acts
        _ _ ih hreceive _
      simp [P] at ih ⊢
      cases msg with
      | none =>
          simp [counter_contract, counter_receive] at hreceive
      | some m =>
          simp [counter_contract, counter_receive] at hreceive
          cases hcounter : counter prev_state m with
          | Err e =>
              simp [hcounter] at hreceive
          | Ok state' =>
              simp [hcounter] at hreceive
              rcases hreceive with ⟨hstate, hacts⟩
              subst new_state
              subst new_acts
              have hspec := counter_correct (prev_state := prev_state)
                (next_state := state') (msg := m) hcounter
              cases m with
              | Inc i =>
                  obtain ⟨_, hcount⟩ := hspec
                  simp [sum_inc_dec, opt_msg_to_number, ConCert.Utils.Extras.sumZ] at ih ⊢
                  omega
              | Dec i =>
                  obtain ⟨_, hcount⟩ := hspec
                  simp [sum_inc_dec, opt_msg_to_number, ConCert.Utils.Extras.sumZ] at ih ⊢
                  omega
    · intro chain ctx dep_info prev_state msg _ prev_out_queue prev_inc_calls _
        new_state new_acts _ _ ih _ hreceive _
      simp [P] at ih ⊢
      cases msg with
      | none =>
          simp [counter_contract, counter_receive] at hreceive
      | some m =>
          simp [counter_contract, counter_receive] at hreceive
          cases hcounter : counter prev_state m with
          | Err e =>
              simp [hcounter] at hreceive
          | Ok state' =>
              simp [hcounter] at hreceive
              rcases hreceive with ⟨hstate, hacts⟩
              subst new_state
              subst new_acts
              have hspec := counter_correct (prev_state := prev_state)
                (next_state := state') (msg := m) hcounter
              cases m with
              | Inc i =>
                  obtain ⟨_, hcount⟩ := hspec
                  simp [sum_inc_dec, opt_msg_to_number, ConCert.Utils.Extras.sumZ] at ih ⊢
                  omega
              | Dec i =>
                  obtain ⟨_, hcount⟩ := hspec
                  simp [sum_inc_dec, opt_msg_to_number, ConCert.Utils.Extras.sumZ] at ih ⊢
                  omega
    · intro _ _ _ _ _ _ _ _ _ _ _ ih _ _
      exact ih
  obtain ⟨dep, cstate, inc_calls, hdep, hstate, hcalls, hP⟩ :=
    contract_induction counter_contract _ _ _ P hcases block_state counter_addr trace hdeployed
  exact ⟨cstate, inc_calls, dep, hcalls, hstate, hdep, hP⟩

end ConCert.Examples.Counter
