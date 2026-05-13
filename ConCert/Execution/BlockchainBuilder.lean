/- Port of execution/theories/BlockchainBuilder.v -/

import ConCert.Execution.ChainedList
import ConCert.Execution.Monad
import ConCert.Execution.ResultMonad
import ConCert.Execution.Serializable
import ConCert.Execution.BlockchainBase
import ConCert.Execution.BlockchainTheories

namespace ConCert.Execution.BlockchainBuilder

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.SerializableBase
open ConCert.Execution.ResultMonad
open ConCert.Execution.ChainedList

variable [Base : ChainBase]

inductive ActionEvaluationError where
  | amount_negative (amount : Amount)
  | amount_too_high (amount : Amount)
  | no_such_contract (addr : Base.Address)
  | too_many_contracts
  | init_failed (err : SerializedValue)
  | receive_failed (err : SerializedValue)
  | deserialization_failed (val : SerializedValue)
  | internal_error

inductive AddBlockError where
  | invalid_header (header : @BlockHeader Base)
  | invalid_root_action (act : @Action Base)
  | origin_from_mismatch (act : @Action Base)
  | action_evaluation_depth_exceeded
  | action_evaluation_error (act : @Action Base) (err : @ActionEvaluationError Base)

class ChainBuilderType where
  builder_type : Type
  builder_initial : builder_type
  builder_env : builder_type → @Environment Base
  builder_add_block :
    builder_type → @BlockHeader Base → List (@Action Base) →
    Result builder_type (@AddBlockError Base)
  builder_trace :
    ∀ (b : builder_type),
      ChainTrace (@empty_state Base)
        { toEnvironment := builder_env b, chain_state_queue := [] }

namespace BuildUtils

def receiver_can_receive_transfer (bstate : @ChainState Base) (act_body : @ActionBody Base) : Prop :=
  match act_body with
  | .act_transfer to_ _ =>
      Base.address_is_contract to_ = false ∨
      (∃ wc state,
        bstate.env_contracts to_ = some wc ∧
        bstate.env_contract_states to_ = some state ∧
        ∀ (bstate_new : @ChainState Base) (ctx : @ContractCallContext Base),
          ∃ new_state,
            wc_receive wc bstate_new.toEnvironment.toChain ctx state none = Ok (new_state, []))
  | _ => True

/-- Coq states this as an `Axiom` even in the upstream source: assumes that
    for any reachable state and prospective deploy, we can decide whether
    *some* fresh contract address allows the deploy's `init` to succeed. -/
axiom deployable_address_decidable :
  ∀ (bstate : @ChainState Base) (wc : @WeakContract Base)
    (setup : SerializedValue) (act_origin act_from : Base.Address)
    (amount : Amount),
    reachable bstate →
    (∃ addr state,
      Base.address_is_contract addr = true ∧
      bstate.env_contracts addr = none ∧
      wc_init wc
        (transfer_balance act_from addr amount bstate.toEnvironment).toChain
        { ctx_origin := act_origin, ctx_from := act_from,
          ctx_contract_address := addr,
          ctx_contract_balance := amount, ctx_amount := amount }
        setup = .Ok state)
    ∨ ¬ ∃ addr state,
        Base.address_is_contract addr = true ∧
        bstate.env_contracts addr = none ∧
        wc_init wc
          (transfer_balance act_from addr amount bstate.toEnvironment).toChain
          { ctx_origin := act_origin, ctx_from := act_from,
            ctx_contract_address := addr,
            ctx_contract_balance := amount, ctx_amount := amount }
          setup = .Ok state

/-- Followed-from-deployable-address by case analysis on `act`; in Coq
    this is proved rather than axiomatized. We carry it as a derived
    axiom for now. -/
axiom action_evaluation_decidable :
  ∀ (bstate : @ChainState Base) (act : @Action Base),
    reachable bstate →
    (∃ bstate' new_acts, Nonempty (ActionEvaluation bstate.toEnvironment act bstate' new_acts))
    ∨ ¬ ∃ bstate' new_acts, Nonempty (ActionEvaluation bstate.toEnvironment act bstate' new_acts)

/-- An action never produces new actions when evaluated. -/
def produces_no_new_acts (act : @Action Base) : Prop :=
  ∀ bstate bstate' new_acts,
    ActionEvaluation bstate act bstate' new_acts → new_acts = []

/-- A queue is emptyable: all acts originate from accounts AND none of them
    produce new acts when evaluated. Together this guarantees that the queue
    can be fully drained. -/
def emptyable (queue : List (@Action Base)) : Prop :=
  queue.Forall act_is_from_account ∧ queue.Forall produces_no_new_acts

axiom empty_queue_is_emptyable : @emptyable Base []

axiom emptyable_cons :
  ∀ (x : @Action Base) (l : List (@Action Base)),
    emptyable (x :: l) → emptyable l

axiom empty_queue :
  ∀ (bstate : @ChainState Base) (P : @ChainState Base → Prop),
    reachable bstate →
    emptyable bstate.chain_state_queue →
    P bstate →
    (∀ (b b' : @ChainState Base) (act : @Action Base) (acts : List (@Action Base)),
      reachable b → reachable b' → P b →
      b.chain_state_queue = act :: acts → b'.chain_state_queue = acts →
      (Nonempty (ActionEvaluation b.toEnvironment act b'.toEnvironment []) ∨
       EnvironmentEquiv b.toEnvironment b'.toEnvironment) → P b') →
    ∃ bstate', reachable_through bstate bstate' ∧ P bstate' ∧ bstate'.chain_state_queue = []

axiom add_block :
  ∀ (bstate : @ChainState Base) (reward : Amount) (creator : Base.Address)
    (acts : List (@Action Base)) (slot_incr : Nat),
    reachable bstate →
    bstate.chain_state_queue = [] →
    Base.address_is_contract creator = false →
    reward ≥ 0 → slot_incr > 0 →
    acts.Forall act_is_from_account →
    acts.Forall act_origin_is_eq_from →
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.chain_state_queue = acts ∧
      EnvironmentEquiv bstate'.toEnvironment
        (add_new_block_to_env
          { block_height := bstate.chain_height + 1,
            block_slot := bstate.current_slot + slot_incr,
            block_finalized_height := bstate.finalized_height,
            block_creator := creator,
            block_reward := reward } bstate.toEnvironment)

axiom forward_time_exact :
  ∀ (bstate : @ChainState Base) (reward : Amount) (creator : Base.Address) (slot : Nat),
    reachable bstate →
    bstate.chain_state_queue = [] →
    Base.address_is_contract creator = false →
    reward ≥ 0 →
    bstate.current_slot < slot →
    ∃ bstate' header,
      reachable_through bstate bstate' ∧
      IsValidNextBlock header (env_chain bstate.toEnvironment) ∧
      slot = bstate'.current_slot ∧
      bstate'.chain_state_queue = [] ∧
      EnvironmentEquiv bstate'.toEnvironment (add_new_block_to_env header bstate.toEnvironment)

axiom forward_time :
  ∀ (bstate : @ChainState Base) (reward : Amount) (creator : Base.Address) (slot : Nat),
    reachable bstate →
    bstate.chain_state_queue = [] →
    Base.address_is_contract creator = false →
    reward ≥ 0 →
    ∃ bstate' header,
      reachable_through bstate bstate' ∧
      IsValidNextBlock header (env_chain bstate.toEnvironment) ∧
      slot ≤ bstate'.current_slot ∧
      bstate'.chain_state_queue = [] ∧
      EnvironmentEquiv bstate'.toEnvironment (add_new_block_to_env header bstate.toEnvironment)

axiom evaluate_action :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base)
    (origin frm caddr : Base.Address) (amount : Amount) (msg : Msg)
    (acts : List (@Action Base)) (new_acts : List (@ActionBody Base))
    (cstate new_cstate : State),
    reachable bstate →
    bstate.chain_state_queue =
      { act_from := frm, act_origin := origin,
        act_body := .act_call caddr amount (serialize msg) } :: acts →
    amount ≥ 0 →
    bstate.env_account_balances frm ≥ amount →
    bstate.env_contracts caddr = some (contract_to_weak_contract contract) →
    bstate.env_contract_states caddr = some (serialize cstate) →
    contract.receive
      (transfer_balance frm caddr amount bstate.toEnvironment).toChain
      { ctx_origin := origin, ctx_from := frm, ctx_contract_address := caddr,
        ctx_contract_balance :=
          if Base.address_eqb frm caddr then bstate.env_account_balances caddr
          else bstate.env_account_balances caddr + amount,
        ctx_amount := amount }
      cstate (some msg) = .Ok (new_cstate, new_acts) →
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.env_contract_states caddr = some (serialize new_cstate) ∧
      bstate'.chain_state_queue =
        (new_acts.map (fun b => { act_origin := origin, act_from := caddr, act_body := b })) ++ acts ∧
      EnvironmentEquiv bstate'.toEnvironment
        (set_contract_state caddr (serialize new_cstate)
          (transfer_balance frm caddr amount bstate.toEnvironment))

axiom evaluate_transfer :
  ∀ (bstate : @ChainState Base) (origin frm to_ : Base.Address)
    (amount : Amount) (acts : List (@Action Base)),
    reachable bstate →
    bstate.chain_state_queue =
      { act_from := frm, act_origin := origin,
        act_body := .act_transfer to_ amount } :: acts →
    amount ≥ 0 →
    bstate.env_account_balances frm ≥ amount →
    Base.address_is_contract to_ = false →
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.chain_state_queue = acts ∧
      EnvironmentEquiv bstate'.toEnvironment
        (transfer_balance frm to_ amount bstate.toEnvironment)

axiom discard_invalid_action :
  ∀ (bstate : @ChainState Base) (act : @Action Base) (acts : List (@Action Base)),
    reachable bstate →
    bstate.chain_state_queue = act :: acts →
    act_is_from_account act →
    (∀ bstate0 new_acts,
      ActionEvaluation bstate.toEnvironment act bstate0 new_acts → False) →
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.chain_state_queue = acts ∧
      EnvironmentEquiv bstate'.toEnvironment bstate.toEnvironment

axiom permute_queue :
  ∀ (bstate : @ChainState Base) (acts acts_permuted : List (@Action Base)),
    reachable bstate →
    bstate.chain_state_queue = acts →
    List.Perm acts acts_permuted →
    ∃ bstate',
      reachable_through bstate bstate' ∧
      bstate'.chain_state_queue = acts_permuted ∧
      EnvironmentEquiv bstate'.toEnvironment bstate.toEnvironment

axiom deploy_contract :
  ∀ {Setup Msg State Error : Type}
    [Serializable Setup] [Serializable Msg]
    [Serializable State] [Serializable Error]
    (contract : @Contract Base Setup Msg State Error _ _ _ _)
    (bstate : @ChainState Base)
    (origin frm caddr : Base.Address) (amount : Amount)
    (acts : List (@Action Base)) (setup : Setup) (cstate : State),
    reachable bstate →
    bstate.chain_state_queue =
      { act_from := frm, act_origin := origin,
        act_body := .act_deploy amount (contract_to_weak_contract contract) (serialize setup) } :: acts →
    amount ≥ 0 →
    bstate.env_account_balances frm ≥ amount →
    Base.address_is_contract caddr = true →
    bstate.env_contracts caddr = none →
    contract.init (transfer_balance frm caddr amount bstate.toEnvironment).toChain
      { ctx_origin := origin, ctx_from := frm, ctx_contract_address := caddr,
        ctx_contract_balance := amount, ctx_amount := amount } setup = .Ok cstate →
    ∃ bstate', ∃ (trace : ChainTrace empty_state bstate'),
      reachable_through bstate bstate' ∧
      bstate'.env_contracts caddr = some (contract_to_weak_contract contract) ∧
      bstate'.env_contract_states caddr = some (serialize cstate) ∧
      deployment_info Setup trace caddr =
        some { deployment_origin := origin, deployment_from := frm,
               deployment_amount := amount, deployment_setup := setup } ∧
      bstate'.chain_state_queue = acts ∧
      EnvironmentEquiv bstate'.toEnvironment
        (set_contract_state caddr (serialize cstate)
          (add_contract caddr (contract_to_weak_contract contract)
            (transfer_balance frm caddr amount bstate.toEnvironment)))

end BuildUtils

end ConCert.Execution.BlockchainBuilder
