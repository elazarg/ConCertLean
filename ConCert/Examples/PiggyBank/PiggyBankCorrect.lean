/- Partial port of examples/piggybank/PiggyBankCorrect.v.

   This file ports the local functional properties that do not rely on the
   larger upstream reachability development. -/

import ConCert.Examples.PiggyBank.PiggyBank
import ConCert.Execution.BlockchainInduction
import Mathlib.Tactic.Linarith

namespace ConCert.Examples.PiggyBank.Correctness

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainInduction
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.ResultMonad
open ConCert.Examples.PiggyBank
open ConCert.Utils.Extras

variable [Base : ChainBase]

theorem insert_inserts_correct
    (prev_state next_state : @State Base)
    (ctx : @ContractCallContext Base)
    (acts : List (@ActionBody Base)) :
    insert prev_state ctx = .Ok (next_state, acts) →
    acts = [] ∧ ctx.ctx_amount + prev_state.balance = next_state.balance := by
  intro h
  unfold insert at h
  by_cases hneg : ctx.ctx_amount < 0
  · simp [ConCert.Execution.ContractCommon.throwIf, hneg] at h
  · simp [ConCert.Execution.ContractCommon.throwIf, hneg] at h
    cases hsmashed : is_smashed prev_state <;> simp [hsmashed] at h
    rcases h with ⟨hstate, hacts⟩
    cases hstate
    cases hacts
    constructor
    · rfl
    · rw [Int.add_comm]

theorem smash_transfers_correctly
    (prev_state next_state : @State Base)
    (ctx : @ContractCallContext Base)
    (acts : List (@ActionBody Base)) :
    smash prev_state ctx = .Ok (next_state, acts) →
    next_state.piggyState = .Smashed ∧
    next_state.balance = 0 ∧
    acts = [.act_transfer prev_state.owner (prev_state.balance + ctx.ctx_amount)] := by
  intro h
  unfold smash at h
  simp [ConCert.Execution.ContractCommon.throwIf] at h
  split at h <;> simp_all
  split at h <;> simp_all
  rcases h with ⟨hstate, hacts⟩
  subst next_state
  subst acts
  simp

theorem receive_is_correct
    (chain : Chain)
    (ctx : @ContractCallContext Base)
    (prev_state next_state : @State Base)
    (msg : Option Msg)
    (acts : List (@ActionBody Base)) :
    receive chain ctx prev_state msg = .Ok (next_state, acts) →
    match msg with
    | some .Insert =>
        acts = [] ∧ ctx.ctx_amount + prev_state.balance = next_state.balance
    | some .Smash =>
        next_state.piggyState = .Smashed ∧
        next_state.balance = 0 ∧
        acts = [.act_transfer prev_state.owner (prev_state.balance + ctx.ctx_amount)]
    | none => False := by
  intro h
  cases msg with
  | none =>
      simp [receive] at h
  | some m =>
      cases m with
      | Insert =>
          exact insert_inserts_correct prev_state next_state ctx acts h
      | Smash =>
          exact smash_transfers_correctly prev_state next_state ctx acts h

theorem receive_produces_no_calls_when_running_insert
    (chain : Chain)
    (ctx : @ContractCallContext Base)
    (prev_state next_state : @State Base)
    (acts : List (@ActionBody Base)) :
    receive chain ctx prev_state (some .Insert) = .Ok (next_state, acts) →
    acts = [] := by
  intro h
  exact (insert_inserts_correct prev_state next_state ctx acts h).1

theorem owner_remains
    (chain : Chain)
    (ctx : @ContractCallContext Base)
    (prev_state next_state : @State Base)
    (msg : Option Msg)
    (acts : List (@ActionBody Base)) :
    receive chain ctx prev_state msg = .Ok (next_state, acts) →
    prev_state.owner = next_state.owner := by
  intro h
  cases msg with
  | none =>
      simp [receive] at h
  | some m =>
      cases m with
      | Insert =>
          have hcorrect := insert_inserts_correct prev_state next_state ctx acts h
          unfold receive at h
          simp at h
          unfold insert at h
          by_cases hneg : ctx.ctx_amount < 0
          · simp [ConCert.Execution.ContractCommon.throwIf, hneg] at h
          · simp [ConCert.Execution.ContractCommon.throwIf, hneg] at h
            cases hsmashed : is_smashed prev_state <;> simp [hsmashed] at h
            rcases h with ⟨hstate, _hacts⟩
            subst next_state
            rfl
      | Smash =>
          unfold receive at h
          simp at h
          unfold smash at h
          simp [ConCert.Execution.ContractCommon.throwIf] at h
          split at h <;> simp_all
          split at h <;> simp_all
          rcases h with ⟨hstate, _hacts⟩
          subst next_state
          rfl

theorem owner_correct
    (bstate : @ChainState Base) (caddr : Base.Address)
    (trace : ChainTrace empty_state bstate) :
    bstate.env_contracts caddr =
      some (contract_to_weak_contract (contract : @Contract Base _ _ _ _ _ _ _ _)) →
    ∃ (cstate : @State Base) (dep : @DeploymentInfo Base Setup),
      deployment_info Setup trace caddr = some dep ∧
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr = some cstate ∧
      cstate.owner = dep.deployment_from := by
  intro hdeployed
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
          @State Base → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ _ dep cstate _ _ _ _ => cstate.owner = dep.deployment_from
  have hcases : ContractInductionCases contract
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
      simp [P, contract, init] at hinit ⊢
      cases hinit
      rfl
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _
      exact ih
    · intro chain ctx _ prev_state msg _ _ _ new_state new_acts
        _ _ ih hreceive _
      simp [P] at ih ⊢
      have howner := owner_remains chain ctx prev_state new_state msg new_acts hreceive
      rw [← howner]
      exact ih
    · intro chain ctx _ prev_state msg _ _ _ _ new_state new_acts
        _ _ ih _ hreceive _
      simp [P] at ih ⊢
      have howner := owner_remains chain ctx prev_state new_state msg new_acts hreceive
      rw [← howner]
      exact ih
    · intro _ _ _ _ _ _ _ _ _ _ _ ih _ _
      exact ih
  obtain ⟨dep, cstate, _inc_calls, hdep, hstate, _hcalls, hP⟩ :=
    contract_induction contract _ _ _ P hcases bstate caddr trace hdeployed
  exact ⟨cstate, dep, hdep, hstate, hP⟩

private theorem smash_sender_is_owner
    {prev_state next_state : @State Base}
    {ctx : @ContractCallContext Base}
    {acts : List (@ActionBody Base)}
    (h : smash prev_state ctx = .Ok (next_state, acts)) :
    ctx.ctx_from = prev_state.owner := by
  unfold smash at h
  by_cases hnot_owner : !Base.address_eqb ctx.ctx_from prev_state.owner
  · simp [ConCert.Execution.ContractCommon.throwIf, hnot_owner] at h
  · have howner : Base.address_eqb ctx.ctx_from prev_state.owner = true := by
      cases hb : Base.address_eqb ctx.ctx_from prev_state.owner
      · exact False.elim (hnot_owner (by simp [hb]))
      · rfl
    exact (Base.address_eqb_spec _ _).mp howner

private def noSelfAction (caddr : Base.Address) :
    @ActionBody Base → Prop
  | .act_transfer to_ _ => Base.address_eqb to_ caddr = false
  | _ => False

private def sum_acts (acts : List (@ActionBody Base)) : Amount :=
  (acts.map act_body_amount).sum

private theorem sum_acts_append
    (xs ys : List (@ActionBody Base)) :
    sum_acts (xs ++ ys) = sum_acts xs + sum_acts ys := by
  simp [sum_acts, List.map_append, List.sum_append]

private theorem sum_acts_perm
    {xs ys : List (@ActionBody Base)} (hperm : xs.Perm ys) :
    sum_acts xs = sum_acts ys := by
  unfold sum_acts
  simpa [List.sum_eq_foldr] using
    (List.Perm.foldr_op_eq
      (op := fun x y : Int => x + y)
      (a := (0 : Int))
      (hperm.map act_body_amount))

private theorem receive_acts_no_self_of_not_self
    {chain : Chain} {ctx : @ContractCallContext Base}
    {prev_state next_state : @State Base} {msg : Option Msg}
    {acts : List (@ActionBody Base)}
    (hnot_self : ctx.ctx_from ≠ ctx.ctx_contract_address)
    (h : receive chain ctx prev_state msg = .Ok (next_state, acts)) :
    acts.Forall (noSelfAction (Base := Base) ctx.ctx_contract_address) := by
  cases msg with
  | none =>
      simp [receive] at h
  | some msg =>
      cases msg with
      | Insert =>
          have hacts := receive_produces_no_calls_when_running_insert
            chain ctx prev_state next_state acts h
          rw [hacts]
          simp
      | Smash =>
          have hcorrect := smash_transfers_correctly prev_state next_state ctx acts h
          have howner := smash_sender_is_owner
            (Base := Base) (prev_state := prev_state) (next_state := next_state)
            (ctx := ctx) (acts := acts) h
          have howner_ne : prev_state.owner ≠ ctx.ctx_contract_address := by
            intro heq
            exact hnot_self (by rw [howner, heq])
          have hneqb :
              Base.address_eqb prev_state.owner ctx.ctx_contract_address =
                false := by
            cases hb : Base.address_eqb prev_state.owner ctx.ctx_contract_address
            · rfl
            · exact False.elim
                (howner_ne ((Base.address_eqb_spec _ _).mp hb))
          rw [hcorrect.2.2]
          simp [noSelfAction, hneqb]

private theorem receive_balance_correct
    {chain : Chain} {ctx : @ContractCallContext Base}
    {prev_state next_state : @State Base} {msg : Option Msg}
    {acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state msg = .Ok (next_state, acts)) :
    prev_state.balance =
      next_state.balance - ctx.ctx_amount + sum_acts (Base := Base) acts := by
  cases msg with
  | none =>
      simp [receive] at h
  | some msg =>
      cases msg with
      | Insert =>
          have hcorrect := insert_inserts_correct prev_state next_state ctx acts h
          rcases hcorrect with ⟨hacts, hbalance⟩
          rw [hacts]
          simp [sum_acts] at hbalance ⊢
          linarith
      | Smash =>
          have hcorrect := smash_transfers_correctly prev_state next_state ctx acts h
          rcases hcorrect with ⟨_hsmashed, hzero, hacts⟩
          rw [hacts, hzero]
          simp [sum_acts, act_body_amount]

theorem no_self_calls
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _))) :
    (outgoing_acts bstate caddr).Forall
      (noSelfAction (Base := Base) caddr) := by
  obtain ⟨trace⟩ := hr
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
          @State Base → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ caddr _ _ _ out_queue _ _ =>
      out_queue.Forall (noSelfAction (Base := Base) caddr)
  have hcases : ContractInductionCases contract
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
    · intro _ _ _ _ _ _ _
      simp [P]
    · intro _ _ _ _ _ _ _ _ _ _ _ _ ih _ _ _ _
      simp only [P, List.forall_cons] at ih
      exact ih.2
    · intro chain ctx _ prev_state msg prev_out_queue _ _
        new_state new_acts hnot_self _ ih hreceive _
      simp [contract] at hreceive
      simp only [P] at ih ⊢
      exact (ConCert.Utils.Extras.Forall_app _ _ _).mp
        ⟨receive_acts_no_self_of_not_self
          (Base := Base) hnot_self hreceive, ih⟩
    · intro _ ctx _ _ _ head _ _ _ _ _ _ _ ih haction _ _
      simp only [P, List.forall_cons] at ih
      cases head with
      | act_transfer to_ amount =>
          rcases haction with ⟨hto, _hamount, _hmsg⟩
          subst to_
          simp [noSelfAction, Address.address_eq_refl] at ih
      | act_deploy amount wc setup =>
          simp [noSelfAction] at ih
      | act_call to_ amount msg_ser =>
          simp [noSelfAction] at ih
    · intro _ _ _ _ _ _ _ _ _ _ _ ih hperm _
      simp only [P] at ih ⊢
      exact ConCert.Utils.Extras.forall_respects_permutation
        _ _ _ hperm ih
  obtain ⟨_, _, _, _, _, _, hP⟩ :=
    contract_induction contract _ _ _ P hcases bstate caddr trace hdeployed
  simpa [P] using hP

theorem balance_on_chain'
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _))) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      bstate.env_account_balances caddr -
          sum_acts (Base := Base) (outgoing_acts bstate caddr) =
        cstate.balance := by
  obtain ⟨trace⟩ := hr
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
          @State Base → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ caddr _ cstate balance out_queue _ _ =>
      balance - sum_acts (Base := Base) out_queue = cstate.balance ∧
        out_queue.Forall (noSelfAction (Base := Base) caddr)
  have hcases : ContractInductionCases contract
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
      constructor
      · simp [contract, init, sum_acts] at hinit ⊢
        cases hinit
        linarith
      · simp
    · intro _ _ _ _ _ _ _ out_act out_acts _ _ _ ih _ hamount _ _
      rcases ih with ⟨hbal, hno⟩
      constructor
      · simp [sum_acts] at hbal ⊢
        linarith
      · simp only [List.forall_cons] at hno
        exact hno.2
    · intro chain ctx _ prev_state msg prev_out_queue _ _
        new_state new_acts hnot_self _ ih hreceive _
      simp [contract] at hreceive
      rcases ih with ⟨hbal, hno⟩
      constructor
      · have hrecv := receive_balance_correct (Base := Base) hreceive
        rw [sum_acts_append]
        linarith
      · exact (ConCert.Utils.Extras.Forall_app _ _ _).mp
          ⟨receive_acts_no_self_of_not_self
            (Base := Base) hnot_self hreceive, hno⟩
    · intro _ ctx _ _ _ head prev_out_queue _ _ _ _ _ _ ih haction _ _
      rcases ih with ⟨_hbal, hno⟩
      simp only [List.forall_cons] at hno
      cases head with
      | act_transfer to_ amount =>
          rcases haction with ⟨hto, _hamount, _hmsg⟩
          subst to_
          simp [noSelfAction, Address.address_eq_refl] at hno
      | act_deploy amount wc setup =>
          simp [noSelfAction] at hno
      | act_call to_ amount msg_ser =>
          simp [noSelfAction] at hno
    · intro _ _ _ _ _ _ _ out_queue _ _ out_queue' ih hperm _
      rcases ih with ⟨hbal, hno⟩
      constructor
      · rw [← sum_acts_perm (Base := Base) hperm]
        exact hbal
      · exact ConCert.Utils.Extras.forall_respects_permutation
          _ _ _ hperm hno
  obtain ⟨_, cstate, _inc_calls, _hdep, hstate, _hcalls, hP⟩ :=
    contract_induction contract _ _ _ P hcases bstate caddr trace hdeployed
  exact ⟨cstate, hstate, hP.1⟩

theorem balance_on_chain
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _)))
    (hacts : outgoing_acts bstate caddr = []) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      bstate.env_account_balances caddr = cstate.balance := by
  obtain ⟨cstate, hstate, hbalance⟩ :=
    balance_on_chain' bstate caddr hr hdeployed
  rw [hacts] at hbalance
  simp [sum_acts] at hbalance
  exact ⟨cstate, hstate, by simpa using hbalance⟩

theorem balance_on_pos
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _)))
    (hacts : outgoing_acts bstate caddr = []) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      0 ≤ cstate.balance := by
  obtain ⟨cstate, hstate, hbalance⟩ :=
    balance_on_chain bstate caddr hr hdeployed hacts
  refine ⟨cstate, hstate, ?_⟩
  rw [← hbalance]
  exact account_balance_nonnegative bstate caddr hr

private theorem receive_smashed_balance_zero
    {chain : Chain} {ctx : @ContractCallContext Base}
    {prev_state next_state : @State Base} {msg : Option Msg}
    {acts : List (@ActionBody Base)}
    (hprev : prev_state.piggyState = .Smashed → prev_state.balance = 0)
    (h : receive chain ctx prev_state msg = .Ok (next_state, acts))
    (hnew : next_state.piggyState = .Smashed) :
    next_state.balance = 0 := by
  cases msg with
  | none =>
      simp [receive] at h
  | some msg =>
      cases msg with
      | Insert =>
          unfold receive insert at h
          by_cases hneg : ctx.ctx_amount < 0
          · simp [ConCert.Execution.ContractCommon.throwIf, hneg] at h
          · simp [ConCert.Execution.ContractCommon.throwIf, hneg] at h
            cases hsmashed : is_smashed prev_state <;> simp [hsmashed] at h
            rcases h with ⟨hstate, _hacts⟩
            subst next_state
            cases prev_state with
            | mk balance owner piggyState =>
                cases piggyState <;> simp [is_smashed] at hsmashed hnew
      | Smash =>
          exact (smash_transfers_correctly prev_state next_state ctx acts h).2.1

theorem state_balance_zero_when_smashed
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _))) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      (cstate.piggyState = .Smashed → cstate.balance = 0) := by
  let Q : @State Base → Prop :=
    fun cstate => cstate.piggyState = .Smashed → cstate.balance = 0
  obtain ⟨cstate, hstate, hQ⟩ :=
    lift_contract_state_prop
      (contract :=
        (contract :
          @Contract Base Setup Msg (@State Base) Error _ _ _ _))
      (Q := Q)
      bstate caddr
      (by
        intro chain ctx setup result hinit hsmashed
        simp [contract, init] at hinit
        cases hinit
        simp at hsmashed)
      (by
        intro chain ctx cstate msg new_cstate acts hQ hreceive
        simp [contract] at hreceive
        exact receive_smashed_balance_zero
          (Base := Base) hQ hreceive)
      hr hdeployed
  exact ⟨cstate, hstate, hQ⟩

theorem balance_is_zero_when_smashed'
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _))) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      (cstate.piggyState = .Smashed →
        bstate.env_account_balances caddr -
            sum_acts (Base := Base) (outgoing_acts bstate caddr) =
          0) := by
  obtain ⟨cstate₁, hstate₁, hzero⟩ :=
    state_balance_zero_when_smashed bstate caddr hr hdeployed
  obtain ⟨cstate₂, hstate₂, hbalance⟩ :=
    balance_on_chain' bstate caddr hr hdeployed
  rw [hstate₁] at hstate₂
  cases hstate₂
  exact ⟨cstate₁, hstate₁, by
    intro hsmashed
    rw [hbalance, hzero hsmashed]⟩

theorem balance_is_zero_when_smashed
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _)))
    (hacts : outgoing_acts bstate caddr = []) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      (cstate.piggyState = .Smashed →
        bstate.env_account_balances caddr = 0) := by
  obtain ⟨cstate, hstate, hzero⟩ :=
    balance_is_zero_when_smashed' bstate caddr hr hdeployed
  refine ⟨cstate, hstate, ?_⟩
  intro hsmashed
  have hz := hzero hsmashed
  rw [hacts] at hz
  simp [sum_acts] at hz
  exact hz

private theorem receive_intact_result_shape
    {chain : Chain} {ctx : @ContractCallContext Base}
    {prev_state next_state : @State Base} {msg : Option Msg}
    {acts : List (@ActionBody Base)}
    (h : receive chain ctx prev_state msg = .Ok (next_state, acts))
    (hnew : next_state.piggyState = .Intact) :
    acts = [] ∧ prev_state.piggyState = .Intact := by
  cases msg with
  | none =>
      simp [receive] at h
  | some msg =>
      cases msg with
      | Insert =>
          unfold receive insert at h
          by_cases hneg : ctx.ctx_amount < 0
          · simp [ConCert.Execution.ContractCommon.throwIf, hneg] at h
          · simp [ConCert.Execution.ContractCommon.throwIf, hneg] at h
            cases hsmashed : is_smashed prev_state <;> simp [hsmashed] at h
            rcases h with ⟨hstate, hacts⟩
            subst next_state
            subst acts
            constructor
            · rfl
            · simpa using hnew
      | Smash =>
          have hcorrect := smash_transfers_correctly prev_state next_state ctx acts h
          rw [hcorrect.1] at hnew
          cases hnew

theorem no_outgoing_actions_when_intact
    (bstate : @ChainState Base) (caddr : Base.Address)
    (hr : reachable bstate)
    (hdeployed :
      bstate.env_contracts caddr =
        some (contract_to_weak_contract
          (contract : @Contract Base Setup Msg (@State Base) Error _ _ _ _))) :
    ∃ cstate,
      @contract_state Base (@State Base) _ bstate.toEnvironment caddr =
        some cstate ∧
      (cstate.piggyState = .Intact → outgoing_acts bstate caddr = []) := by
  obtain ⟨trace⟩ := hr
  let P : Nat → Nat → Nat → Base.Address → @DeploymentInfo Base Setup →
          @State Base → Amount → List (@ActionBody Base) →
          List (@ContractCallInfo Base Msg) → List (@Tx Base) → Prop :=
    fun _ _ _ caddr _ cstate _ out_queue _ _ =>
      (cstate.piggyState = .Intact → out_queue = []) ∧
        out_queue.Forall (noSelfAction (Base := Base) caddr)
  have hcases : ContractInductionCases contract
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
      constructor
      · intro _; rfl
      · simp
    · intro _ _ _ _ _ cstate _ out_act out_acts _ _ _ ih _ _ _ _
      rcases ih with ⟨hintact, hno⟩
      constructor
      · intro hcstate
        have hnil := hintact hcstate
        cases hnil
      · simp only [List.forall_cons] at hno
        exact hno.2
    · intro chain ctx _ prev_state msg prev_out_queue _ _
        new_state new_acts hnot_self _ ih hreceive _
      simp [contract] at hreceive
      rcases ih with ⟨hintact, hno⟩
      constructor
      · intro hnew_intact
        rcases receive_intact_result_shape
            (Base := Base) hreceive hnew_intact with
          ⟨hacts, hprev_intact⟩
        rw [hacts, hintact hprev_intact]
        rfl
      · exact (ConCert.Utils.Extras.Forall_app _ _ _).mp
          ⟨receive_acts_no_self_of_not_self
            (Base := Base) hnot_self hreceive, hno⟩
    · intro _ ctx _ prev_state msg head prev_out_queue _ _ new_state new_acts
        _ _ ih haction hreceive _
      simp [contract] at hreceive
      rcases ih with ⟨hintact, hno⟩
      constructor
      · intro hnew_intact
        rcases receive_intact_result_shape
            (Base := Base) hreceive hnew_intact with
          ⟨_hacts, hprev_intact⟩
        have hnil := hintact hprev_intact
        cases hnil
      · simp only [List.forall_cons] at hno
        cases head with
        | act_transfer to_ amount =>
            rcases haction with ⟨hto, _hamount, _hmsg⟩
            subst to_
            simp [noSelfAction, Address.address_eq_refl] at hno
        | act_deploy amount wc setup =>
            simp [noSelfAction] at hno
        | act_call to_ amount msg_ser =>
            simp [noSelfAction] at hno
    · intro _ _ _ _ _ cstate _ out_queue _ _ out_queue' ih hperm _
      rcases ih with ⟨hintact, hno⟩
      constructor
      · intro hcstate
        have hnil := hintact hcstate
        rw [hnil] at hperm
        exact hperm.symm.eq_nil
      · exact ConCert.Utils.Extras.forall_respects_permutation
          _ _ _ hperm hno
  obtain ⟨_, cstate, _inc_calls, _hdep, hstate, _hcalls, hP⟩ :=
    contract_induction contract _ _ _ P hcases bstate caddr trace hdeployed
  exact ⟨cstate, hstate, hP.1⟩

theorem stay_smashed
    {prev_state : @State Base} {msg : Option Msg} {chain : Chain}
    {ctx : @ContractCallContext Base} :
    prev_state.piggyState = .Smashed →
    ∃ e : Error, receive chain ctx prev_state msg = .Err e := by
  intro hsmashed
  cases prev_state with
  | mk balance owner piggyState =>
      simp only at hsmashed
      subst piggyState
      cases msg with
      | none =>
          exact ⟨error_no_msg, rfl⟩
      | some m =>
          cases m with
          | Insert =>
              unfold receive insert is_smashed
              by_cases hneg : ctx.ctx_amount < 0
              · exact ⟨error_amount_not_positive, by
                  simp [ConCert.Execution.ContractCommon.throwIf, hneg]⟩
              · exact ⟨error_already_smashed, by
                  simp [ConCert.Execution.ContractCommon.throwIf, hneg]⟩
          | Smash =>
              unfold receive smash is_smashed
              by_cases howner : !Base.address_eqb ctx.ctx_from owner
              · exact ⟨error_not_owner, by
                  simp [ConCert.Execution.ContractCommon.throwIf, howner]⟩
              · exact ⟨error_already_smashed, by
                  simp [ConCert.Execution.ContractCommon.throwIf, howner]⟩

theorem if_intact_then_balance_can_only_increase
    (prev_state next_state : @State Base)
    (ctx : @ContractCallContext Base)
    (chain : Chain)
    (new_acts : List (@ActionBody Base)) :
    prev_state.piggyState = .Intact →
    receive chain ctx prev_state (some .Insert) = .Ok (next_state, new_acts) →
    prev_state.balance ≤ next_state.balance := by
  intro hintact hreceive
  unfold receive insert at hreceive
  by_cases hneg : ctx.ctx_amount < 0
  · simp [ConCert.Execution.ContractCommon.throwIf, hneg] at hreceive
  · have hnot_smashed : is_smashed prev_state = false := by
      cases prev_state with
      | mk balance owner piggyState =>
          cases piggyState <;> simp [is_smashed] at hintact ⊢
    simp [ConCert.Execution.ContractCommon.throwIf, hneg, hnot_smashed] at hreceive
    rcases hreceive with ⟨hstate, _hacts⟩
    cases hstate
    have hnonneg : 0 ≤ ctx.ctx_amount := le_of_not_gt hneg
    have hle := add_le_add_left hnonneg prev_state.balance
    simpa using hle

theorem initializes_correctly
    (chain : Chain)
    (ctx : @ContractCallContext Base)
    (setup : Setup)
    (new_state : @State Base) :
    init chain ctx setup = .Ok new_state →
    new_state.piggyState = .Intact := by
  intro h
  unfold init at h
  cases h
  rfl

end ConCert.Examples.PiggyBank.Correctness
