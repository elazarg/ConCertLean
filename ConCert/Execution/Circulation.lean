/- Port of execution/theories/Circulation.v -/

import Mathlib.Tactic.Linarith
import ConCert.Utils.Extras
import ConCert.Execution.BlockchainBase
import ConCert.Execution.BlockchainTheories
import ConCert.Execution.Finite

namespace ConCert.Execution.Circulation

open ConCert.Execution.BlockchainBase
open ConCert.Execution.BlockchainTheories
open ConCert.Execution.Finite
open ConCert.Execution.ChainedList
open ConCert.Utils.Extras

variable [Base : ChainBase] [Finite Base.Address]

def circulation (env : @Environment Base) : Int :=
  sumZ env.env_account_balances (Finite.elements (T := Base.Address))

theorem address_reorganize
    {a b : Base.Address} (h : a ≠ b) :
    ∃ suf, List.Perm ([a, b] ++ suf) (Finite.elements (T := Base.Address)) := by
  apply NoDup_incl_reorganize _ [a, b]
  · -- [a, b].Nodup
    rw [List.nodup_cons]
    refine ⟨?_, List.nodup_singleton _⟩
    intro hin
    rw [List.mem_singleton] at hin
    exact h hin
  · -- [a, b].Subset elements
    intro x hx
    rw [List.mem_cons, List.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finite.elements_all _
    · exact Finite.elements_all _

theorem eval_action_from_to_same
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (eval : ActionEvaluation pre act post new_acts)
    (h_eq : ActionEvaluation.eval_from eval = ActionEvaluation.eval_to eval) :
    circulation post = circulation pre := by
  unfold circulation
  induction (Finite.elements (T := Base.Address)) with
  | nil => rfl
  | cons hd tl ih =>
    show post.env_account_balances hd + sumZ _ tl =
         pre.env_account_balances hd + sumZ _ tl
    rw [ih, account_balance_post eval, h_eq]
    -- After h_eq, both ifs have the same condition (addr_eqb hd eval_to)
    show (pre.env_account_balances hd +
            (if Base.address_eqb hd (ActionEvaluation.eval_to eval) then
                ActionEvaluation.eval_amount eval else 0) -
            (if Base.address_eqb hd (ActionEvaluation.eval_to eval) then
                ActionEvaluation.eval_amount eval else 0) : Int) +
          sumZ pre.env_account_balances tl =
          pre.env_account_balances hd + sumZ pre.env_account_balances tl
    by_cases ht : Base.address_eqb hd (ActionEvaluation.eval_to eval) = true
    · rw [if_pos ht]; linarith
    · rw [if_neg ht]; linarith

theorem eval_action_circulation_unchanged
    {pre post : @Environment Base} {act : @Action Base}
    {new_acts : List (@Action Base)}
    (eval : ActionEvaluation pre act post new_acts) :
    circulation post = circulation pre := by
  by_cases h_eq : ActionEvaluation.eval_from eval = ActionEvaluation.eval_to eval
  · exact eval_action_from_to_same eval h_eq
  · obtain ⟨suf, perm⟩ := address_reorganize h_eq
    have perm_sym := perm.symm
    unfold circulation
    rw [sumZ_permutation perm_sym, sumZ_permutation (f := pre.env_account_balances) perm_sym]
    -- Both LHS and RHS now have sumZ over [eval_from, eval_to] ++ suf
    show post.env_account_balances (ActionEvaluation.eval_from eval) +
         (post.env_account_balances (ActionEvaluation.eval_to eval) +
          sumZ post.env_account_balances suf) =
         pre.env_account_balances (ActionEvaluation.eval_from eval) +
         (pre.env_account_balances (ActionEvaluation.eval_to eval) +
          sumZ pre.env_account_balances suf)
    rw [account_balance_post_to eval h_eq, account_balance_post_from eval h_eq]
    -- It remains to show: sumZ post suf = sumZ pre suf
    -- Use that eval_from and eval_to are not in suf (from Perm + NoDup of elements).
    have nodup_full : List.Nodup ([ActionEvaluation.eval_from eval,
                                    ActionEvaluation.eval_to eval] ++ suf) := by
      exact (perm.nodup_iff).mpr Finite.elements_set
    have from_not_in_suf : ActionEvaluation.eval_from eval ∉ suf := by
      apply in_NoDup_app _ [ActionEvaluation.eval_from eval,
                             ActionEvaluation.eval_to eval]
      · exact List.mem_cons_self
      · exact nodup_full
    have to_not_in_suf : ActionEvaluation.eval_to eval ∉ suf := by
      apply in_NoDup_app _ [ActionEvaluation.eval_from eval,
                             ActionEvaluation.eval_to eval]
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact nodup_full
    have hsuf : sumZ post.env_account_balances suf = sumZ pre.env_account_balances suf := by
      clear perm perm_sym nodup_full
      induction suf with
      | nil => rfl
      | cons x xs ih =>
        have hx_from : x ≠ ActionEvaluation.eval_from eval := by
          intro heq; subst heq; exact from_not_in_suf List.mem_cons_self
        have hx_to : x ≠ ActionEvaluation.eval_to eval := by
          intro heq; subst heq; exact to_not_in_suf List.mem_cons_self
        have hf' : ActionEvaluation.eval_from eval ∉ xs :=
          fun h => from_not_in_suf (List.mem_cons_of_mem _ h)
        have ht' : ActionEvaluation.eval_to eval ∉ xs :=
          fun h => to_not_in_suf (List.mem_cons_of_mem _ h)
        show post.env_account_balances x + sumZ post.env_account_balances xs =
             pre.env_account_balances x + sumZ pre.env_account_balances xs
        rw [ih hf' ht', account_balance_post_irrelevant eval x hx_from hx_to]
    rw [hsuf]; linarith

theorem circulation_proper
    (e1 e2 : @Environment Base) (h : EnvironmentEquiv e1 e2) :
    circulation e1 = circulation e2 := by
  unfold circulation
  have hfn : e1.env_account_balances = e2.env_account_balances := by
    funext a; exact h.account_balances_eq a
  rw [hfn]

theorem circulation_add_new_block
    (header : @BlockHeader Base) (env : @Environment Base) :
    circulation (add_new_block_to_env header env) =
      circulation env + header.block_reward := by
  -- Reorganize elements so block_creator is first
  have hp : ∃ suf, List.Perm ([header.block_creator] ++ suf)
              (Finite.elements (T := Base.Address)) := by
    apply NoDup_incl_reorganize _ [header.block_creator]
    · exact List.nodup_singleton _
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact Finite.elements_all _
  obtain ⟨suf, perm⟩ := hp
  have perm_sym := perm.symm
  unfold circulation
  rw [sumZ_permutation perm_sym, sumZ_permutation (f := env.env_account_balances) perm_sym]
  -- balances of (add_new_block_to_env header env) = add_balance creator reward env.balances
  -- Element block_creator: env.balances creator + reward; others: same.
  show (add_new_block_to_env header env).env_account_balances header.block_creator +
        sumZ (add_new_block_to_env header env).env_account_balances suf =
        env.env_account_balances header.block_creator + sumZ env.env_account_balances suf +
          header.block_reward
  have h_creator : (add_new_block_to_env header env).env_account_balances header.block_creator =
                    env.env_account_balances header.block_creator + header.block_reward := by
    show add_balance header.block_creator header.block_reward _ _ = _
    unfold add_balance
    rw [if_pos (Address.address_eq_refl _)]; linarith
  rw [h_creator]
  -- For elements in suf, block_creator ∉ suf (from Perm + NoDup of elements).
  have nodup_full : List.Nodup ([header.block_creator] ++ suf) :=
    (perm.nodup_iff).mpr Finite.elements_set
  have creator_not_in_suf : header.block_creator ∉ suf := by
    apply in_NoDup_app _ [header.block_creator]
    · exact List.mem_cons_self
    · exact nodup_full
  have hsuf : sumZ (add_new_block_to_env header env).env_account_balances suf =
              sumZ env.env_account_balances suf := by
    clear perm perm_sym nodup_full
    induction suf with
    | nil => rfl
    | cons x xs ih =>
      have hx_ne : x ≠ header.block_creator := by
        intro heq; subst heq; exact creator_not_in_suf List.mem_cons_self
      have hin' : header.block_creator ∉ xs :=
        fun h => creator_not_in_suf (List.mem_cons_of_mem _ h)
      show (add_new_block_to_env header env).env_account_balances x +
            sumZ (add_new_block_to_env header env).env_account_balances xs =
            env.env_account_balances x + sumZ env.env_account_balances xs
      rw [ih hin']
      have hx_balance : (add_new_block_to_env header env).env_account_balances x =
                        env.env_account_balances x := by
        show add_balance header.block_creator header.block_reward _ _ = _
        unfold add_balance
        rw [if_neg]
        intro habs
        exact hx_ne (((Base.address_eqb_spec _ _).mp habs))
      rw [hx_balance]
  rw [hsuf]; linarith

theorem step_circulation {prev next : @ChainState Base} (step : ChainStep prev next) :
    circulation next.toEnvironment =
      (match step with
       | .step_block hdr _ _ _ _ _ => circulation prev.toEnvironment + hdr.block_reward
       | _ => circulation prev.toEnvironment) := by
  cases step with
  | step_block hdr _ _ _ _ henv =>
    show circulation next.toEnvironment = _
    rw [circulation_proper next.toEnvironment _ henv]
    exact circulation_add_new_block _ _
  | step_action _ _ _ _ eval _ =>
    exact eval_action_circulation_unchanged eval
  | step_action_invalid _ _ henv _ _ _ _ =>
    exact circulation_proper next.toEnvironment _ henv
  | step_permute henv _ =>
    exact circulation_proper next.toEnvironment _ henv

theorem chain_trace_circulation
    {state : @ChainState Base} (trace : ChainTrace empty_state state) :
    circulation state.toEnvironment =
      sumZ (fun h => @BlockHeader.block_reward Base h) (trace_blocks trace) := by
  induction trace with
  | clnil =>
    -- circulation of empty_state = 0
    unfold circulation
    show sumZ (fun _ => (0 : Int)) _ = sumZ _ (trace_blocks ChainedList.clnil)
    rw [sumZ_zero]
    simp [trace_blocks, sumZ]
  | snoc tail s ih =>
    simp only [trace_blocks, sumZ_app]
    cases s with
    | step_block hdr _ _ _ _ henv =>
      rw [circulation_proper _ _ henv, circulation_add_new_block, ih]
      show _ = sumZ (fun h => h.block_reward) [hdr] + _
      simp [sumZ]; linarith
    | step_action _ _ _ _ eval _ =>
      rw [eval_action_circulation_unchanged eval, ih]
      show _ = sumZ _ [] + _
      simp [sumZ]
    | step_action_invalid _ _ henv _ _ _ _ =>
      rw [circulation_proper _ _ henv, ih]
      show _ = sumZ _ [] + _
      simp [sumZ]
    | step_permute henv _ =>
      rw [circulation_proper _ _ henv, ih]
      show _ = sumZ _ [] + _
      simp [sumZ]

end ConCert.Execution.Circulation
