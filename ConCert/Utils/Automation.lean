/- Port of utils/theories/Automation.v.

The original is entirely Ltac tactics (`appify`, `perm_simplify`, `destruct_match`,
`propify`, `destruct_hyps`, etc.). Lean tactic scripts still need local
adaptation, but the common names below give proof ports small, predictable
wrappers around Lean's native tactics. -/

namespace ConCert.Utils.Automation

syntax "appify" : tactic
syntax "perm_simplify" : tactic
syntax "destruct_match" : tactic
syntax "propify" : tactic
syntax "destruct_units" : tactic
syntax "solve_by_rewrite" : tactic
syntax "solve_by_inversion" : tactic
syntax "specialize_hypotheses" : tactic
syntax "unset_all" : tactic
syntax "destruct_or_hyps" : tactic
syntax "destruct_hyps" : tactic
syntax "destruct_and_split" : tactic
syntax "tryfalse" : tactic

macro_rules
  | `(tactic| appify) =>
      `(tactic| try simp only [List.cons_append, List.singleton_append])
  | `(tactic| perm_simplify) =>
      `(tactic| first | simpa using List.Perm.refl _ | simp_all)
  | `(tactic| destruct_match) =>
      `(tactic| split <;> simp_all)
  | `(tactic| propify) =>
      `(tactic| simp_all)
  | `(tactic| destruct_units) =>
      `(tactic| subst_vars <;> simp_all)
  | `(tactic| solve_by_rewrite) =>
      `(tactic| first | simp_all | assumption)
  | `(tactic| solve_by_inversion) =>
      `(tactic| first | contradiction | simp_all)
  | `(tactic| specialize_hypotheses) =>
      `(tactic| try simp_all)
  | `(tactic| unset_all) =>
      `(tactic| try subst_vars)
  | `(tactic| destruct_or_hyps) =>
      `(tactic| try simp_all)
  | `(tactic| destruct_hyps) =>
      `(tactic| try simp_all)
  | `(tactic| destruct_and_split) =>
      `(tactic| repeat' first | constructor | simp_all)
  | `(tactic| tryfalse) =>
      `(tactic| try (first | contradiction | simp_all))

theorem Permutation_app_middle
    {A : Type} (xs l1 l2 l3 l4 : List A)
    (h : List.Perm (l1 ++ l2) (l3 ++ l4)) :
    List.Perm (l1 ++ xs ++ l2) (l3 ++ xs ++ l4) := by
  have h1 : List.Perm (l1 ++ xs ++ l2) ((l1 ++ l2) ++ xs) := by
    rw [List.append_assoc, List.append_assoc]
    exact List.perm_append_comm.append_left _
  have h2 : List.Perm ((l3 ++ l4) ++ xs) (l3 ++ xs ++ l4) := by
    rw [List.append_assoc, List.append_assoc]
    exact List.perm_append_comm.append_left _
  exact h1.trans ((h.append_right xs).trans h2)

end ConCert.Utils.Automation
