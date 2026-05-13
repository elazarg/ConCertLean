/- Port of utils/theories/Automation.v.

The original is entirely Ltac tactics (`appify`, `perm_simplify`, `destruct_match`,
`propify`, `destruct_hyps`, etc.). These are not directly portable; they will be
re-implemented as Lean 4 tactic macros when proofs are elaborated. For now this
file is a placeholder so that downstream `import`s resolve. -/

namespace ConCert.Utils.Automation

-- TODO: port tactics: appify, perm_simplify, destruct_match, propify,
-- destruct_units, solve_by_rewrite, solve_by_inversion, specialize_hypotheses,
-- unset_all, destruct_or_hyps, destruct_hyps, destruct_and_split, tryfalse.

axiom Permutation_app_middle :
  ∀ {A : Type} (xs l1 l2 l3 l4 : List A),
    List.Perm (l1 ++ l2) (l3 ++ l4) →
    List.Perm (l1 ++ xs ++ l2) (l3 ++ xs ++ l4)

end ConCert.Utils.Automation
