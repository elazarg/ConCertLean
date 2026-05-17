/- Port of the non-tactic helper retained from utils/theories/Automation.v.

The Rocq file is mostly Ltac. Those tactics are not part of the executable or
proved Lean surface unless a ported proof actually uses them. -/

namespace ConCert.Utils.Automation

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
