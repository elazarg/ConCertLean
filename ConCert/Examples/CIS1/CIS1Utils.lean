/- Port of examples/cis1/CIS1Utils.v. -/

import Mathlib.Data.List.Basic

namespace ConCert.Examples.CIS1

namespace RemoveProperties

def remove {A : Type} [DecidableEq A] (x : A) (l : List A) : List A :=
  l.filter (fun y => y ≠ x)

theorem mem_remove {A : Type} [DecidableEq A] {x y : A} {l : List A} :
    x ∈ remove y l ↔ x ≠ y ∧ x ∈ l := by
  simp [remove, and_comm]

theorem not_in_remove_same {A : Type} [DecidableEq A]
    (l : List A) (x : A) :
    x ∉ l → remove x l = l := by
  intro hnot
  unfold remove
  rw [List.filter_eq_self]
  intro y hy
  exact decide_eq_true
    (by
      intro hxy
      exact hnot (by simpa [hxy] using hy))

theorem not_in_remove {A : Type} [DecidableEq A]
    (l : List A) (x y : A) :
    x ∉ l → x ∉ remove y l := by
  intro hnot hin
  exact hnot (mem_remove.mp hin).2

theorem remove_remove {A : Type} [DecidableEq A]
    (l : List A) (x y : A) :
    x ∉ remove y (remove x l) := by
  intro hin
  exact (mem_remove.mp (mem_remove.mp hin).2).1 rfl

theorem In_remove {A : Type} [DecidableEq A]
    (l : List A) (x y : A) :
    x ≠ y → x ∈ remove y l → x ∈ l := by
  intro _ hin
  exact (mem_remove.mp hin).2

theorem neq_not_removed {A : Type} [DecidableEq A]
    (l : List A) (x y : A) :
    x ≠ y → x ∈ l → x ∈ remove y l := by
  intro hneq hin
  exact mem_remove.mpr ⟨hneq, hin⟩

def remove_all {A : Type} [DecidableEq A] :
    List A → List A → List A
  | [], xs => xs
  | x :: tl, xs => remove x (remove_all tl xs)

theorem not_mem_remove_all_of_mem {A : Type} [DecidableEq A]
    {to_remove xs : List A} {x : A} :
    x ∈ to_remove → x ∉ remove_all to_remove xs := by
  induction to_remove generalizing xs with
  | nil =>
      simp
  | cons y ys ih =>
      intro hx hin
      simp at hx
      have hin' := mem_remove.mp hin
      rcases hx with hxy | hxys
      · exact hin'.1 hxy
      · exact ih hxys hin'.2

theorem remove_all_In {A : Type} [DecidableEq A]
    (to_remove xs : List A) :
    to_remove.Forall (fun x => x ∉ remove_all to_remove xs) := by
  rw [List.forall_iff_forall_mem]
  intro x hx
  exact not_mem_remove_all_of_mem hx

theorem In_remove_all {A : Type} [DecidableEq A]
    (to_remove xs : List A) (x : A) :
    x ∉ to_remove → x ∈ remove_all to_remove xs → x ∈ xs := by
  induction to_remove generalizing xs with
  | nil =>
      simp [remove_all]
  | cons y ys ih =>
      intro hnot hin
      have hin' := mem_remove.mp (by simpa [remove_all] using hin)
      have hnotys : x ∉ ys := by
        intro hxys
        exact hnot (List.mem_cons_of_mem y hxys)
      exact ih xs hnotys hin'.2

theorem remove_all_not_in_to_remove {A : Type} [DecidableEq A]
    (to_remove xs : List A) (x : A) :
    x ∉ to_remove → x ∈ xs → x ∈ remove_all to_remove xs := by
  induction to_remove generalizing xs with
  | nil =>
      simp [remove_all]
  | cons y ys ih =>
      intro hnot hin
      have hneq : x ≠ y := by
        intro hxy
        exact hnot (by simp [hxy])
      have hnotys : x ∉ ys := by
        intro hxys
        exact hnot (List.mem_cons_of_mem y hxys)
      exact mem_remove.mpr ⟨hneq, ih xs hnotys hin⟩

theorem NoDup_remove {A : Type} [DecidableEq A]
    (l : List A) (x : A) :
    l.Nodup → (remove x l).Nodup := by
  intro hnodup
  simpa [remove] using hnodup.filter (fun y => y ≠ x)

theorem remove_extensional {A : Type} [DecidableEq A]
    (l1 l2 : List A) (y : A) :
    (∀ x, x ∈ l1 ↔ x ∈ l2) →
      (∀ x, x ∈ remove y l1 ↔ x ∈ remove y l2) := by
  intro h x
  simp [mem_remove, h x]

end RemoveProperties

end ConCert.Examples.CIS1
