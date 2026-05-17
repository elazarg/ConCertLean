/- Port of utils/theories/Extras.v. -/

import Mathlib.Data.List.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import ConCert.Utils.Automation

namespace ConCert.Utils.Extras

open List

def withDefault {A : Type} (default : A) : Option A → A
  | some v => v
  | none   => default

/-- Rocq source-name alias. -/
abbrev with_default {A : Type} (default : A) (o : Option A) : A :=
  withDefault default o

def unpackOption {A : Type} : (a : Option A) →
    (match a with | some _ => A | none => Unit)
  | some x => x
  | none   => ()

/-- Rocq source-name alias. -/
abbrev unpack_option {A : Type} (a : Option A) :
    (match a with | some _ => A | none => Unit) :=
  unpackOption a

theorem incl_split
    {A : Type} (l m n : List A) (h : (l ++ m).Subset n) :
    l.Subset n ∧ m.Subset n := by
  refine ⟨?_, ?_⟩
  · intro x hx; exact h (List.mem_append_left m hx)
  · intro x hx; exact h (List.mem_append_right l hx)

theorem NoDup_incl_reorganize
    {A : Type} (l l' : List A)
    (hnd : l'.Nodup) (hsub : l'.Subset l) :
    ∃ suf, List.Perm (l' ++ suf) l := by
  have hsp : List.Subperm l' l := List.subperm_of_subset hnd hsub
  obtain ⟨m, hperm, hsl⟩ := hsp
  obtain ⟨suf, hsuf⟩ := hsl.exists_perm_append
  exact ⟨suf, (hperm.symm.append_right suf).trans hsuf.symm⟩

theorem in_NoDup_app
    {A : Type} (x : A) (l m : List A) (hx : x ∈ l) (hnd : (l ++ m).Nodup) :
    x ∉ m := by
  rw [List.nodup_append] at hnd
  intro hxm
  exact (hnd.2.2 x hx x hxm) rfl

theorem seq_app
    (start len1 len2 : Nat) :
    List.range' start (len1 + len2) =
      List.range' start len1 ++ List.range' (start + len1) len2 := by
  have h := @List.range'_append start len1 len2 1
  -- h : range' start len1 1 ++ range' (start + 1*len1) len2 1 = range' start (len1+len2) 1
  -- range' _ _ defaults to step 1
  rw [Nat.one_mul] at h
  exact h.symm


theorem filter_app
    {A : Type} (pred : A → Bool) (l l' : List A) :
    (l ++ l').filter pred = l.filter pred ++ l'.filter pred :=
  List.filter_append l l'

theorem filter_map
    {A B : Type} (f : A → B) (pred : B → Bool) (l : List A) :
    (l.map f).filter pred = (l.filter (fun a => pred (f a))).map f :=
  List.filter_map

theorem filter_false
    {A : Type} (l : List A) : l.filter (fun _ => false) = [] :=
  List.filter_false l

theorem filter_true
    {A : Type} (l : List A) : l.filter (fun _ => true) = l :=
  List.filter_true l

theorem Permutation_filter
    {A : Type} (pred : A → Bool) (l l' : List A) (h : List.Perm l l') :
    List.Perm (l.filter pred) (l'.filter pred) :=
  h.filter pred

theorem existsb_forallb
    {A : Type} (f : A → Bool) (l : List A) :
    l.any f = !(l.all (fun x => !(f x))) :=
  List.any_eq_not_all_not

def All {A : Type} (f : A → Prop) : List A → Prop
  | []      => True
  | x :: xs => f x ∧ All f xs

theorem All_app
    {A : Type} (f : A → Prop) (l l' : List A) :
    All f (l ++ l') ↔ All f l ∧ All f l' := by
  induction l with
  | nil => simp [All]
  | cons hd tl ih =>
    simp [All, ih]
    tauto

theorem All_map
    {A B : Type} (g : B → Prop) (f : A → B) (l : List A) :
    All g (l.map f) ↔ All (fun a => g (f a)) l := by
  induction l with
  | nil => simp [All, List.map]
  | cons hd tl ih => simp [List.map, All, ih]

theorem All_ext_in
    {A : Type} (f g : A → Prop) (l : List A)
    (hf : All f l) (himp : ∀ a, a ∈ l → f a → g a) : All g l := by
  induction l with
  | nil => exact trivial
  | cons hd tl ih =>
    obtain ⟨hhd, htl⟩ := hf
    refine ⟨himp hd List.mem_cons_self hhd, ih htl ?_⟩
    intro a ha
    exact himp a (List.mem_cons_of_mem _ ha)

private theorem All_mem_imp
    {A : Type} {f : A → Prop} {l : List A}
    (h : All f l) {x : A} (hx : x ∈ l) : f x := by
  induction l with
  | nil => cases hx
  | cons hd tl ih =>
    obtain ⟨hhd, htl⟩ := h
    rw [List.mem_cons] at hx
    cases hx with
    | inl heq => subst heq; exact hhd
    | inr hxr => exact ih htl hxr

theorem All_Forall
    {A : Type} (l : List A) (f : A → Prop) : All f l ↔ l.Forall f := by
  induction l with
  | nil => simp [All]
  | cons _ _ ih => simp [All, ih]

theorem all_incl
    {A : Type} (l l' : List A) (f : A → Prop)
    (h : l.Subset l') (hall : All f l') : All f l := by
  induction l with
  | nil => exact trivial
  | cons hd tl ih =>
    have hsub : tl.Subset l' := fun a ha => h (List.mem_cons_of_mem _ ha)
    have hhd : hd ∈ l' := h List.mem_cons_self
    exact ⟨All_mem_imp hall hhd, ih hsub⟩

theorem forall_respects_permutation
    {A : Type} (xs ys : List A) (P : A → Prop)
    (hp : List.Perm xs ys) (h : xs.Forall P) : ys.Forall P := by
  rw [List.forall_iff_forall_mem] at h ⊢
  intro x hx
  exact h x (hp.symm.mem_iff.mp hx)

theorem Forall_false_filter_nil
    {A : Type} (pred : A → Bool) (l : List A)
    (h : l.Forall (fun a => pred a = false)) : l.filter pred = [] := by
  rw [List.filter_eq_nil_iff]
  intro a ha
  rw [List.forall_iff_forall_mem] at h
  simp [h a ha]

theorem Forall_app
    {A : Type} (P : A → Prop) (l l' : List A) :
    (l.Forall P ∧ l'.Forall P) ↔ (l ++ l').Forall P :=
  List.forall_append.symm

theorem firstn_incl {A : Type} (n : Nat) (l : List A) : (l.take n).Subset l :=
  fun _ hx => List.mem_of_mem_take hx

theorem skipn_incl {A : Type} (n : Nat) (l : List A) : (l.drop n).Subset l :=
  fun _ hx => List.mem_of_mem_drop hx

theorem firstn_map
    {A B : Type} (f : A → B) (n : Nat) (l : List A) :
    (l.map f).take n = (l.take n).map f :=
  (List.map_take (f := f) (l := l) (i := n)).symm

theorem skipn_map
    {A B : Type} (f : A → B) (n : Nat) (l : List A) :
    (l.map f).drop n = (l.drop n).map f :=
  (List.map_drop (f := f) (l := l) (i := n)).symm

theorem map_nth_alt
    {A B : Type} (n : Nat) (l : List A) (f : A → B) (d1 : B) (d2 : A)
    (h : n < l.length) : (l.map f).getD n d1 = f (l.getD n d2) := by
  have hmap : n < (l.map f).length := by simp [h]
  rw [← List.getElem_eq_getD (h := hmap) d1,
      ← List.getElem_eq_getD (h := h) d2]
  exact List.getElem_map _

theorem list_eq_nth
    {A : Type} (xs ys : List A) (hlen : xs.length = ys.length)
    (h : ∀ (i : Nat) (a a' : A),
      (xs[i]? : Option A) = some a → (ys[i]? : Option A) = some a' → a = a') :
    xs = ys := by
  apply List.ext_getElem hlen
  intro i hi hi'
  have ha : xs[i]? = some xs[i] := List.getElem?_eq_getElem hi
  have ha' : ys[i]? = some ys[i] := List.getElem?_eq_getElem hi'
  exact h i xs[i] ys[i] ha ha'

theorem nth_error_seq_in
    (i start len : Nat) (h : i < len) :
    (List.range' start len)[i]? = some (start + i) := by
  rw [List.getElem?_eq_getElem (by simp [h])]
  rw [List.getElem_range']
  simp

theorem nth_error_snoc
    {B : Type} (l : List B) (x : B) :
    (l ++ [x])[l.length]? = some x := by
  rw [List.getElem?_eq_getElem (by simp)]
  rw [List.getElem_append_right (by simp)]
  simp

theorem NoDup_filter
    {A : Type} (f : A → Bool) (l : List A) (h : l.Nodup) : (l.filter f).Nodup :=
  List.Nodup.filter f h

theorem NoDup_map
    {A B : Type} (f : A → B) (l : List A) (h : l.Nodup)
    (hinj : ∀ a a', a ∈ l → a' ∈ l → f a = f a' → a = a') : (l.map f).Nodup :=
  List.Nodup.map_on (fun a ha a' ha' heq => hinj a a' ha ha' heq) h

theorem filter_all
    {A : Type} (f : A → Bool) (l : List A) (h : ∀ a, a ∈ l → f a = true) :
    l.filter f = l :=
  List.filter_eq_self.mpr h

end ConCert.Utils.Extras
