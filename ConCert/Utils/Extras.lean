/- Port of utils/theories/Extras.v. -/

import Mathlib.Data.List.Defs
import Mathlib.Data.List.Perm.Basic
import ConCert.Utils.Automation

namespace ConCert.Utils.Extras

open List

def mapOption {A B : Type} (f : A → Option B) : List A → List B
  | []      => []
  | hd :: tl =>
    match f hd with
    | some b => b :: mapOption f tl
    | none   => mapOption f tl

/-- Coq-name compatibility alias. -/
abbrev map_option {A B : Type} (f : A → Option B) (xs : List A) : List B :=
  mapOption f xs

def withDefault {A : Type} (default : A) : Option A → A
  | some v => v
  | none   => default

/-- Coq-name compatibility alias. -/
abbrev with_default {A : Type} (default : A) (o : Option A) : A :=
  withDefault default o

def unpackOption {A : Type} : (a : Option A) →
    (match a with | some _ => A | none => Unit)
  | some x => x
  | none   => ()

/-- Coq-name compatibility alias. -/
abbrev unpack_option {A : Type} (a : Option A) :
    (match a with | some _ => A | none => Unit) :=
  unpackOption a

def sumZ {A : Type} (f : A → Int) : List A → Int
  | []        => 0
  | x :: xs'  => f x + sumZ f xs'

def sumNat {A : Type} (f : A → Nat) : List A → Nat
  | []        => 0
  | x :: xs'  => f x + sumNat f xs'

def sumN {A : Type} (f : A → Nat) : List A → Nat
  | []        => 0
  | x :: xs'  => f x + sumN f xs'

theorem sumnat_permutation
    {A : Type} {f : A → Nat} {xs ys : List A} (h : List.Perm xs ys) :
    sumNat f xs = sumNat f ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sumNat, ih]
  | swap => simp [sumNat]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sumnat_map
    {A B : Type} (f : A → B) (g : B → Nat) (xs : List A) :
    sumNat g (xs.map f) = sumNat (fun a => g (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => simp [List.map, sumNat, ih]

theorem sumZ_permutation
    {A : Type} {f : A → Int} {xs ys : List A} (h : List.Perm xs ys) :
    sumZ f xs = sumZ f ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sumZ, ih]
  | swap _ _ _ =>
    show _ + (_ + _) = _ + (_ + _)
    rw [← Int.add_assoc, ← Int.add_assoc, Int.add_comm (f _) (f _)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sumZ_app
    {A : Type} {f : A → Int} {xs ys : List A} :
    sumZ f (xs ++ ys) = sumZ f xs + sumZ f ys := by
  induction xs with
  | nil => simp [sumZ]
  | cons hd tl ih => simp [sumZ, ih, Int.add_assoc]

theorem sumZ_map
    {A B : Type} (f : A → B) (g : B → Int) (xs : List A) :
    sumZ g (xs.map f) = sumZ (fun a => g (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => simp [List.map, sumZ, ih]

theorem sumZ_filter
    {A : Type} (f : A → Int) (pred : A → Bool) (xs : List A) :
    sumZ f (xs.filter pred) = sumZ (fun a => if pred a then f a else 0) xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    cases hp : pred hd with
    | true => simp [List.filter, hp, sumZ, ih]
    | false => simp [List.filter, hp, sumZ, ih]

theorem sumZ_mul
    (f : Int → Int) (l : List Int) (z : Int) :
    z * sumZ f l = sumZ (fun z' => z * f z') l := by
  induction l with
  | nil => simp [sumZ]
  | cons hd tl ih => simp [sumZ, Int.mul_add, ← ih]

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
    (l.map f).filter pred = (l.filter (fun a => pred (f a))).map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases hp : pred (f hd) with
    | true => simp [List.filter, List.map, hp, ih]
    | false => simp [List.filter, List.map, hp, ih]

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

def zip {X Y} : List X → List Y → List (X × Y)
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | _, _ => []

theorem zip_app
    {X Y : Type} (xs xs' : List X) (ys ys' : List Y)
    (h : xs.length = ys.length) :
    zip (xs ++ xs') (ys ++ ys') = zip xs ys ++ zip xs' ys' := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons hd tl ih =>
    cases ys with
    | nil => cases h
    | cons hd' tl' =>
      show (hd, hd') :: zip (tl ++ xs') (tl' ++ ys') =
        ((hd, hd') :: zip tl tl') ++ zip xs' ys'
      simp [ih tl' (by simpa using h)]

theorem zip_map
    {A B C D : Type} (f : A → B) (g : C → D) (xs : List A) (ys : List C) :
    zip (xs.map f) (ys.map g) = (zip xs ys).map (fun p => (f p.1, g p.2)) := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> rfl
  | cons hd tl ih =>
    cases ys with
    | nil => rfl
    | cons hd' tl' =>
      show (f hd, g hd') :: zip (tl.map f) (tl'.map g) =
        ((f hd, g hd') :: (zip tl tl').map _)
      rw [ih tl']

theorem existsb_forallb
    {A : Type} (f : A → Bool) (l : List A) :
    l.any f = !(l.all (fun x => !(f x))) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases hfh : f hd with
    | true => simp [List.any, List.all, hfh]
    | false => simp [List.any, List.all, hfh, ih]

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

theorem sumZ_seq_n
    (f : Nat → Int) (n len : Nat) :
    sumZ f (List.range' n len) = sumZ (fun i => f (i + n)) (List.range' 0 len) := by
  have h : List.range' n len = (List.range' 0 len).map (· + n) := by
    have hcomm : (List.range' 0 len).map (· + n) =
        (List.range' 0 len).map (fun x => n + x) := by
      apply List.map_congr_left; intros; rw [Nat.add_comm]
    rw [hcomm]
    have hm := @List.map_add_range' n 0 len 1
    simp at hm
    exact hm.symm
  rw [h, sumZ_map]

theorem sumZ_zero {A : Type} (l : List A) : sumZ (fun _ => 0) l = 0 := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [sumZ, ih]

theorem sumZ_eq
    {A : Type} (f g : A → Int) (l : List A)
    (h : ∀ x, x ∈ l → f x = g x) : sumZ f l = sumZ g l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    show f hd + sumZ f tl = g hd + sumZ g tl
    rw [h hd List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem sumZ_seq_feq
    (f g : Nat → Int) (len : Nat)
    (h : ∀ i, i < len → f i = g i) :
    sumZ g (List.range' 0 len) = sumZ f (List.range' 0 len) := by
  symm
  apply sumZ_eq
  intro x hx
  rw [List.mem_range'] at hx
  obtain ⟨i, hi, hxe⟩ := hx
  have hxi : x = i := by omega
  subst hxi
  exact h x hi

theorem sumZ_firstn
    {A : Type} (default : A) (f : A → Int) (n : Nat) (l : List A)
    (h : n ≤ l.length ∨ f default = 0) :
    sumZ f (l.take n) = sumZ (fun i => f (l.getD i default)) (List.range' 0 n) := by
  induction l generalizing n with
  | nil =>
    have : n = 0 ∨ f default = 0 := by
      rcases h with h | h
      · left; simp at h; exact h
      · right; exact h
    rcases this with hn | hfd
    · subst hn; rfl
    · rw [List.take_nil]
      show (0:Int) = sumZ (fun i => f (([] : List A).getD i default)) (List.range' 0 n)
      have heq : ∀ x, x ∈ List.range' 0 n →
          (fun i => f (([] : List A).getD i default)) x = (fun _ => (0:Int)) x := by
        intros; simp [List.getD]; exact hfd
      rw [sumZ_eq _ _ _ heq, sumZ_zero]
  | cons hd tl ih =>
    cases n with
    | zero => rfl
    | succ k =>
      rw [List.take_succ_cons, List.range'_succ]
      show f hd + sumZ f (tl.take k) =
        f ((hd::tl).getD 0 default) +
          sumZ (fun i => f ((hd::tl).getD i default)) (List.range' 1 k)
      congr 1
      have hsub : k ≤ tl.length ∨ f default = 0 := by
        rcases h with h | h
        · left; simp at h; omega
        · right; exact h
      rw [ih k hsub]
      have hr : List.range' 1 k = (List.range' 0 k).map (· + 1) := by
        have hm := @List.map_add_range' 1 0 k 1
        simp at hm
        have hcomm : (List.range' 0 k).map (· + 1) =
            (List.range' 0 k).map (fun x => 1 + x) := by
          apply List.map_congr_left; intros; omega
        rw [hcomm, hm]
      rw [hr, sumZ_map]
      apply sumZ_eq
      intro x _
      show f (tl.getD x default) = f ((hd::tl).getD (x+1) default)
      rfl

theorem sumZ_skipn
    {A : Type} (default : A) (f : A → Int) (n : Nat) (l : List A) :
    sumZ f (l.drop n) =
      sumZ (fun i => f (l.getD (n + i) default)) (List.range' 0 (l.length - n)) := by
  induction l generalizing n with
  | nil =>
    simp [List.drop_nil]
    rfl
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp only [List.drop_zero, Nat.zero_add, List.length_cons, Nat.sub_zero]
      rw [List.range'_succ]
      show f hd + sumZ f tl = f ((hd::tl).getD 0 default) +
        sumZ (fun i => f ((hd::tl).getD i default)) (List.range' 1 tl.length)
      congr 1
      rw [show sumZ f tl = sumZ f (tl.drop 0) from rfl, ih 0]
      simp only [Nat.zero_add, Nat.sub_zero]
      have hr : List.range' 1 tl.length = (List.range' 0 tl.length).map (· + 1) := by
        have hm := @List.map_add_range' 1 0 tl.length 1
        simp at hm
        have hcomm : (List.range' 0 tl.length).map (· + 1) =
            (List.range' 0 tl.length).map (fun x => 1 + x) := by
          apply List.map_congr_left; intros; omega
        rw [hcomm, hm]
      rw [hr, sumZ_map]
      apply sumZ_eq
      intro x _
      show f (tl.getD x default) = f ((hd::tl).getD (x+1) default)
      rfl
    | succ k =>
      show sumZ f (tl.drop k) =
        sumZ (fun i => f ((hd::tl).getD (k+1+i) default))
          (List.range' 0 ((hd::tl).length - (k+1)))
      have hlen : (hd::tl).length - (k+1) = tl.length - k := by simp
      rw [hlen, ih k]
      apply sumZ_eq
      intro x _
      show f (tl.getD (k+x) default) = f ((hd::tl).getD (k+1+x) default)
      have : k + 1 + x = (k+x) + 1 := by omega
      rw [this]
      rfl

theorem sumZ_add
    {A : Type} (f g : A → Int) (l : List A) :
    sumZ (fun a => f a + g a) l = sumZ f l + sumZ g l := by
  induction l with
  | nil => simp [sumZ]
  | cons hd tl ih =>
    show (f hd + g hd) + sumZ (fun a => f a + g a) tl = (f hd + sumZ f tl) + (g hd + sumZ g tl)
    rw [ih]; omega

theorem sumZ_sub
    {A : Type} (f g : A → Int) (l : List A) :
    sumZ (fun a => f a - g a) l = sumZ f l - sumZ g l := by
  induction l with
  | nil => simp [sumZ]
  | cons hd tl ih =>
    show (f hd - g hd) + sumZ (fun a => f a - g a) tl = (f hd + sumZ f tl) - (g hd + sumZ g tl)
    rw [ih]; omega

theorem sumZ_seq_split
    (split_len : Nat) (f : Nat → Int) (start len : Nat)
    (h : split_len ≤ len) :
    sumZ f (List.range' start len) =
      sumZ f (List.range' start split_len) +
      sumZ f (List.range' (start + split_len) (len - split_len)) := by
  conv_lhs => rw [show len = split_len + (len - split_len) by omega]
  rw [seq_app]
  exact sumZ_app

theorem sumZ_sumZ_swap
    {A B : Type} (f : A → B → Int) (xs : List A) (ys : List B) :
    sumZ (fun a => sumZ (f a) ys) xs = sumZ (fun b => sumZ (fun a => f a b) xs) ys := by
  induction xs with
  | nil =>
    show 0 = sumZ (fun b => sumZ (fun _ => f _ b) []) ys
    simp [sumZ]
    exact (sumZ_zero ys).symm
  | cons hd tl ih =>
    show sumZ (f hd) ys + sumZ (fun a => sumZ (f a) ys) tl =
      sumZ (fun b => f hd b + sumZ (fun a => f a b) tl) ys
    rw [ih]
    rw [← sumZ_add]

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
  | nil => exact ⟨fun _ => trivial, fun _ => trivial⟩
  | cons hd tl ih =>
    match tl with
    | [] =>
      refine ⟨fun ⟨h, _⟩ => ?_, fun h => ?_⟩
      · exact h
      · exact ⟨h, trivial⟩
    | hd' :: tl' =>
      show f hd ∧ All f (hd' :: tl') ↔ f hd ∧ (hd' :: tl').Forall f
      rw [ih]

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
  rw [← All_Forall] at h ⊢
  have hmem : ∀ x, x ∈ xs → x ∈ ys := fun x hx => hp.mem_iff.mp hx
  -- All P xs and ys ⊆ xs (via permutation) ⇒ All P ys
  apply all_incl ys xs P
  · intro x hx; exact hp.symm.mem_iff.mp hx
  · exact h

theorem Forall_false_filter_nil
    {A : Type} (pred : A → Bool) (l : List A)
    (h : l.Forall (fun a => pred a = false)) : l.filter pred = [] := by
  rw [← All_Forall] at h
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨hhd, htl⟩ := h
    rw [List.filter_cons_of_neg (by simp [hhd])]
    exact ih htl

theorem Forall_app
    {A : Type} (P : A → Prop) (l l' : List A) :
    (l.Forall P ∧ l'.Forall P) ↔ (l ++ l').Forall P := by
  rw [← All_Forall, ← All_Forall, ← All_Forall, All_app]

theorem firstn_incl {A : Type} (n : Nat) (l : List A) : (l.take n).Subset l := by
  intro x hx; exact List.mem_of_mem_take hx

theorem skipn_incl {A : Type} (n : Nat) (l : List A) : (l.drop n).Subset l := by
  intro x hx; exact List.mem_of_mem_drop hx

theorem sumZ_map_id
    {A : Type} (f : A → Int) (l : List A) :
    sumZ f l = sumZ id (l.map f) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [sumZ, List.map, ih]

theorem sumZ_le
    {A : Type} (f g : A → Int) (xs : List A)
    (h : ∀ x, x ∈ xs → f x ≤ g x) : sumZ f xs ≤ sumZ g xs := by
  induction xs with
  | nil => exact Int.le_refl _
  | cons hd tl ih =>
    show f hd + sumZ f tl ≤ g hd + sumZ g tl
    have h1 : f hd ≤ g hd := h hd List.mem_cons_self
    have h2 : sumZ f tl ≤ sumZ g tl :=
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem sumZ_nonnegative
    {A : Type} (f : A → Int) (l : List A)
    (h : ∀ x, x ∈ l → 0 ≤ f x) : 0 ≤ sumZ f l := by
  induction l with
  | nil => exact Int.le_refl _
  | cons hd tl ih =>
    show 0 ≤ f hd + sumZ f tl
    have h1 : 0 ≤ f hd := h hd List.mem_cons_self
    have h2 : 0 ≤ sumZ f tl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem sumZ_in_le
    {A : Type} (x : A) (f : A → Int) (l : List A)
    (hnn : ∀ y, y ∈ l → 0 ≤ f y) (hx : x ∈ l) : f x ≤ sumZ f l := by
  induction l with
  | nil => cases hx
  | cons hd tl ih =>
    rw [List.mem_cons] at hx
    show f x ≤ f hd + sumZ f tl
    cases hx with
    | inl heq =>
      subst heq
      have : 0 ≤ sumZ f tl :=
        sumZ_nonnegative f tl (fun y hy => hnn y (List.mem_cons_of_mem _ hy))
      omega
    | inr hxr =>
      have h1 : 0 ≤ f hd := hnn hd List.mem_cons_self
      have h2 : f x ≤ sumZ f tl :=
        ih (fun y hy => hnn y (List.mem_cons_of_mem _ hy)) hxr
      omega

theorem firstn_map
    {A B : Type} (f : A → B) (n : Nat) (l : List A) :
    (l.map f).take n = (l.take n).map f := by
  exact (List.map_take (f := f) (l := l) (i := n)).symm

theorem skipn_map
    {A B : Type} (f : A → B) (n : Nat) (l : List A) :
    (l.map f).drop n = (l.drop n).map f := by
  exact (List.map_drop (f := f) (l := l) (i := n)).symm

theorem map_nth_alt
    {A B : Type} (n : Nat) (l : List A) (f : A → B) (d1 : B) (d2 : A)
    (h : n < l.length) : (l.map f).getD n d1 = f (l.getD n d2) := by
  have hmap : n < (l.map f).length := by simp [h]
  rw [← List.getElem_eq_getD (h := hmap) d1,
      ← List.getElem_eq_getD (h := h) d2]
  exact List.getElem_map _

theorem sumnat_max
    {A : Type} (f : A → Nat) (l : List A) (m : Nat)
    (h : ∀ a, a ∈ l → f a ≤ m) : sumNat f l ≤ m * l.length := by
  induction l with
  | nil => simp [sumNat]
  | cons hd tl ih =>
    show f hd + sumNat f tl ≤ m * (tl.length + 1)
    have h1 : f hd ≤ m := h hd List.mem_cons_self
    have h2 : sumNat f tl ≤ m * tl.length :=
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have hmul : m * (tl.length + 1) = m * tl.length + m := Nat.mul_succ m tl.length
    omega

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
    {A : Type} (f : A → Bool) (l : List A) (h : l.Nodup) : (l.filter f).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hhd, htl⟩ := h
    cases hf : f hd with
    | true =>
      rw [List.filter_cons_of_pos hf, List.nodup_cons]
      refine ⟨?_, ih htl⟩
      intro hin
      exact hhd (List.mem_filter.mp hin).1
    | false =>
      rw [List.filter_cons_of_neg (by simp [hf])]
      exact ih htl

theorem NoDup_map
    {A B : Type} (f : A → B) (l : List A) (h : l.Nodup)
    (hinj : ∀ a a', a ∈ l → a' ∈ l → f a = f a' → a = a') : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hhd, htl⟩ := h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih htl ?_⟩
    · intro hin
      obtain ⟨a, ha, hfa⟩ := List.mem_map.mp hin
      have : hd = a := hinj hd a List.mem_cons_self (List.mem_cons_of_mem _ ha) hfa.symm
      rw [this] at hhd
      exact hhd ha
    · intro a a' ha ha' heq
      exact hinj a a' (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ ha') heq

theorem filter_all
    {A : Type} (f : A → Bool) (l : List A) (h : ∀ a, a ∈ l → f a = true) :
    l.filter f = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : f hd = true := h hd List.mem_cons_self
    simp [List.filter, hhd, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

theorem sumN_permutation
    {A : Type} {f : A → Nat} {xs ys : List A} (h : List.Perm xs ys) :
    sumN f xs = sumN f ys := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [sumN, ih]
  | swap => simp [sumN]; omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem sumN_map
    {A B : Type} (f : A → B) (g : B → Nat) (xs : List A) :
    sumN g (xs.map f) = sumN (fun a => g (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [List.map, sumN, ih]

theorem sumN_map_id
    {A : Type} (f : A → Nat) (l : List A) : sumN f l = sumN id (l.map f) := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [sumN, List.map, ih]

theorem sumN_app
    {A : Type} {f : A → Nat} {xs ys : List A} :
    sumN f (xs ++ ys) = sumN f xs + sumN f ys := by
  induction xs with
  | nil => simp [sumN]
  | cons _ _ ih => simp [sumN, ih]; omega

theorem sumN_split
    {A : Type} (f : A → Nat) (x y z : A) (xs : List A) (h : f z = f x + f y) :
    sumN f (z :: xs) = sumN f (x :: y :: xs) := by
  simp [sumN, h]; omega

theorem sumN_swap
    {A : Type} (f : A → Nat) (x y : A) (xs : List A) :
    sumN f (x :: y :: xs) = sumN f (y :: x :: xs) := by
  simp [sumN]; omega

theorem sumN_in_le
    {A : Type} (f : A → Nat) (x : A) (xs : List A) (h : x ∈ xs) :
    f x ≤ sumN f xs := by
  induction xs with
  | nil => cases h
  | cons hd tl ih =>
    rw [List.mem_cons] at h
    show f x ≤ f hd + sumN f tl
    cases h with
    | inl heq => subst heq; omega
    | inr hx => have := ih hx; omega

theorem sumN_inv
    {A : Type} (f : A → Nat) (x : A) (xs : List A) :
    sumN f xs + f x = sumN f (x :: xs) := by
  simp [sumN]; omega

def isSome {A : Type} : Option A → Bool
  | some _ => true
  | none   => false

def isNone {A : Type} : Option A → Bool
  | some _ => false
  | none   => true

theorem with_default_is_some
    {A : Type} (x : Option A) (y : A) (h : isSome x = false) :
    withDefault y x = y := by
  cases x with
  | none => rfl
  | some a => cases h

theorem with_default_indep
    {A : Type} (o : Option A) (d d' v : A) (h : o = some v) :
    withDefault d o = withDefault d' o := by
  subst h; rfl

theorem isSome_some
    {A : Type} (x : Option A) (y : A) (h : x = some y) : isSome x = true := by
  subst h; rfl

theorem isSome_none
    {A : Type} (x : Option A) (h : x = none) : isSome x = false := by
  subst h; rfl

theorem isSome_exists
    {A : Type} (x : Option A) : isSome x = true ↔ ∃ y : A, x = some y := by
  cases x with
  | none =>
    refine ⟨fun h => ?_, fun ⟨_, h⟩ => ?_⟩
    · cases h
    · cases h
  | some a => exact ⟨fun _ => ⟨a, rfl⟩, fun _ => rfl⟩

theorem isSome_not_exists
    {A : Type} (x : Option A) : isSome x = false ↔ ∀ y : A, x ≠ some y := by
  cases x with
  | none =>
    refine ⟨?_, ?_⟩
    · intro _ _ h; cases h
    · intro _; rfl
  | some a =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h
    · exact absurd rfl (h a)

end ConCert.Utils.Extras
