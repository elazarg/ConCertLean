/- Port of execution/theories/BoundedN.v
   `N` (binary naturals) and `Nat` are unified to_ `Nat` here. -/

import ConCert.Execution.Finite
import ConCert.Execution.Monad
import ConCert.Execution.OptionMonad
import ConCert.Execution.Containers
import ConCert.Utils.Extras

namespace ConCert.Execution

open ConCert.Execution.Containers

/-- A natural number strictly less than `bound`. -/
structure BoundedN (bound : Nat) where
  val : Nat
  lt : val < bound

namespace BoundedN

def to_N {bound : Nat} (n : BoundedN bound) : Nat := n.val

def eqb {bound : Nat} (a b : BoundedN bound) : Bool :=
  a.to_N == b.to_N

def of_N {bound : Nat} (n : Nat) : Option (BoundedN bound) :=
  if h : n < bound then some ⟨n, h⟩ else none

def to_nat {bound : Nat} (n : BoundedN bound) : Nat := n.to_N
def of_nat {bound : Nat} (n : Nat) : Option (BoundedN bound) := of_N n
def to_Z {bound : Nat} (n : BoundedN bound) : Int := Int.ofNat n.to_N
def of_Z {bound : Nat} (z : Int) : Option (BoundedN bound) :=
  if z < 0 then none else of_N z.toNat

/-- `of_Z_const` mirrors Coq's `unpack_option (of_Z bound z)`: its return type
    *depends* on whether `of_Z bound z` succeeds — `BoundedN bound` if it does,
    `Unit` if it doesn't. Practical call sites pin `bound` to a positive
    constant and supply a valid `z`, so the `BoundedN bound` branch is taken. -/
def of_Z_const (bound : Nat) (z : Int) :
    (match of_Z (bound := bound) z with | some _ => BoundedN bound | none => Unit) :=
  match of_Z (bound := bound) z with
  | some b => b
  | none   => ()

theorem to_N_inj
    {bound : Nat} {a b : BoundedN bound} (h : to_N a = to_N b) : a = b := by
  cases a; cases b; cases h; rfl

theorem eqb_refl {bound : Nat} (n : BoundedN bound) : eqb n n = true := by
  unfold eqb; exact beq_self_eq_true _

theorem eqb_spec {bound : Nat} (a b : BoundedN bound) : eqb a b = true ↔ a = b := by
  unfold eqb
  rw [beq_iff_eq]
  constructor
  · exact to_N_inj
  · intro h
    rw [h]

theorem to_nat_inj
    {bound : Nat} (a b : BoundedN bound) (h : to_nat a = to_nat b) : a = b :=
  to_N_inj h

theorem to_Z_inj
    {bound : Nat} (a b : BoundedN bound) (h : to_Z a = to_Z b) : a = b := by
  apply to_N_inj
  show a.val = b.val
  have : (Int.ofNat a.val : Int) = Int.ofNat b.val := h
  exact Int.ofNat.inj this

theorem of_to_N {bound : Nat} (n : BoundedN bound) : of_N (to_N n) = some n := by
  unfold of_N to_N
  rw [dif_pos n.lt]

theorem of_to_nat
    {bound : Nat} (n : BoundedN bound) : of_nat (to_nat n) = some n := of_to_N n

theorem of_to_Z {bound : Nat} (n : BoundedN bound) : of_Z (to_Z n) = some n := by
  unfold of_Z to_Z to_N
  have hge : ¬ (Int.ofNat n.val : Int) < 0 := by
    have : (0 : Int) ≤ Int.ofNat n.val := Int.natCast_nonneg _
    omega
  rw [if_neg hge]
  show of_N (Int.ofNat n.val).toNat = some n
  have : (Int.ofNat n.val).toNat = n.val := by simp
  rw [this]
  exact of_to_N n

theorem of_N_some
    {bound : Nat} {m : Nat} {n : BoundedN bound}
    (h : of_N m = some n) : to_N n = m := by
  unfold of_N at h
  split at h
  · cases h; rfl
  · cases h

theorem of_N_none
    {bound : Nat} {m : Nat} (h : @of_N bound m = none) : bound ≤ m := by
  unfold of_N at h
  split at h
  · cases h
  · exact Nat.le_of_not_lt (by assumption)

theorem of_nat_some
    {bound : Nat} {m : Nat} {n : BoundedN bound}
    (h : of_nat m = some n) : to_nat n = m := of_N_some h

theorem of_nat_none
    {bound : Nat} {m : Nat} (h : @of_nat bound m = none) : bound ≤ m :=
  of_N_none h

private theorem mem_mapOption_iff {A B : Type} (f : A → Option B) (b : B)
    (xs : List A) :
    b ∈ ConCert.Utils.Extras.mapOption f xs ↔ ∃ a ∈ xs, f a = some b := by
  induction xs with
  | nil => simp [ConCert.Utils.Extras.mapOption]
  | cons hd tl ih =>
    unfold ConCert.Utils.Extras.mapOption
    split
    · next b' hb' =>
      simp only [List.mem_cons]
      constructor
      · rintro (rfl | hin)
        · exact ⟨hd, by simp, hb'⟩
        · obtain ⟨a, ha, hfa⟩ := ih.mp hin
          exact ⟨a, Or.inr ha, hfa⟩
      · rintro ⟨a, (rfl | hin), hfa⟩
        · rw [hb'] at hfa
          left; exact (Option.some.injEq _ _).mp hfa.symm
        · exact Or.inr (ih.mpr ⟨a, hin, hfa⟩)
    · next hb' =>
      simp only [List.mem_cons]
      constructor
      · intro hin
        obtain ⟨a, ha, hfa⟩ := ih.mp hin
        exact ⟨a, Or.inr ha, hfa⟩
      · rintro ⟨a, (rfl | hin), hfa⟩
        · rw [hb'] at hfa; cases hfa
        · exact ih.mpr ⟨a, hin, hfa⟩

theorem in_map_of_nat
    (bound : Nat) (n : BoundedN bound) (xs : List Nat) :
    n ∈ ConCert.Utils.Extras.mapOption (@of_nat bound) xs ↔ to_nat n ∈ xs := by
  rw [mem_mapOption_iff]
  constructor
  · rintro ⟨a, ha, hfa⟩
    have := of_nat_some hfa
    rw [this]; exact ha
  · intro hin
    exact ⟨to_nat n, hin, of_to_nat n⟩

def bounded_elements (bound : Nat) : List (BoundedN bound) :=
  ConCert.Utils.Extras.mapOption of_nat (List.range bound)

private theorem nodup_mapOption_of_inj {A B : Type} (f : A → Option B)
    (xs : List A) (hxs : xs.Nodup)
    (hinj : ∀ {a a' : A} {b : B}, f a = some b → f a' = some b → a = a') :
    (ConCert.Utils.Extras.mapOption f xs).Nodup := by
  induction xs with
  | nil => simp [ConCert.Utils.Extras.mapOption]
  | cons hd tl ih =>
    unfold ConCert.Utils.Extras.mapOption
    cases hxs with
    | cons hhd htl =>
      split
      · next b hb =>
        refine List.nodup_cons.mpr ⟨?_, ih htl⟩
        intro hbin
        obtain ⟨a, ha, hfa⟩ := (mem_mapOption_iff f b tl).mp hbin
        have := hinj hb hfa
        subst this
        exact hhd hd ha rfl
      · exact ih htl

theorem bounded_elements_set (bound : Nat) :
    List.Nodup (bounded_elements bound) := by
  unfold bounded_elements
  apply nodup_mapOption_of_inj _ _ List.nodup_range
  intro a a' b ha ha'
  exact (of_nat_some ha).symm.trans (of_nat_some ha')

theorem bounded_elements_all
    (bound : Nat) (a : BoundedN bound) : a ∈ bounded_elements bound := by
  unfold bounded_elements
  rw [in_map_of_nat]
  exact List.mem_range.mpr a.lt

instance BoundedN_finite {bound : Nat} : ConCert.Execution.Finite.Finite (BoundedN bound) where
  elements := bounded_elements bound
  elements_set := bounded_elements_set bound
  elements_all := bounded_elements_all bound

/-- Compare `BoundedN` values by their underlying `val`. Inherits transitivity
    and equality-coherence from `Nat`'s `LawfulOrd`. -/
instance instOrd {bound : Nat} : Ord (BoundedN bound) where
  compare a b := compare a.val b.val

instance instLawfulOrd {bound : Nat} : LawfulOrd (BoundedN bound) where
  eq_swap {a b} := by
    show compare a.val b.val = (compare b.val a.val).swap
    exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} := by
    show (compare a.val b.val).isLE → (compare b.val c.val).isLE →
         (compare a.val c.val).isLE
    exact Std.TransCmp.isLE_trans
  compare_self {a} := by
    show compare a.val a.val = .eq
    exact Std.ReflCmp.compare_self
  eq_of_compare {a b} := by
    show compare a.val b.val = .eq → a = b
    intro h
    have hval : a.val = b.val := Std.LawfulEqCmp.eq_of_compare h
    cases a; cases b; congr

end BoundedN

end ConCert.Execution
