/- Port of execution/theories/Containers.v.

   `FMap` is backed by `Std.ExtTreeMap` (quotient-extensional ordered
   tree map): two maps with the same `find` view are propositionally
   equal. `Std.TreeMap` would not work — it exposes tree shape, so
   distinct insertion orders give distinct values. -/

import Std.Data.ExtTreeMap
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise

namespace ConCert.Execution.Containers

/-- `Ord` that agrees with propositional equality on `.eq` and is
    transitive. Bundles `Std.TransCmp` (needed by `ExtTreeMap`'s API) and
    `Std.LawfulEqCmp` (so `compare a b = .eq ↔ a = b`). -/
class LawfulOrd (α : Type) [Ord α] : Prop extends
  Std.TransCmp (α := α) compare,
  Std.LawfulEqCmp (α := α) compare

theorem LawfulOrd.compare_eq_iff_eq {α : Type} [Ord α] [LawfulOrd α] (a b : α) :
    compare a b = Ordering.eq ↔ a = b := by
  constructor
  · exact Std.LawfulEqCmp.eq_of_compare
  · intro h; subst h; exact Std.ReflCmp.compare_self

instance instLawfulOrdNat : LawfulOrd Nat where
  eq_swap {a b} := by
    exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} := by
    exact Std.TransCmp.isLE_trans
  compare_self {a} := by
    exact Std.ReflCmp.compare_self
  eq_of_compare {a b} := by
    intro h
    exact Std.LawfulEqCmp.eq_of_compare h

instance instLawfulOrdInt : LawfulOrd Int where
  eq_swap {a b} := by
    exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} := by
    exact Std.TransCmp.isLE_trans
  compare_self {a} := by
    exact Std.ReflCmp.compare_self
  eq_of_compare {a b} := by
    intro h
    exact Std.LawfulEqCmp.eq_of_compare h

instance instLawfulOrdString : LawfulOrd String where
  eq_swap {a b} := by
    exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} := by
    exact Std.TransCmp.isLE_trans
  compare_self {a} := by
    exact Std.ReflCmp.compare_self
  eq_of_compare {a b} := by
    intro h
    exact Std.LawfulEqCmp.eq_of_compare h

instance instOrdProd {α β : Type} [Ord α] [Ord β] : Ord (α × β) :=
  Ord.lex inferInstance inferInstance

instance instLawfulOrdProd {α β : Type} [Ord α] [LawfulOrd α] [Ord β] [LawfulOrd β] :
    LawfulOrd (α × β) where
  eq_swap {a b} := by
    exact Std.OrientedCmp.eq_swap
  isLE_trans {a b c} := by
    exact Std.TransCmp.isLE_trans
  compare_self {a} := by
    exact Std.ReflCmp.compare_self
  eq_of_compare {a b} := by
    intro h
    exact Std.LawfulEqCmp.eq_of_compare h

/-- Finite map. Backed by `Std.ExtTreeMap`; equality is map equality. -/
abbrev FMap (K : Type) [Ord K] [LawfulOrd K] (V : Type) : Type :=
  Std.ExtTreeMap K V compare

namespace FMap

variable {K : Type} [Ord K] [LawfulOrd K] {V : Type}

/-! ### Core operations — thin wrappers over the `ExtTreeMap` API. -/

def empty : FMap K V := Std.ExtTreeMap.empty

def lookup (k : K) (m : FMap K V) : Option V := Std.ExtTreeMap.get? m k

abbrev find (k : K) (m : FMap K V) : Option V := lookup k m

def mem (k : K) (m : FMap K V) : Bool := Std.ExtTreeMap.contains m k

def add (k : K) (v : V) (m : FMap K V) : FMap K V := Std.ExtTreeMap.insert m k v

def remove (k : K) (m : FMap K V) : FMap K V := Std.ExtTreeMap.erase m k

def elements (m : FMap K V) : List (K × V) := Std.ExtTreeMap.toList m

def size (m : FMap K V) : Nat := Std.ExtTreeMap.size m

def of_list (l : List (K × V)) : FMap K V := Std.ExtTreeMap.ofList l compare

/-- First-map-biased union (matches stdpp's `union`): on key collisions,
    the value from `m1` wins. Implemented by starting from `m2` and
    inserting every `(k, v)` from `m1` over the top — `ExtTreeMap.insert`
    overwrites, so `m1`'s entries dominate. -/
def union (m1 m2 : FMap K V) : FMap K V :=
  Std.ExtTreeMap.insertMany m2 (Std.ExtTreeMap.toList m1)

def alter (f : V → V) (k : K) (m : FMap K V) : FMap K V :=
  Std.ExtTreeMap.alter m k (Option.map f)

def partial_alter (f : Option V → Option V) (k : K) (m : FMap K V) : FMap K V :=
  Std.ExtTreeMap.alter m k f

def keys (m : FMap K V) : List K := (elements m).map Prod.fst
def values (m : FMap K V) : List V := (elements m).map Prod.snd

def update (key : K) (value : Option V) (m : FMap K V) : FMap K V :=
  match value with
  | some n => add key n m
  | none => remove key m

/-! ### Extensional equality (now coincides with `=` because `ExtTreeMap`
    is quotient-extensional). -/

def extEq (m1 m2 : FMap K V) : Prop := ∀ k, find k m1 = find k m2

/-! ### Algebraic facts. -/

private theorem cmp_eq_iff (k k' : K) : compare k k' = Ordering.eq ↔ k = k' :=
  LawfulOrd.compare_eq_iff_eq k k'

private theorem cmp_self (k : K) : compare k k = Ordering.eq :=
  Std.ReflCmp.compare_self

theorem find_empty (k : K) : find k (empty : FMap K V) = none := by
  simp [find, lookup, empty]

theorem find_add (k : K) (v : V) (m : FMap K V) : find k (add k v m) = some v := by
  simp [find, lookup, add]

theorem find_add_ne (k k' : K) (v : V) (m : FMap K V) (h : k ≠ k') :
    find k' (add k v m) = find k' m := by
  have hne : compare k k' ≠ Ordering.eq := fun he => h ((cmp_eq_iff _ _).mp he)
  simp [find, lookup, add, Std.ExtTreeMap.getElem?_insert, hne]

theorem find_partial_alter (k : K) (f : Option V → Option V) (m : FMap K V) :
    find k (partial_alter f k m) = f (find k m) := by
  simp [find, lookup, partial_alter]

theorem find_partial_alter_ne (k k' : K) (f : Option V → Option V) (m : FMap K V)
    (h : k ≠ k') : find k' (partial_alter f k m) = find k' m := by
  have hne : compare k k' ≠ Ordering.eq := fun he => h ((cmp_eq_iff _ _).mp he)
  simp [find, lookup, partial_alter, Std.ExtTreeMap.getElem?_alter, hne]

theorem find_remove (k : K) (m : FMap K V) : find k (remove k m) = none := by
  simp [find, lookup, remove]

theorem find_remove_ne (k k' : K) (m : FMap K V) (h : k ≠ k') :
    find k' (remove k m) = find k' m := by
  have hne : compare k k' ≠ Ordering.eq := fun he => h ((cmp_eq_iff _ _).mp he)
  simp [find, lookup, remove, Std.ExtTreeMap.getElem?_erase, hne]

theorem elements_empty : (elements (empty : FMap K V)) = [] := by
  -- toList_eq_nil_iff : t.toList = [] ↔ t = ∅
  exact (Std.ExtTreeMap.toList_eq_nil_iff).mpr rfl

theorem extEq_iff_eq (m1 m2 : FMap K V) : extEq m1 m2 ↔ m1 = m2 := by
  refine ⟨fun h => ?_, fun h _ => by rw [h]⟩
  exact Std.ExtTreeMap.ext_getElem? h

theorem ext_eq (m1 m2 : FMap K V) :
    (∀ k, find k m1 = find k m2) → m1 = m2 :=
  (extEq_iff_eq m1 m2).mp

theorem add_add (k : K) (v v' : V) (m : FMap K V) :
    add k v (add k v' m) = add k v m := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k'
  by_cases h : k = k'
  · subst h
    simp [add]
  · have hne : compare k k' ≠ Ordering.eq := fun he => h ((cmp_eq_iff _ _).mp he)
    simp [add, Std.ExtTreeMap.getElem?_insert, hne]

theorem add_commute (k k' : K) (v v' : V) (m : FMap K V) (h : k ≠ k') :
    add k v (add k' v' m) = add k' v' (add k v m) := by
  apply Std.ExtTreeMap.ext_getElem?
  intro x
  show (Std.ExtTreeMap.insert (Std.ExtTreeMap.insert m k' v') k v)[x]? =
       (Std.ExtTreeMap.insert (Std.ExtTreeMap.insert m k v) k' v')[x]?
  rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_insert,
      Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_insert]
  by_cases hk : compare k x = Ordering.eq
  · by_cases hk' : compare k' x = Ordering.eq
    · exfalso
      exact h ((cmp_eq_iff _ _).mp hk |>.trans ((cmp_eq_iff _ _).mp hk').symm)
    · simp [hk, hk']
  · simp [hk]

theorem add_remove (k : K) (v : V) (m : FMap K V) :
    add k v (remove k m) = add k v m := by
  apply Std.ExtTreeMap.ext_getElem?
  intro x
  by_cases h : k = x
  · subst h
    simp [add, remove]
  · have hne : compare k x ≠ Ordering.eq := fun he => h ((cmp_eq_iff _ _).mp he)
    simp [add, remove, Std.ExtTreeMap.getElem?_insert,
          Std.ExtTreeMap.getElem?_erase, hne]

theorem remove_add (k : K) (v : V) (m : FMap K V) (h : find k m = none) :
    remove k (add k v m) = m := by
  apply Std.ExtTreeMap.ext_getElem?
  intro x
  by_cases hx : k = x
  · subst hx
    simp [find, lookup] at h
    simp [add, remove, h]
  · have hne : compare k x ≠ Ordering.eq := fun he => hx ((cmp_eq_iff _ _).mp he)
    simp [add, remove, Std.ExtTreeMap.getElem?_erase,
          Std.ExtTreeMap.getElem?_insert, hne]

theorem add_id (k : K) (v : V) (m : FMap K V) (h : find k m = some v) :
    add k v m = m := by
  apply Std.ExtTreeMap.ext_getElem?
  intro x
  by_cases hx : k = x
  · subst hx
    simp [find, lookup] at h
    simp [add, h]
  · have hne : compare k x ≠ Ordering.eq := fun he => hx ((cmp_eq_iff _ _).mp he)
    simp [add, Std.ExtTreeMap.getElem?_insert, hne]

theorem remove_empty (k : K) : remove k (empty : FMap K V) = (empty : FMap K V) := by
  simp [remove, empty, Std.ExtTreeMap.erase_empty]

theorem size_empty : size (empty : FMap K V) = 0 := by
  simp [size, empty, Std.ExtTreeMap.size_empty]

theorem size_add_new (k : K) (v : V) (m : FMap K V) (h : find k m = none) :
    size (add k v m) = size m + 1 := by
  have hg : (m : Std.ExtTreeMap K V compare)[k]? = none := h
  have hc : (m : Std.ExtTreeMap K V compare).contains k = false := by
    rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, hg]; rfl
  simp [size, add, Std.ExtTreeMap.size_insert, hc]

theorem size_add_existing (k : K) (v : V) (m : FMap K V) (h : find k m ≠ none) :
    size (add k v m) = size m := by
  have hg : (m : Std.ExtTreeMap K V compare)[k]? ≠ none := h
  have hc : (m : Std.ExtTreeMap K V compare).contains k = true := by
    rw [Std.ExtTreeMap.contains_eq_isSome_getElem?]
    cases hk : (m : Std.ExtTreeMap K V compare)[k]? with
    | none => exact (hg hk).elim
    | some _ => rfl
  simp [size, add, Std.ExtTreeMap.size_insert, hc]

theorem length_elements (m : FMap K V) : (elements m).length = size m := by
  simp [elements, size, Std.ExtTreeMap.length_toList]

theorem In_elements (k : K) (v : V) (m : FMap K V) :
    (k, v) ∈ elements m ↔ find k m = some v := by
  exact Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some

theorem not_In_elements (k : K) (m : FMap K V) :
    (∀ v, (k, v) ∉ elements m) ↔ find k m = none := by
  constructor
  · intro h
    cases hk : find k m with
    | none => rfl
    | some v => exact absurd ((In_elements k v m).mpr hk) (h v)
  · intro hnone v hmem
    rw [In_elements] at hmem
    rw [hmem] at hnone
    cases hnone

theorem NoDup_elements (m : FMap K V) : List.Nodup (elements m) := by
  -- distinct_keys_toList gives pairwise distinct keys; project to (k,v) distinctness
  have hp := Std.ExtTreeMap.distinct_keys_toList (t := m)
  refine hp.imp (fun {a b} hab habeq => ?_)
  apply hab
  have : a.fst = b.fst := by rw [habeq]
  rw [this]; exact cmp_self _

private theorem nodup_map_fst_of_pairwise {α β : Type _} (l : List (α × β))
    (h : List.Pairwise (fun a b => a.fst ≠ b.fst) l) :
    (l.map Prod.fst).Nodup := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons]
    cases h with
    | cons hhd htl =>
      refine ⟨?_, ih htl⟩
      intro hin
      obtain ⟨⟨a, b⟩, hin', habeq⟩ := List.mem_map.mp hin
      simp only at habeq
      exact hhd _ hin' habeq.symm

theorem NoDup_keys (m : FMap K V) : List.Nodup (keys m) := by
  unfold keys elements
  apply nodup_map_fst_of_pairwise
  have hp := Std.ExtTreeMap.distinct_keys_toList (t := m)
  refine hp.imp ?_
  intro a b hab heq
  apply hab
  rw [heq]; exact cmp_self _

theorem find_update_eq (key1 : K) (n : Option V) (map : FMap K V) :
    find key1 (update key1 n map) = n := by
  cases n with
  | none => simp [update]; exact find_remove key1 map
  | some v => simp [update]; exact find_add key1 v map

theorem find_update_ne (key1 key2 : K) (n : Option V) (map : FMap K V)
    (h : key1 ≠ key2) : find key1 (update key2 n map) = find key1 map := by
  cases n with
  | none => simp [update]; exact find_remove_ne key2 key1 map (Ne.symm h)
  | some v => simp [update]; exact find_add_ne key2 key1 v map (Ne.symm h)

theorem map_update_idemp (key : K) (n m : Option V) (map : FMap K V) :
    update key n (update key m map) = update key n map := by
  apply (extEq_iff_eq _ _).mp
  intro k
  by_cases h : key = k
  · subst h; rw [find_update_eq, find_update_eq]
  · rw [find_update_ne _ _ _ _ (Ne.symm h),
        find_update_ne _ _ _ _ (Ne.symm h),
        find_update_ne _ _ _ _ (Ne.symm h)]

/-! ### Permutation lemmas and induction principle.

    These rely on `List.Perm` extensionality (`perm_ext_iff_of_nodup`)
    and the `ofList`/`getElem?` API of `ExtTreeMap`. The
    `(t : ExtTreeMap ...).contains_ofList` family also requires a `BEq K` /
    `LawfulBEq K` / `LawfulBEqCmp compare` bridge derived from the
    `LawfulEqCmp` part of `LawfulOrd`; local instances provide that bridge. -/

local instance beqOfOrd : BEq K := ⟨fun a b => decide (compare a b = .eq)⟩

local instance reflBEqOfOrd : ReflBEq K := ⟨by
  intro a
  show decide (compare a a = .eq) = true
  simp⟩

local instance lawfulBEqOfOrd : LawfulBEq K := ⟨by
  intro a b h
  have hd : decide (compare a b = .eq) = true := h
  exact (cmp_eq_iff _ _).mp (of_decide_eq_true hd)⟩

local instance lawfulBEqCmpOfOrd : Std.LawfulBEqCmp (α := K) compare := ⟨by
  intro a b
  show compare a b = .eq ↔ (decide (compare a b = .eq)) = true
  simp⟩

private theorem find_eq_getElem? (k : K) (m : FMap K V) :
    find k m = (m : Std.ExtTreeMap K V compare)[k]? :=
  Std.ExtTreeMap.get?_eq_getElem?

theorem of_elements_eq (m : FMap K V) : of_list (elements m) = m := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  show (Std.ExtTreeMap.ofList (Std.ExtTreeMap.toList m) compare)[k]? = m[k]?
  cases hm : m[k]? with
  | some v =>
    have hmem : (k, v) ∈ (m : Std.ExtTreeMap K V compare).toList :=
      Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hm
    exact Std.ExtTreeMap.getElem?_ofList_of_mem (cmp_self k)
      (Std.ExtTreeMap.distinct_keys_toList) hmem
  | none =>
    have hkmiss : ((m : Std.ExtTreeMap K V compare).toList.map Prod.fst).contains k = false := by
      rw [List.contains_eq_mem]
      simp only [decide_eq_false_iff_not]
      intro hin
      obtain ⟨⟨k', v'⟩, hin', hkeq⟩ := List.mem_map.mp hin
      cases hkeq
      have hgs : (m : Std.ExtTreeMap K V compare)[k']? = some v' :=
        Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hin'
      rw [hgs] at hm; cases hm
    exact Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false hkmiss

theorem of_list_elements (m : FMap K V) : of_list (elements m) = m :=
  of_elements_eq m

theorem elements_of_list (l : List (K × V)) (hn : List.Nodup (l.map Prod.fst)) :
    List.Perm (elements (of_list l)) l := by
  have hL : (elements (of_list l)).Nodup := NoDup_elements _
  have hR : l.Nodup := List.Nodup.of_map _ hn
  rw [List.perm_ext_iff_of_nodup hL hR]
  have hpair : List.Pairwise (fun a b : K × V => ¬ compare a.fst b.fst = .eq) l := by
    have h1 : List.Pairwise (fun a b : K × V => a.fst ≠ b.fst) l :=
      List.pairwise_map.mp hn
    exact h1.imp (fun {a b} hab he => hab ((cmp_eq_iff _ _).mp he))
  intro ⟨k, v⟩
  show (k, v) ∈ Std.ExtTreeMap.toList (Std.ExtTreeMap.ofList l compare) ↔ (k, v) ∈ l
  rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
  refine ⟨?_, ?_⟩
  · intro hg
    have hcontain : (Std.ExtTreeMap.ofList l compare).contains k = true := by
      rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, hg]; rfl
    rw [Std.ExtTreeMap.contains_ofList, List.contains_eq_mem] at hcontain
    have hk_in : k ∈ l.map Prod.fst := of_decide_eq_true hcontain
    obtain ⟨⟨k', v'⟩, hin, heq⟩ := List.mem_map.mp hk_in
    cases heq
    have hg' : (Std.ExtTreeMap.ofList l compare)[k']? = some v' :=
      Std.ExtTreeMap.getElem?_ofList_of_mem (cmp_self k') hpair hin
    rw [hg] at hg'
    cases hg'
    exact hin
  · intro hin
    exact Std.ExtTreeMap.getElem?_ofList_of_mem (cmp_self k) hpair hin

theorem elements_add (k : K) (v : V) (m : FMap K V) (h : find k m = none) :
    List.Perm (elements (add k v m)) ((k, v) :: elements m) := by
  rw [find_eq_getElem?] at h
  have hL : (elements (add k v m)).Nodup := NoDup_elements _
  have hRtail : (elements m).Nodup := NoDup_elements _
  have hR : ((k, v) :: elements m).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, hRtail⟩
    intro hin
    have hin' : (k, v) ∈ (m : Std.ExtTreeMap K V compare).toList := hin
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at hin'
    rw [hin'] at h; cases h
  rw [List.perm_ext_iff_of_nodup hL hR]
  intro ⟨k', v'⟩
  show (k', v') ∈ Std.ExtTreeMap.toList (Std.ExtTreeMap.insert m k v) ↔
       (k', v') ∈ (k, v) :: Std.ExtTreeMap.toList m
  rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, List.mem_cons,
      Std.ExtTreeMap.getElem?_insert]
  by_cases hk : compare k k' = .eq
  · have hkeq : k = k' := (cmp_eq_iff _ _).mp hk
    subst hkeq
    rw [if_pos hk]
    refine ⟨?_, ?_⟩
    · intro hv'; cases hv'; exact Or.inl rfl
    · rintro (heq | hin)
      · cases heq; rfl
      · rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some] at hin
        rw [hin] at h; cases h
  · rw [if_neg hk]
    refine ⟨?_, ?_⟩
    · intro hm
      exact Or.inr (Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mpr hm)
    · rintro (heq | hin)
      · cases heq; exfalso; exact hk (cmp_self _)
      · exact Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hin

theorem elements_add_existing (k : K) (vold vnew : V) (m : FMap K V)
    (_h : find k m = some vold) :
    List.Perm (elements (add k vnew m)) ((k, vnew) :: elements (remove k m)) := by
  have hL : (elements (add k vnew m)).Nodup := NoDup_elements _
  have hRtail : (elements (remove k m)).Nodup := NoDup_elements _
  have hR : ((k, vnew) :: elements (remove k m)).Nodup := by
    rw [List.nodup_cons]
    refine ⟨?_, hRtail⟩
    intro hin
    have hin' : (k, vnew) ∈ (Std.ExtTreeMap.erase m k).toList := hin
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
        Std.ExtTreeMap.getElem?_erase, if_pos (cmp_self k)] at hin'
    cases hin'
  rw [List.perm_ext_iff_of_nodup hL hR]
  intro ⟨k', v'⟩
  show (k', v') ∈ Std.ExtTreeMap.toList (Std.ExtTreeMap.insert m k vnew) ↔
       (k', v') ∈ (k, vnew) :: Std.ExtTreeMap.toList (Std.ExtTreeMap.erase m k)
  rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some, List.mem_cons,
      Std.ExtTreeMap.getElem?_insert]
  by_cases hk : compare k k' = .eq
  · have hkeq : k = k' := (cmp_eq_iff _ _).mp hk
    subst hkeq
    rw [if_pos hk]
    refine ⟨?_, ?_⟩
    · intro hv'; cases hv'; exact Or.inl rfl
    · rintro (heq | hin)
      · cases heq; rfl
      · rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
            Std.ExtTreeMap.getElem?_erase, if_pos hk] at hin
        cases hin
  · rw [if_neg hk]
    refine ⟨?_, ?_⟩
    · intro hm
      refine Or.inr ?_
      rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
          Std.ExtTreeMap.getElem?_erase, if_neg hk]
      exact hm
    · rintro (heq | hin)
      · cases heq; exfalso; exact hk (cmp_self _)
      · rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some,
            Std.ExtTreeMap.getElem?_erase, if_neg hk] at hin
        exact hin

theorem keys_already (k : K) (v v' : V) (m : FMap K V)
    (h : find k m = some v) : List.Perm (keys (add k v' m)) (keys m) := by
  -- elements (add k v' m) ~ (k, v') :: elements (remove k m)
  -- elements m ~ (k, v) :: elements (remove k m)
  have hAdd := elements_add_existing k v v' m h
  have hRem : List.Perm (elements m) ((k, v) :: elements (remove k m)) := by
    -- elements m = elements (add k v (remove k m)) (since add k v after remove k restores)
    have hRemNone : find k (remove k m) = none := find_remove k m
    have hAddRem : add k v (remove k m) = m := by
      apply Std.ExtTreeMap.ext_getElem?
      intro x
      by_cases hx : k = x
      · subst hx
        show (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k v)[k]? = m[k]?
        rw [Std.ExtTreeMap.getElem?_insert, if_pos (cmp_self k)]
        rw [find_eq_getElem?] at h
        exact h.symm
      · have hne : compare k x ≠ Ordering.eq := fun he => hx ((cmp_eq_iff _ _).mp he)
        show (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k v)[x]? = m[x]?
        rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase,
            if_neg hne, if_neg hne]
    have := elements_add k v (remove k m) hRemNone
    rw [hAddRem] at this
    exact this
  -- Combine: elements (add k v' m) ~ (k,v') :: elements (remove k m)
  --          elements m ~ (k, v) :: elements (remove k m)
  -- For keys: map fst preserves Perm
  unfold keys
  have h1 := hAdd.map Prod.fst
  have h2 := hRem.map Prod.fst
  -- h1 : keys (add k v' m) ~ (k :: keys (remove k m))
  -- h2 : keys m ~ (k :: keys (remove k m))
  exact h1.trans h2.symm

theorem ind (P : FMap K V → Prop)
    (h0 : P empty)
    (hstep : ∀ k v m, find k m = none → P m → P (add k v m))
    (m : FMap K V) : P m := by
  -- strong induction on size m
  suffices hsuf : ∀ n (m : FMap K V), size m = n → P m by exact hsuf _ m rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m hsz
    by_cases hn : n = 0
    · subst hn
      have hempty : m = empty := by
        have : (m : Std.ExtTreeMap K V compare).size = 0 := hsz
        exact Std.ExtTreeMap.eq_empty_iff_size_eq_zero.mpr this
      rw [hempty]; exact h0
    · -- size m > 0, extract a key
      have hpos : 0 < size m := by
        rw [hsz]; exact Nat.pos_of_ne_zero hn
      -- toList is nonempty
      have htl_ne : (m : Std.ExtTreeMap K V compare).toList ≠ [] := by
        intro he
        rw [Std.ExtTreeMap.toList_eq_nil_iff] at he
        have : size m = 0 := by
          show (m : Std.ExtTreeMap K V compare).size = 0
          rw [he]; exact Std.ExtTreeMap.size_empty
        omega
      -- Get head
      match hl : (m : Std.ExtTreeMap K V compare).toList with
      | [] => exact (htl_ne hl).elim
      | (k, v) :: tl =>
        have hmem : (k, v) ∈ (m : Std.ExtTreeMap K V compare).toList := by
          rw [hl]; exact List.mem_cons_self
        have hfind : (m : Std.ExtTreeMap K V compare)[k]? = some v :=
          Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hmem
        have hfind' : find k m = some v := by rw [find_eq_getElem?]; exact hfind
        -- m = add k v (remove k m)
        have hAddRem : add k v (remove k m) = m := by
          apply Std.ExtTreeMap.ext_getElem?
          intro x
          by_cases hx : k = x
          · subst hx
            show (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k v)[k]? = m[k]?
            rw [Std.ExtTreeMap.getElem?_insert, if_pos (cmp_self k)]
            exact hfind.symm
          · have hne : compare k x ≠ Ordering.eq := fun he => hx ((cmp_eq_iff _ _).mp he)
            show (Std.ExtTreeMap.insert (Std.ExtTreeMap.erase m k) k v)[x]? = m[x]?
            rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase,
                if_neg hne, if_neg hne]
        -- size (remove k m) < size m
        have hcontains : (m : Std.ExtTreeMap K V compare).contains k = true := by
          rw [Std.ExtTreeMap.contains_eq_isSome_getElem?, hfind]; rfl
        have hszRem : size (remove k m) < n := by
          show (Std.ExtTreeMap.erase m k).size < n
          rw [Std.ExtTreeMap.size_erase, if_pos hcontains]
          show (m : Std.ExtTreeMap K V compare).size - 1 < n
          have heq : (m : Std.ExtTreeMap K V compare).size = n := hsz
          rw [heq]
          exact Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos
        have hPrem : P (remove k m) := ih _ hszRem (remove k m) rfl
        have hRemNone : find k (remove k m) = none := find_remove k m
        have := hstep k v (remove k m) hRemNone hPrem
        rw [hAddRem] at this
        exact this

end FMap

end ConCert.Execution.Containers
