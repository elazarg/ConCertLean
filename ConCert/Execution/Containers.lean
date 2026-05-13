/- Port of execution/theories/Containers.v.

   `FMap` is backed by `Std.ExtTreeMap` (quotient-extensional ordered
   tree map): two maps with the same `find` view are propositionally
   equal. `Std.TreeMap` would not work — it exposes tree shape, so
   distinct insertion orders give distinct values. -/

import Std.Data.ExtTreeMap

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

/-! ### Algebraic facts.

    Axiomatized; derivable from `ExtTreeMap`'s lemma library
    (`getElem?_insert`, `getElem?_erase`, `ext_getElem?`, `toList_inj`). -/

axiom of_elements_eq : ∀ (m : FMap K V), of_list (elements m) = m
axiom of_list_elements : ∀ (m : FMap K V), of_list (elements m) = m

axiom elements_of_list :
  ∀ (l : List (K × V)),
    List.Nodup (l.map Prod.fst) → List.Perm (elements (of_list l)) l

axiom find_add :
  ∀ (k : K) (v : V) (m : FMap K V), find k (add k v m) = some v

axiom find_add_ne :
  ∀ (k k' : K) (v : V) (m : FMap K V),
    k ≠ k' → find k' (add k v m) = find k' m

axiom find_partial_alter :
  ∀ (k : K) (f : Option V → Option V) (m : FMap K V),
    find k (partial_alter f k m) = f (find k m)

axiom find_partial_alter_ne :
  ∀ (k k' : K) (f : Option V → Option V) (m : FMap K V),
    k ≠ k' → find k' (partial_alter f k m) = find k' m

axiom find_empty :
  ∀ (k : K), find k (empty : FMap K V) = none

axiom elements_add :
  ∀ (k : K) (v : V) (m : FMap K V),
    find k m = none →
    List.Perm (elements (add k v m)) ((k, v) :: elements m)

axiom elements_empty : (elements (empty : FMap K V)) = []

axiom add_remove :
  ∀ (k : K) (v : V) (m : FMap K V), add k v (remove k m) = add k v m

axiom add_add :
  ∀ (k : K) (v v' : V) (m : FMap K V), add k v (add k v' m) = add k v m

axiom remove_add :
  ∀ (k : K) (v : V) (m : FMap K V),
    find k m = none → remove k (add k v m) = m

axiom find_remove : ∀ (k : K) (m : FMap K V), find k (remove k m) = none

axiom find_remove_ne :
  ∀ (k k' : K) (m : FMap K V), k ≠ k' → find k' (remove k m) = find k' m

axiom add_commute :
  ∀ (k k' : K) (v v' : V) (m : FMap K V),
    k ≠ k' → add k v (add k' v' m) = add k' v' (add k v m)

axiom add_id :
  ∀ (k : K) (v : V) (m : FMap K V), find k m = some v → add k v m = m

axiom remove_empty :
  ∀ (k : K), remove k (empty : FMap K V) = (empty : FMap K V)

axiom keys_already :
  ∀ (k : K) (v v' : V) (m : FMap K V),
    find k m = some v → List.Perm (keys (add k v' m)) (keys m)

axiom ind :
  ∀ (P : FMap K V → Prop),
    P empty →
    (∀ k v m, find k m = none → P m → P (add k v m)) →
    ∀ m, P m

axiom size_empty : size (empty : FMap K V) = 0

axiom size_add_new :
  ∀ (k : K) (v : V) (m : FMap K V),
    find k m = none → size (add k v m) = size m + 1

axiom size_add_existing :
  ∀ (k : K) (v : V) (m : FMap K V),
    find k m ≠ none → size (add k v m) = size m

axiom length_elements : ∀ (m : FMap K V), (elements m).length = size m

axiom In_elements :
  ∀ (k : K) (v : V) (m : FMap K V),
    (k, v) ∈ elements m ↔ find k m = some v

axiom elements_add_existing :
  ∀ (k : K) (vold vnew : V) (m : FMap K V),
    find k m = some vold →
    List.Perm (elements (add k vnew m)) ((k, vnew) :: elements (remove k m))

axiom not_In_elements :
  ∀ (k : K) (m : FMap K V),
    (∀ v, (k, v) ∉ elements m) ↔ find k m = none

axiom NoDup_elements : ∀ (m : FMap K V), List.Nodup (elements m)

axiom NoDup_keys : ∀ (m : FMap K V), List.Nodup (keys m)

axiom map_update_idemp :
  ∀ (key : K) (n m : Option V) (map : FMap K V),
    update key n (update key m map) = update key n map

axiom find_update_ne :
  ∀ (key1 key2 : K) (n : Option V) (map : FMap K V),
    key1 ≠ key2 → find key1 (update key2 n map) = find key1 map

axiom find_update_eq :
  ∀ (key1 : K) (n : Option V) (map : FMap K V),
    find key1 (update key1 n map) = n

/-- Extensional equality coincides with structural equality on
    `ExtTreeMap`. Derivable from `Std.ExtTreeMap.ext_getElem?`. -/
axiom extEq_iff_eq (m1 m2 : FMap K V) : extEq m1 m2 ↔ m1 = m2

end FMap

end ConCert.Execution.Containers
