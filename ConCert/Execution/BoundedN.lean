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

axiom to_N_inj :
  ∀ {bound : Nat} {a b : BoundedN bound}, to_N a = to_N b → a = b

axiom eqb_refl :
  ∀ {bound : Nat} (n : BoundedN bound), eqb n n = true

axiom to_nat_inj :
  ∀ {bound : Nat} (a b : BoundedN bound), to_nat a = to_nat b → a = b

axiom to_Z_inj :
  ∀ {bound : Nat} (a b : BoundedN bound), to_Z a = to_Z b → a = b

axiom of_to_N :
  ∀ {bound : Nat} (n : BoundedN bound), of_N (to_N n) = some n

axiom of_to_nat :
  ∀ {bound : Nat} (n : BoundedN bound), of_nat (to_nat n) = some n

axiom of_to_Z :
  ∀ {bound : Nat} (n : BoundedN bound), of_Z (to_Z n) = some n

axiom of_N_some :
  ∀ {bound : Nat} {m : Nat} {n : BoundedN bound},
    of_N m = some n → to_N n = m

axiom of_N_none :
  ∀ {bound : Nat} {m : Nat}, @of_N bound m = none → bound ≤ m

axiom of_nat_some :
  ∀ {bound : Nat} {m : Nat} {n : BoundedN bound},
    of_nat m = some n → to_nat n = m

axiom of_nat_none :
  ∀ {bound : Nat} {m : Nat}, @of_nat bound m = none → bound ≤ m

axiom in_map_of_nat :
  ∀ (bound : Nat) (n : BoundedN bound) (xs : List Nat),
    n ∈ ConCert.Utils.Extras.mapOption (@of_nat bound) xs ↔ to_nat n ∈ xs

def bounded_elements (bound : Nat) : List (BoundedN bound) :=
  ConCert.Utils.Extras.mapOption of_nat (List.range bound)

axiom bounded_elements_set :
  ∀ (bound : Nat), List.Nodup (bounded_elements bound)

axiom bounded_elements_all :
  ∀ (bound : Nat) (a : BoundedN bound), a ∈ bounded_elements bound

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
