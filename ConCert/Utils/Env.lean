/- Port of utils/theories/Env.v -/

import ConCert.Utils.Automation

namespace ConCert.Utils.Env

abbrev Env (A : Type) := List (String × A)

def lookup {A : Type} : Env A → String → Option A
  | [], _ => none
  | (nm, a) :: ρ', key =>
    if nm == key then some a else lookup ρ' key

def lookup_with_ind_rec {A : Type} : Nat → Env A → String → Option (Nat × A)
  | _, [], _ => none
  | i, (nm, a) :: ρ', key =>
    if nm == key then some (i, a) else lookup_with_ind_rec (1 + i) ρ' key

def lookup_with_ind {A : Type} (ρ : Env A) (key : String) : Option (Nat × A) :=
  lookup_with_ind_rec 0 ρ key

def lookup_i {A : Type} : Env A → Nat → Option A
  | [], _ => none
  | (_, a) :: ρ', i =>
    if i == 0 then some a else lookup_i ρ' (i - 1)

-- TODO: port notations `ρ # (k)` and `ρ # [ k ~> v ]`.

def remove_by_key {A : Type} (key : String) : Env A → Env A
  | [] => []
  | (nm, a) :: ρ' =>
    if nm == key then remove_by_key key ρ' else (nm, a) :: remove_by_key key ρ'

-- Lemma lookup_i_length is a {e | lookup_i ρ n = Some e}-typed sig.
-- Stated as an existence axiom here.
axiom lookup_i_length {A : Type} (ρ : Env A) (n : Nat) :
  (n < ρ.length) → ∃ e, lookup_i ρ n = some e

axiom lookup_i_length_false {A : Type} (ρ : Env A) (n : Nat) :
  ¬ (n < ρ.length) → lookup_i ρ n = none

end ConCert.Utils.Env
