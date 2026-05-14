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

infixl:65 " # " => lookup

syntax:65 term:66 " # " "[" term " ~> " term "]" : term
macro_rules
  | `($ρ:term # [ $k:term ~> $v:term ]) => `(($k, $v) :: $ρ)

def remove_by_key {A : Type} (key : String) : Env A → Env A
  | [] => []
  | (nm, a) :: ρ' =>
    if nm == key then remove_by_key key ρ' else (nm, a) :: remove_by_key key ρ'

-- The Rocq lemma is a `{e | lookup_i ρ n = Some e}`-typed witness.
-- Lean states and proves the corresponding existential.
theorem lookup_i_length {A : Type} (ρ : Env A) (n : Nat) :
    (n < ρ.length) → ∃ e, lookup_i ρ n = some e := by
  induction ρ generalizing n with
  | nil => intro h; simp at h
  | cons hd tl ih =>
    intro h
    cases n with
    | zero =>
      obtain ⟨nm, a⟩ := hd
      exact ⟨a, by simp [lookup_i]⟩
    | succ k =>
      obtain ⟨nm, a⟩ := hd
      have hk : k < tl.length := by
        simp [List.length] at h; omega
      obtain ⟨e, he⟩ := ih k hk
      refine ⟨e, ?_⟩
      simp [lookup_i, he]

theorem lookup_i_length_false {A : Type} (ρ : Env A) (n : Nat) :
    ¬ (n < ρ.length) → lookup_i ρ n = none := by
  induction ρ generalizing n with
  | nil => intro _; cases n <;> rfl
  | cons hd tl ih =>
    intro h
    cases n with
    | zero =>
      exfalso
      apply h
      simp [List.length]
    | succ k =>
      obtain ⟨nm, a⟩ := hd
      have hk : ¬ k < tl.length := by
        intro hk; apply h; simp [List.length]; omega
      simp [lookup_i, ih k hk]

end ConCert.Utils.Env
