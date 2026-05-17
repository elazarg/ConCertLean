/- Abstract algebraic layer for examples/boardroomVoting/BoardroomMath.v. -/

import Mathlib.Data.List.Basic
import Mathlib.Tactic
import ConCert.Examples.BoardroomVoting.Euler

namespace ConCert.Examples.BoardroomVoting.BoardroomMath

universe u

class BoardroomAxioms (A : Type u) where
  elmeq : A → A → Prop
  elmeqb : A → A → Bool
  elmeqb_spec : ∀ {x y}, elmeqb x y = true ↔ elmeq x y
  zero : A
  one : A
  add : A → A → A
  mul : A → A → A
  opp : A → A
  inv : A → A
  pow : A → Int → A
  order : Int
  order_ge_two : 2 ≤ order
  elmeq_refl : ∀ a, elmeq a a
  elmeq_symm : ∀ {a b}, elmeq a b → elmeq b a
  elmeq_trans : ∀ {a b c}, elmeq a b → elmeq b c → elmeq a c
  one_nonzero : ¬ elmeq one zero
  mul_nonzero : ∀ {a b}, ¬ elmeq a zero → ¬ elmeq b zero →
    ¬ elmeq (mul a b) zero
  inv_nonzero : ∀ {a}, ¬ elmeq a zero → ¬ elmeq (inv a) zero
  pow_nonzero : ∀ {a e}, ¬ elmeq a zero → ¬ elmeq (pow a e) zero
  pow_zero : ∀ {a}, ¬ elmeq a zero → elmeq (pow a 0) one
  pow_one : ∀ a, elmeq (pow a 1) a
  pow_add : ∀ {a e e'}, ¬ elmeq a zero →
    elmeq (pow a (e + e')) (mul (pow a e) (pow a e'))
  pow_mul : ∀ {a e e'}, ¬ elmeq a zero →
    elmeq (pow (pow a e) e') (pow a (e * e'))

variable {A : Type u} [BoardroomAxioms A]

def nonzero (a : A) : Prop :=
  ¬ BoardroomAxioms.elmeq a BoardroomAxioms.zero

def expEq : Int → Int → Prop :=
  fun e e' =>
    e % (BoardroomAxioms.order (A := A) - 1) =
      e' % (BoardroomAxioms.order (A := A) - 1)

theorem elmeqb_eq_true {a b : A} :
    BoardroomAxioms.elmeqb a b = true ↔
      BoardroomAxioms.elmeq a b :=
  BoardroomAxioms.elmeqb_spec

theorem elmeqb_refl (a : A) :
    BoardroomAxioms.elmeqb a a = true :=
  elmeqb_eq_true.mpr (BoardroomAxioms.elmeq_refl a)

theorem elmeqb_eq_false {a b : A} :
    BoardroomAxioms.elmeqb a b = false ↔
      ¬ BoardroomAxioms.elmeq a b := by
  constructor
  · intro hfalse hEq
    have htrue := elmeqb_eq_true.mpr hEq
    simp [hfalse] at htrue
  · intro hnot
    cases h : BoardroomAxioms.elmeqb a b
    · rfl
    · exfalso
      exact hnot (elmeqb_eq_true.mp h)

theorem expEq_refl (e : Int) : expEq (A := A) e e := rfl

theorem expEq_symm {e e' : Int} :
    expEq (A := A) e e' → expEq (A := A) e' e :=
  Eq.symm

theorem expEq_trans {e₁ e₂ e₃ : Int} :
    expEq (A := A) e₁ e₂ →
      expEq (A := A) e₂ e₃ → expEq (A := A) e₁ e₃ :=
  Eq.trans

def expEqSetoid (A : Type u) [BoardroomAxioms A] : Setoid Int where
  r := expEq (A := A)
  iseqv := ⟨expEq_refl, @expEq_symm A _, @expEq_trans A _⟩

class Generator (A : Type u) [BoardroomAxioms A] where
  generator : A
  generator_nonzero : nonzero generator
  generator_generates :
    ∀ a, nonzero a →
      ∃! e : Int,
        0 ≤ e ∧ e < BoardroomAxioms.order (A := A) - 1 ∧
          BoardroomAxioms.elmeq (BoardroomAxioms.pow generator e) a

class DiscreteLog (A : Type u) [BoardroomAxioms A] [Generator A] where
  log : A → Int
  log_proper : ∀ {a b}, BoardroomAxioms.elmeq a b →
    expEq (A := A) (log a) (log b)
  pow_log : ∀ a, nonzero a →
    BoardroomAxioms.elmeq
      (BoardroomAxioms.pow (Generator.generator (A := A)) (log a)) a
  log_one : expEq (A := A) (log BoardroomAxioms.one) 0
  log_mul : ∀ {a b}, nonzero a → nonzero b →
    expEq (A := A) (log (BoardroomAxioms.mul a b)) (log a + log b)
  log_inv : ∀ a, expEq (A := A) (log (BoardroomAxioms.inv a)) (-(log a))
  log_generator : log (Generator.generator (A := A)) = 1

section AbstractProtocol

variable [Generator A]

def prod : List A → A
  | [] => BoardroomAxioms.one
  | x :: xs => BoardroomAxioms.mul x (prod xs)

def compute_public_key (sk : Int) : A :=
  BoardroomAxioms.pow (Generator.generator (A := A)) sk

def reconstructed_key (pks : List A) (n : Nat) : A :=
  let lprod := prod (pks.take n)
  let rprod := BoardroomAxioms.inv (prod (pks.drop (n + 1)))
  BoardroomAxioms.mul lprod rprod

def compute_public_vote (rk : A) (sk : Int) (sv : Bool) : A :=
  BoardroomAxioms.mul
    (BoardroomAxioms.pow rk sk)
    (if sv then Generator.generator (A := A) else BoardroomAxioms.one)

def bruteforce_tally_aux : Nat → A → Option Nat
  | n, votesProduct =>
      if BoardroomAxioms.elmeqb
          (BoardroomAxioms.pow (Generator.generator (A := A)) (Int.ofNat n))
          votesProduct then
        some n
      else
        match n with
        | 0 => none
        | n' + 1 => bruteforce_tally_aux n' votesProduct

def bruteforce_tally (votes : List A) : Option Nat :=
  bruteforce_tally_aux votes.length (prod votes)

theorem bruteforce_tally_aux_some_correct
    {n res : Nat} {votesProduct : A}
    (h : bruteforce_tally_aux (A := A) n votesProduct = some res) :
    res ≤ n ∧
      BoardroomAxioms.elmeqb
        (BoardroomAxioms.pow (Generator.generator (A := A)) (Int.ofNat res))
        votesProduct = true := by
  induction n with
  | zero =>
      unfold bruteforce_tally_aux at h
      split_ifs at h with hfound
      ·
        cases h
        exact ⟨Nat.le_refl 0, hfound⟩
  | succ n ih =>
      unfold bruteforce_tally_aux at h
      split_ifs at h with hfound
      ·
        cases h
        exact ⟨Nat.le_refl (n + 1), hfound⟩
      ·
        have hrec := ih h
        exact ⟨Nat.le_succ_of_le hrec.1, hrec.2⟩

theorem bruteforce_tally_some_correct
    {votes : List A} {res : Nat}
    (h : bruteforce_tally (A := A) votes = some res) :
    res ≤ votes.length ∧
      BoardroomAxioms.elmeqb
        (BoardroomAxioms.pow (Generator.generator (A := A)) (Int.ofNat res))
        (prod votes) = true := by
  exact bruteforce_tally_aux_some_correct (A := A) h

omit [BoardroomAxioms A] [Generator A] in
theorem forall_take {P : A → Prop} {xs : List A}
    (h : List.Forall P xs) (n : Nat) :
    List.Forall P (xs.take n) := by
  rw [List.forall_iff_forall_mem] at h ⊢
  intro x hx
  exact h x (List.mem_of_mem_take hx)

omit [BoardroomAxioms A] [Generator A] in
theorem forall_drop {P : A → Prop} {xs : List A}
    (h : List.Forall P xs) (n : Nat) :
    List.Forall P (xs.drop n) := by
  rw [List.forall_iff_forall_mem] at h ⊢
  intro x hx
  exact h x (List.mem_of_mem_drop hx)

omit [Generator A] in
theorem prod_nonzero_of_forall :
    ∀ {xs : List A}, List.Forall nonzero xs → nonzero (prod xs)
  | [], _ => by
      simpa [prod, nonzero] using
        (BoardroomAxioms.one_nonzero (A := A))
  | _ :: _, h => by
      rw [List.forall_cons] at h
      exact BoardroomAxioms.mul_nonzero h.1
        (prod_nonzero_of_forall h.2)

theorem compute_public_key_nonzero (sk : Int) :
    nonzero (compute_public_key (A := A) sk) :=
  BoardroomAxioms.pow_nonzero
    (Generator.generator_nonzero (A := A))

theorem compute_public_keys_nonzero (sks : List Int) :
    List.Forall nonzero (sks.map (compute_public_key (A := A))) := by
  induction sks with
  | nil => simp
  | cons sk sks ih =>
      simp [compute_public_key_nonzero sk, ih]

omit [Generator A] in
theorem reconstructed_key_nonzero {pks : List A} {i : Nat}
    (h : List.Forall nonzero pks) :
    nonzero (reconstructed_key (A := A) pks i) := by
  unfold reconstructed_key
  exact BoardroomAxioms.mul_nonzero
    (prod_nonzero_of_forall (forall_take h i))
    (BoardroomAxioms.inv_nonzero
      (prod_nonzero_of_forall (forall_drop h (i + 1))))

theorem compute_public_vote_nonzero {rk : A} {sk : Int} {sv : Bool}
    (hrk : nonzero rk) :
    nonzero (compute_public_vote (A := A) rk sk sv) := by
  unfold compute_public_vote
  exact BoardroomAxioms.mul_nonzero
    (BoardroomAxioms.pow_nonzero hrk)
    (by
      cases sv
      · simpa [nonzero] using (BoardroomAxioms.one_nonzero (A := A))
      · simpa [nonzero] using (Generator.generator_nonzero (A := A)))

end AbstractProtocol

end ConCert.Examples.BoardroomVoting.BoardroomMath
