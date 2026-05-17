/- Mathlib-backed replacement for examples/boardroomVoting/Euler.v. -/

import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic

namespace ConCert.Examples.BoardroomVoting

def rel_primes (n : Nat) : Finset Nat :=
  (Finset.range n).filter fun k => n.Coprime k

def totient (n : Nat) : Nat :=
  (rel_primes n).card

theorem mem_relPrimes {k n : Nat} :
    k ∈ rel_primes n ↔ k < n ∧ n.Coprime k := by
  simp [rel_primes]

theorem totient_eq_nat_totient (n : Nat) :
    totient n = Nat.totient n := by
  rfl

theorem euler {a n : Nat} (hcoprime : Nat.Coprime a n) :
    a ^ totient n ≡ 1 [MOD n] := by
  simpa [totient_eq_nat_totient] using Nat.ModEq.pow_totient hcoprime

theorem prime_totient {p : Nat} (hp : p.Prime) :
    totient p = p - 1 := by
  simpa [totient_eq_nat_totient] using Nat.totient_prime hp

theorem fermatNat {a p : Nat} (hp : p.Prime)
    (hcoprime : Nat.Coprime a p) :
    a ^ (p - 1) ≡ 1 [MOD p] :=
  Nat.ModEq.pow_card_sub_one_eq_one hp hcoprime

theorem fermat {p : Nat} (hp : p.Prime) {a : Int}
    (hcoprime : IsCoprime a (p : Int)) :
    a ^ (p - 1) ≡ 1 [ZMOD (p : Int)] :=
  Int.ModEq.pow_card_sub_one_eq_one hp hcoprime

theorem fermatOfModNeZero {p : Nat} (hp : p.Prime) {a : Int}
    (ha : a % (p : Int) ≠ 0) :
    a ^ (p - 1) % (p : Int) = 1 % (p : Int) := by
  have hnot_dvd : ¬ (p : Int) ∣ a := by
    intro hdiv
    exact ha (Int.dvd_iff_emod_eq_zero.mp hdiv)
  have hcoprime : IsCoprime a (p : Int) :=
    ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hnot_dvd).symm
  exact (fermat hp hcoprime).eq

end ConCert.Examples.BoardroomVoting
