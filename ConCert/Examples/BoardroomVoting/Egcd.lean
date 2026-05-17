/- Thin mathlib-backed replacement for examples/boardroomVoting/Egcd.v. -/

import Mathlib.Data.Int.GCD

namespace ConCert.Examples.BoardroomVoting

def egcd (m n : Int) : Int × Int :=
  (Int.gcdA m n, Int.gcdB m n)

theorem egcd_spec (m n : Int) :
    let (x, y) := egcd m n
    m * x + n * y = (m.gcd n : Int) := by
  simpa [egcd] using (Int.gcd_eq_gcd_ab m n).symm

theorem mul_fst_egcd {a n : Int}
    (hcoprime : a.gcd n = 1) :
    a * (egcd a n).1 % n = 1 % n := by
  have hbez := egcd_spec a n
  simp [egcd, hcoprime] at hbez
  have hax : a * Int.gcdA a n = 1 - n * Int.gcdB a n := by
    omega
  calc
    a * (egcd a n).1 % n
        = (1 - n * Int.gcdB a n) % n := by rw [egcd, hax]
    _ = (1 % n - (n * Int.gcdB a n) % n) % n := by
      rw [Int.sub_emod]
    _ = 1 % n := by
      rw [Int.mul_emod_right]
      simp

end ConCert.Examples.BoardroomVoting
