/-
An exact arithmetic witness for the singularity of the accelerated Syracuse map.

The lift `n ↦ 4*n+1` adds two bits to the valuation of `3*n+1` while
preserving the accelerated output. Thus two output fibers can approach the
2-adic point `-1/3` to arbitrary precision without their outputs merging.
This module makes the finite-precision assertion over natural numbers; it
does not use a topological continuity claim.
-/

import CollatzShadowing.CollatzBridge

namespace CollatzShadowing

/-- Repeated inverse lift along the same accelerated Syracuse output. -/
def singularLift (seed : ℕ) : ℕ → ℕ
  | 0 => seed
  | k + 1 => 4 * singularLift seed k + 1

/-- Each lift multiplies the Syracuse numerator by four. -/
theorem singularLift_numerator (seed k : ℕ) :
    syracuseNumerator (singularLift seed k) =
      4 ^ k * syracuseNumerator seed := by
  induction k with
  | zero => simp [singularLift]
  | succ k ih =>
      calc
        syracuseNumerator (singularLift seed (k + 1))
            = 4 * syracuseNumerator (singularLift seed k) := by
                simp only [singularLift, syracuseNumerator]
                ring
        _ = 4 * (4 ^ k * syracuseNumerator seed) := by rw [ih]
        _ = 4 ^ (k + 1) * syracuseNumerator seed := by
              rw [pow_succ]
              ring

/-- If the seed's odd Syracuse output is certified, every lift has the same
output and two more valuation bits per lift. -/
theorem singularLift_step_of_seed
    {seed a m : ℕ} (hnum : syracuseNumerator seed = 2 ^ a * m)
    (hm : Odd m) (k : ℕ) :
    syracuseExponent (singularLift seed k) = a + 2 * k
      ∧ S (singularLift seed k) = m := by
  apply syracuseStep_of_num_eq_two_pow_mul_odd (hodd := hm)
  rw [singularLift_numerator, hnum]
  rw [show a + 2 * k = 2 * k + a by omega, pow_add]
  have hfour : 4 ^ k = 2 ^ (2 * k) := by
    calc
      4 ^ k = (2 ^ 2 : ℕ) ^ k := by norm_num
      _ = 2 ^ (2 * k) := by rw [pow_mul]
  rw [hfour]
  ring

/-- Lifts of `1` have output `1` and unbounded numerator valuation. -/
theorem singularLift_one (k : ℕ) :
    syracuseExponent (singularLift 1 k) = 2 + 2 * k
      ∧ S (singularLift 1 k) = 1 := by
  exact singularLift_step_of_seed
    (seed := 1) (a := 2) (m := 1)
    (by norm_num [syracuseNumerator]) (by norm_num) k

/-- Lifts of `9` have output `7` and unbounded numerator valuation. -/
theorem singularLift_nine (k : ℕ) :
    syracuseExponent (singularLift 9 k) = 2 + 2 * k
      ∧ S (singularLift 9 k) = 7 := by
  exact singularLift_step_of_seed
    (seed := 9) (a := 2) (m := 7)
    (by norm_num [syracuseNumerator]) (by norm_num) k

/-- Every lift of a positive odd seed remains positive and odd. -/
theorem singularLift_pos_odd {seed : ℕ} (hpos : 0 < seed)
    (hodd : Odd seed) (k : ℕ) :
    0 < singularLift seed k ∧ Odd (singularLift seed k) := by
  induction k with
  | zero => simpa [singularLift] using And.intro hpos hodd
  | succ k _ =>
      constructor
      · simp [singularLift]
      · refine ⟨2 * singularLift seed k, ?_⟩
        simp only [singularLift]
        omega

/-- Arbitrarily precise positive odd inputs near the formal singular point
can have distinct accelerated outputs. The condition `2^R ∣ 3*n+1` is the
integer form of 2-adic proximity to `-1/3`, since `3` is a 2-adic unit. -/
theorem singular_outputs_separated_at_every_precision (R : ℕ) :
    ∃ n₁ n₇ : ℕ,
      0 < n₁ ∧ Odd n₁ ∧ 0 < n₇ ∧ Odd n₇
        ∧ 2 ^ R ∣ syracuseNumerator n₁
        ∧ 2 ^ R ∣ syracuseNumerator n₇
        ∧ S n₁ = 1 ∧ S n₇ = 7 := by
  refine ⟨singularLift 1 R, singularLift 9 R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (singularLift_pos_odd (by norm_num) (by norm_num) R).1
  · exact (singularLift_pos_odd (by norm_num) (by norm_num) R).2
  · exact (singularLift_pos_odd (by norm_num) (by norm_num) R).1
  · exact (singularLift_pos_odd (by norm_num) (by norm_num) R).2
  · rw [singularLift_numerator]
    refine ⟨4 * 2 ^ R, ?_⟩
    rw [show (4 : ℕ) ^ R = 2 ^ (2 * R) by
      calc
        4 ^ R = (2 ^ 2 : ℕ) ^ R := by norm_num
        _ = 2 ^ (2 * R) := by rw [pow_mul]]
    rw [show 2 * R = R + R by omega, pow_add]
    norm_num [syracuseNumerator]
    ring
  · rw [singularLift_numerator]
    refine ⟨28 * 2 ^ R, ?_⟩
    rw [show (4 : ℕ) ^ R = 2 ^ (2 * R) by
      calc
        4 ^ R = (2 ^ 2 : ℕ) ^ R := by norm_num
        _ = 2 ^ (2 * R) := by rw [pow_mul]]
    rw [show 2 * R = R + R by omega, pow_add]
    norm_num [syracuseNumerator]
    ring
  · exact (singularLift_one R).2
  · exact (singularLift_nine R).2

end CollatzShadowing
