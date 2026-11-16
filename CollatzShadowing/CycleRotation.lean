/-
Exact rotation identities for the affine constants of Syracuse words.
Divisibility tests at divisors of the cycle denominator are invariant under
rotation when the displayed coprimality conditions hold. These arithmetic
interfaces neither construct a cycle nor exclude every nontrivial cycle.

AI-assisted development: Codex with Piero Borgatta, 2026-11-13.
-/

import CollatzShadowing.CycleConstraints
import Mathlib.RingTheory.Coprime.Lemmas

namespace CollatzShadowing.CycleRotation

/-- Signed cycle denominator; no contractivity hypothesis is hidden. -/
def denominator (w : List ℕ) : ℤ :=
  (2 : ℤ) ^ w.sum - (3 : ℤ) ^ w.length

/-- Moving the initial exponent to the end preserves both denominator data. -/
theorem denominator_rotate (a : ℕ) (rest : List ℕ) :
    denominator (rest ++ [a]) = denominator (a :: rest) := by
  simp [denominator, Nat.add_comm]

/-- The exact affine constant identity, valid without positivity or closure. -/
theorem constant_rotate (a : ℕ) (rest : List ℕ) :
    (2 : ℤ) ^ a * (syracuseWordConst (rest ++ [a]) : ℤ) =
      3 * (syracuseWordConst (a :: rest) : ℤ) + denominator (a :: rest) := by
  rw [syracuseWordConst_append_singleton]
  simp only [denominator, List.sum_cons, List.length_cons, syracuseWordConst,
    Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add, pow_succ]
  ring

/-- A divisor of the cycle denominator divides one constant precisely when
it divides the rotated constant. The coprimality inputs expose the exact
cancellation needed; no cycle-existence assumption is used. -/
theorem dvd_constant_iff_dvd_rotated (a : ℕ) (rest : List ℕ) (d : ℤ)
    (hd : d ∣ denominator (a :: rest))
    (h2 : IsCoprime d (2 : ℤ)) (h3 : IsCoprime d (3 : ℤ)) :
    d ∣ (syracuseWordConst (a :: rest) : ℤ) ↔
      d ∣ (syracuseWordConst (rest ++ [a]) : ℤ) := by
  have hid := constant_rotate a rest
  constructor
  · intro hc
    have hmul : d ∣ (2 : ℤ) ^ a * (syracuseWordConst (rest ++ [a]) : ℤ) := by
      rw [hid]
      exact dvd_add (dvd_mul_of_dvd_right hc 3) hd
    exact h2.pow_right.dvd_of_dvd_mul_left hmul
  · intro hc
    have hmul : d ∣ 3 * (syracuseWordConst (a :: rest) : ℤ) := by
      have hdifference := dvd_sub (dvd_mul_of_dvd_right hc ((2 : ℤ) ^ a)) hd
      rw [hid, add_sub_cancel_right] at hdifference
      exact hdifference
    exact h3.dvd_of_dvd_mul_left hmul

/-- The whole denominator's divisibility sieve is likewise rotation-invariant.
This records the common concrete use with coprimality made explicit. -/
theorem denominator_dvd_constant_iff (a : ℕ) (rest : List ℕ)
    (h2 : IsCoprime (denominator (a :: rest)) (2 : ℤ))
    (h3 : IsCoprime (denominator (a :: rest)) (3 : ℤ)) :
    denominator (a :: rest) ∣ (syracuseWordConst (a :: rest) : ℤ) ↔
      denominator (rest ++ [a]) ∣ (syracuseWordConst (rest ++ [a]) : ℤ) := by
  rw [denominator_rotate]
  exact dvd_constant_iff_dvd_rotated a rest _ (dvd_refl _) h2 h3

/-- A positive closed exact word satisfies the signed denominator equation. -/
theorem denominator_mul_source {w : List ℕ} {n : ℕ}
    (hm : SyracuseWordMatchesFrom w n) (hclosed : evalSyracuseWord w n = n) :
    denominator w * (n : ℤ) = (syracuseWordConst w : ℤ) :=
  syracuseWordCycleEquationInt hm hclosed

/-- A valid closed exact word passes every divisor test; rotating the same
test does not give an additional independent exclusion. -/
theorem cycle_divisor_passes_rotated {a : ℕ} {rest : List ℕ} {n : ℕ} {d : ℤ}
    (hm : SyracuseWordMatchesFrom (a :: rest) n)
    (hclosed : evalSyracuseWord (a :: rest) n = n)
    (hd : d ∣ denominator (a :: rest))
    (h2 : IsCoprime d (2 : ℤ)) (h3 : IsCoprime d (3 : ℤ)) :
    d ∣ (syracuseWordConst (rest ++ [a]) : ℤ) := by
  apply (dvd_constant_iff_dvd_rotated a rest d hd h2 h3).mp
  rw [← denominator_mul_source hm hclosed]
  exact dvd_mul_of_dvd_left hd (n : ℤ)


end CollatzShadowing.CycleRotation
