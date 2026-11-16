/-
Exact minimum-product constraints for finite Syracuse paths and cycles.

The integer product bound is classical. This file completes the independent
local candidate recorded in the November 13 cycle review. It imports no
external cycle-exclusion theorem, numerical verification range, or Rhin bound.
A lower bound M for every state remains an explicit hypothesis.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/

import CollatzShadowing.CycleConstraints
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CollatzShadowing.CycleMinimumProduct

/-- An exact path staying above M obeys the cross-multiplied product bound.
This avoids logarithms and holds for any finite path, not only cycles. -/
theorem path_minimum_product_bound (w : List ℕ) (n M : ℕ)
    (hm : SyracuseWordMatchesFrom w n)
    (hmin : ∀ j < w.length, M ≤ S^[j] n) :
    2 ^ w.sum * M ^ w.length * evalSyracuseWord w n ≤
      (3 * M + 1) ^ w.length * n := by
  induction w generalizing n with
  | nil => simp [evalSyracuseWord]
  | cons a rest ih =>
      rcases hm with ⟨ha, hrest⟩
      have hstep : syracuseStepWithExponent a n = S n := by
        simp [syracuseStepWithExponent, S, syracuseNumerator, ha]
      have hmul := pow_mul_syracuseStepWithExponent_eq_of_exponent ha
      rw [hstep] at hmul
      have hzero : M ≤ n := by simpa using hmin 0 (by simp)
      have hrestmin : ∀ j < rest.length, M ≤ S^[j] (S n) := by
        intro j hj
        simpa only [Function.iterate_succ_apply] using hmin (j + 1) (by simpa using hj)
      have htail := ih (S n) hrest hrestmin
      have hfirst : 2 ^ a * M * S n ≤ (3 * M + 1) * n := by
        calc
          _ = M * (2 ^ a * S n) := by ring
          _ = M * (3 * n + 1) := by rw [hmul]
          _ ≤ (3 * M + 1) * n := by nlinarith
      calc
        _ = (2 ^ a * M) *
            (2 ^ rest.sum * M ^ rest.length * evalSyracuseWord rest (S n)) := by
          simp only [List.sum_cons, List.length_cons, evalSyracuseWord, hstep,
            pow_add, pow_succ]
          ring
        _ ≤ (2 ^ a * M) * ((3 * M + 1) ^ rest.length * S n) :=
          Nat.mul_le_mul_left _ htail
        _ = (3 * M + 1) ^ rest.length * (2 ^ a * M * S n) := by ring
        _ ≤ (3 * M + 1) ^ rest.length * ((3 * M + 1) * n) :=
          Nat.mul_le_mul_left _ hfirst
        _ = _ := by rw [List.length_cons, pow_succ]; ring

/-- An exact positive cycle with minimum at least M satisfies an integer
gap constraint. A computational lower bound for its minimum remains an
external premise until separately certified. -/
theorem cycle_minimum_product_bound (w : List ℕ) (n M : ℕ) (hn : 0 < n)
    (hm : SyracuseWordMatchesFrom w n) (hclosed : evalSyracuseWord w n = n)
    (hmin : ∀ j < w.length, M ≤ S^[j] n) :
    2 ^ w.sum * M ^ w.length ≤ (3 * M + 1) ^ w.length := by
  have h := path_minimum_product_bound w n M hm hmin
  rw [hclosed] at h
  exact Nat.le_of_mul_le_mul_right h hn

/-- Classical logarithmic gap bound in the exact local word coordinates.
Any transcendence-theory lower bound remains a separate external input. -/
theorem cycle_log_gap_le (w : List ℕ) (n M : ℕ) (hn : 0 < n) (hM : 0 < M)
    (hm : SyracuseWordMatchesFrom w n) (hclosed : evalSyracuseWord w n = n)
    (hmin : ∀ j < w.length, M ≤ S^[j] n) :
    (w.sum : ℝ) * Real.log 2 - (w.length : ℝ) * Real.log 3 ≤
      (w.length : ℝ) / (3 * (M : ℝ)) := by
  have hprod := cycle_minimum_product_bound w n M hn hm hclosed hmin
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hprod' : (2 : ℝ) ^ w.sum * (M : ℝ) ^ w.length ≤
      (3 * (M : ℝ) + 1) ^ w.length := by exact_mod_cast hprod
  have hlog := Real.log_le_log (by positivity :
    0 < (2 : ℝ) ^ w.sum * (M : ℝ) ^ w.length) hprod'
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  simp only [Real.log_pow] at hlog
  have hsplit : 3 * (M : ℝ) + 1 =
      (3 * (M : ℝ)) * (1 + 1 / (3 * (M : ℝ))) := by field_simp
  rw [hsplit, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (ne_of_gt hM')] at hlog
  have hsmall : Real.log (1 + 1 / (3 * (M : ℝ))) ≤ 1 / (3 * (M : ℝ)) := by
    have h := Real.log_le_sub_one_of_pos (by positivity :
      0 < 1 + 1 / (3 * (M : ℝ)))
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hsmall
    (show (0 : ℝ) ≤ w.length by positivity)
  have hfinal : (w.sum : ℝ) * Real.log 2 - (w.length : ℝ) * Real.log 3 ≤
      (w.length : ℝ) * (1 / (3 * (M : ℝ))) := by nlinarith
  simpa [div_eq_mul_inv] using hfinal

end CollatzShadowing.CycleMinimumProduct
