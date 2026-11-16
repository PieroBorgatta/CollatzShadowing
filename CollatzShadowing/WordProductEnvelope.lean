/-
Product envelopes for actual Syracuse words and same-profile transports.

The reciprocal budget is an explicit hypothesis. In particular this module
neither assumes nor proves the universal orbit packing estimate, an outgoing
mass estimate, or a comparison of predecessor densities.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/

import CollatzShadowing.WeightedWords
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace CollatzShadowing.WordProductEnvelope

open scoped BigOperators
open WeightedVisits

/-- The multiplicative inflation relative to the homogeneous Syracuse slope. -/
noncomputable def inflation (x k : ℕ) : ℝ :=
  (2 : ℝ) ^ exponentSum x k * (S^[k] x : ℝ) / ((3 : ℝ) ^ k * x)

/-- One actual step multiplies inflation by its local additive correction. -/
theorem inflation_succ {x : ℕ} (hx : 0 < x) (k : ℕ) :
    inflation x (k + 1) =
      inflation x k * (1 + 1 / (3 * (S^[k] x : ℝ))) := by
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hx
  have hn : (S^[k] x : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (orbit_pos hx k)
  have hstep : (2 : ℝ) ^ syracuseExponent (S^[k] x) * (S^[k + 1] x : ℝ) =
      3 * (S^[k] x : ℝ) + 1 := by exact_mod_cast orbit_step x k
  unfold inflation
  rw [exponentSum, pow_add, pow_succ]
  field_simp
  nlinarith [hstep]

/-- Exact product identity; repeated visits are allowed. -/
theorem inflation_eq_product {x : ℕ} (hx : 0 < x) (k : ℕ) :
    inflation x k = ∏ i ∈ Finset.range k, (1 + 1 / (3 * (S^[i] x : ℝ))) := by
  induction k with
  | zero => simp [inflation, exponentSum, Nat.ne_of_gt hx]
  | succ k ih => rw [inflation_succ hx, Finset.prod_range_succ, ih]

/-- A reciprocal budget bounds inflation exponentially. No orbit packing
or first-arrival assumption is hidden in this statement. -/
theorem inflation_le_exp_of_reciprocal_budget {x k : ℕ} {B : ℝ}
    (hx : 0 < x)
    (hbudget : (∑ i ∈ Finset.range k, 1 / (S^[i] x : ℝ)) ≤ B) :
    inflation x k ≤ Real.exp (B / 3) := by
  rw [inflation_eq_product hx]
  calc
    _ ≤ ∏ i ∈ Finset.range k, Real.exp (1 / (3 * (S^[i] x : ℝ))) := by
      apply Finset.prod_le_prod
      · intro i hi
        have hn : (0 : ℝ) < S^[i] x := by exact_mod_cast orbit_pos hx i
        positivity
      · intro i hi
        have h := Real.add_one_le_exp (1 / (3 * (S^[i] x : ℝ)))
        simpa only [add_comm] using h
    _ = Real.exp (∑ i ∈ Finset.range k, 1 / (3 * (S^[i] x : ℝ))) :=
      (Real.exp_sum _ _).symm
    _ ≤ Real.exp (B / 3) := by
      apply Real.exp_le_exp.mpr
      calc
        _ = (∑ i ∈ Finset.range k, 1 / (S^[i] x : ℝ)) / 3 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ B / 3 := div_le_div_of_nonneg_right hbudget (by norm_num)

/-- Inflation, written with the endpoint and exponent total of an exact word. -/
theorem exact_word_inflation {w : List ℕ} {u n : ℕ}
    (hm : SyracuseWordMatchesFrom w u) (he : evalSyracuseWord w u = n) :
    inflation u w.length = (2 : ℝ) ^ w.sum * n / ((3 : ℝ) ^ w.length * u) := by
  unfold inflation
  rw [← word_sum_eq_exponentSum hm, ← evalSyracuseWord_eq_iterate_of_matches w u hm, he]

/-- Every actual same-length, same-total image has a controlled height.
Existence of the image word is an input and no positive mass is asserted. -/
theorem same_profile_height {w w' : List ℕ} {u v n y : ℕ} {B : ℝ}
    (hu : 0 < u) (hn : 0 < n)
    (hw : SyracuseWordMatchesFrom w u) (he : evalSyracuseWord w u = n)
    (hw' : SyracuseWordMatchesFrom w' v) (he' : evalSyracuseWord w' v = y)
    (hk : w'.length = w.length) (hA : w'.sum = w.sum)
    (hbudget : (∑ i ∈ Finset.range w.length, 1 / (S^[i] u : ℝ)) ≤ B) :
    (v : ℝ) ≤ (y : ℝ) / n * Real.exp (B / 3) * u := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (3 : ℝ) ^ w.length := by positivity
  have hinf := inflation_le_exp_of_reciprocal_budget hu hbudget
  rw [exact_word_inflation hw he] at hinf
  have hscaled : (2 : ℝ) ^ w.sum * n ≤
      Real.exp (B / 3) * ((3 : ℝ) ^ w.length * u) :=
    (div_le_iff₀ (mul_pos hp hu')).mp hinf
  have ha := evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w' v hw'
  rw [he', hk, hA] at ha
  have ha' : (3 : ℝ) ^ w.length * v + (syracuseWordConst w' : ℝ) =
      (2 : ℝ) ^ w.sum * y := by exact_mod_cast ha.symm
  have hvbound : (3 : ℝ) ^ w.length * v ≤ (2 : ℝ) ^ w.sum * y := by
    have hc : (0 : ℝ) ≤ syracuseWordConst w' := by positivity
    linarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (le_div_iff₀ hn').mpr
  apply (mul_le_mul_iff_right₀ hp).mp
  have hleft := mul_le_mul_of_nonneg_right hvbound hn'.le
  have hright := mul_le_mul_of_nonneg_right hscaled (show (0 : ℝ) ≤ y by positivity)
  nlinarith

/-- At reciprocal budget 81 and endpoint ratio at most 21, the same-profile
height constant is 21 * exp 27. The image still has to exist. -/
theorem same_profile_height_81 {w w' : List ℕ} {u v n y : ℕ}
    (hu : 0 < u) (hn : 0 < n)
    (hw : SyracuseWordMatchesFrom w u) (he : evalSyracuseWord w u = n)
    (hw' : SyracuseWordMatchesFrom w' v) (he' : evalSyracuseWord w' v = y)
    (hk : w'.length = w.length) (hA : w'.sum = w.sum)
    (hbudget : (∑ i ∈ Finset.range w.length, 1 / (S^[i] u : ℝ)) ≤ 81)
    (hyn : y ≤ 21 * n) :
    (v : ℝ) ≤ 21 * Real.exp 27 * u := by
  have h := same_profile_height hu hn hw he hw' he' hk hA hbudget
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (y : ℝ) / n ≤ 21 := by
    apply (div_le_iff₀ hn').mpr
    exact_mod_cast hyn
  norm_num at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hr (Real.exp_nonneg 27)) (by positivity))

/-- Preserving a profile is unnecessary: a bounded ratio of homogeneous
slopes also controls the height. Both lengths and exponent totals may vary.
The cross-multiplied slope comparison and image existence are explicit. -/
theorem comparable_slope_height {w w' : List ℕ} {u v n y : ℕ} {B C : ℝ}
    (hu : 0 < u) (hn : 0 < n) (hC : 0 ≤ C)
    (hw : SyracuseWordMatchesFrom w u) (he : evalSyracuseWord w u = n)
    (hw' : SyracuseWordMatchesFrom w' v) (he' : evalSyracuseWord w' v = y)
    (hbudget : (∑ i ∈ Finset.range w.length, 1 / (S^[i] u : ℝ)) ≤ B)
    (hslope : (2 : ℝ) ^ w'.sum * (3 : ℝ) ^ w.length ≤
      C * (2 : ℝ) ^ w.sum * (3 : ℝ) ^ w'.length) :
    (v : ℝ) ≤ C * ((y : ℝ) / n) * Real.exp (B / 3) * u := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < (3 : ℝ) ^ w.length := by positivity
  have hq : (0 : ℝ) < (3 : ℝ) ^ w'.length := by positivity
  have hy : (0 : ℝ) ≤ y := by positivity
  have hinf := inflation_le_exp_of_reciprocal_budget hu hbudget
  rw [exact_word_inflation hw he] at hinf
  have hscaled := (div_le_iff₀ (mul_pos hp hu')).mp hinf
  have hbase : (2 : ℝ) ^ w.sum / (3 : ℝ) ^ w.length ≤
      Real.exp (B / 3) * u / n := by
    apply (div_le_div_iff₀ hp hn').mpr
    nlinarith only [hscaled]
  have hratio : (2 : ℝ) ^ w'.sum / (3 : ℝ) ^ w'.length ≤
      (C * (2 : ℝ) ^ w.sum) / (3 : ℝ) ^ w.length :=
    (div_le_div_iff₀ hq hp).mpr hslope
  have ha := evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w' v hw'
  rw [he'] at ha
  have ha' : (3 : ℝ) ^ w'.length * v + (syracuseWordConst w' : ℝ) =
      (2 : ℝ) ^ w'.sum * y := by exact_mod_cast ha.symm
  have hv : (v : ℝ) ≤ ((2 : ℝ) ^ w'.sum / (3 : ℝ) ^ w'.length) * y := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hq).mpr
    have hc : (0 : ℝ) ≤ syracuseWordConst w' := by positivity
    nlinarith only [ha', hc]
  calc
    (v : ℝ) ≤ ((2 : ℝ) ^ w'.sum / (3 : ℝ) ^ w'.length) * y := hv
    _ ≤ ((C * (2 : ℝ) ^ w.sum) / (3 : ℝ) ^ w.length) * y :=
      mul_le_mul_of_nonneg_right hratio hy
    _ = (C * ((2 : ℝ) ^ w.sum / (3 : ℝ) ^ w.length)) * y := by ring
    _ ≤ (C * (Real.exp (B / 3) * u / n)) * y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase hC) hy
    _ = C * ((y : ℝ) / n) * Real.exp (B / 3) * u := by ring

end CollatzShadowing.WordProductEnvelope
