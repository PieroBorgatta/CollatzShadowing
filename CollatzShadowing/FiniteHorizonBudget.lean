/-
Finite-horizon localization of exact Syracuse predecessor catalogues.

The source lower bound is deterministic. The reciprocal-square tail then
improves the tilted-atom budget when all sources are large. This file does
not import a random law, an Lp estimate, a cutoff identity or a mixing rate.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/

import CollatzShadowing.FirstArrivalBudget
import CollatzShadowing.IntegerAtomTilt

namespace CollatzShadowing.FiniteHorizonBudget

open WeightedVisits RootPoolBudget
open scoped BigOperators

/-- Every odd accelerated step grows the shifted height by at most 3/2. -/
theorem step_shifted_growth {u : ℕ} (hu : Odd u) :
    2 * (S u + 1) ≤ 3 * (u + 1) := by
  have ha := FirstArrivalBudget.exponent_pos_of_odd hu
  obtain ⟨a, he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have hp : 0 < 2 ^ a := by positivity
  have hpow : 2 ≤ 2 ^ syracuseExponent u := by
    rw [he, pow_succ]
    omega
  have hstep : 2 ^ syracuseExponent u * S u = 3 * u + 1 := by
    simpa [syracuseStepWithExponent, S, syracuseNumerator] using
      (pow_mul_syracuseStepWithExponent_eq_of_exponent
        (n := u) (a := syracuseExponent u) rfl)
  have hb := Nat.mul_le_mul_right (S u) hpow
  omega

/-- The exact forward orbit has the universal shifted-height envelope. -/
theorem iterate_shifted_growth {u : ℕ} (hu : Odd u) (k : ℕ) :
    2 ^ k * (S^[k] u + 1) ≤ 3 ^ k * (u + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hs : 2 * (S^[k + 1] u + 1) ≤ 3 * (S^[k] u + 1) := by
        simpa only [Function.iterate_succ_apply'] using
          step_shifted_growth (FirstArrivalBudget.orbit_odd hu k)
      calc
        2 ^ (k + 1) * (S^[k + 1] u + 1) =
            2 ^ k * (2 * (S^[k + 1] u + 1)) := by ring
        _ ≤ 2 ^ k * (3 * (S^[k] u + 1)) := Nat.mul_le_mul_left _ hs
        _ = 3 * (2 ^ k * (S^[k] u + 1)) := by ring
        _ ≤ 3 * (3 ^ k * (u + 1)) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (k + 1) * (u + 1) := by ring

/-- An arrival by time K has a source bounded below by the growth envelope.
The empty word and periodic targets are allowed. -/
theorem source_lower_of_horizon {w : List ℕ} {u n K R : ℕ}
    (hu : Odd u) (hm : SyracuseWordMatchesFrom w u)
    (he : evalSyracuseWord w u = n) (hk : w.length ≤ K)
    (hR : 3 ^ K * (R + 1) ≤ 2 ^ K * (n + 1)) : R ≤ u := by
  have hg := iterate_shifted_growth hu w.length
  rw [← evalSyracuseWord_eq_iterate_of_matches w u hm, he] at hg
  have hp : 2 ^ (K - w.length) ≤ 3 ^ (K - w.length) := by
    exact pow_le_pow_left' (by omega : (2 : ℕ) ≤ 3) _
  have hpow2 : 2 ^ K = 2 ^ (K - w.length) * 2 ^ w.length := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hpow3 : 3 ^ K = 3 ^ (K - w.length) * 3 ^ w.length := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hfull : 2 ^ K * (n + 1) ≤ 3 ^ K * (u + 1) := by
    rw [hpow2, hpow3]
    calc
      _ = 2 ^ (K - w.length) * (2 ^ w.length * (n + 1)) := by ring
      _ ≤ 2 ^ (K - w.length) * (3 ^ w.length * (u + 1)) :=
        Nat.mul_le_mul_left _ hg
      _ ≤ 3 ^ (K - w.length) * (3 ^ w.length * (u + 1)) :=
        Nat.mul_le_mul_right _ hp
      _ = _ := by ring
  have hle := le_trans hR hfull
  have hpos : 0 < 3 ^ K := by positivity
  have : R + 1 ≤ u + 1 := Nat.le_of_mul_le_mul_left hle hpos
  omega

private theorem reciprocal_square_shifted_range (R : ℕ) (hR : 0 < R) (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 : ℚ) / ((R : ℚ) + j) ^ 2) ≤
      2 / (R : ℚ) - 2 / ((R : ℚ) + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hR' : (1 : ℚ) ≤ R := by exact_mod_cast hR
      have hN : (0 : ℚ) ≤ N := by positivity
      have h1 : (0 : ℚ) < (R : ℚ) + N := by linarith
      have h2 : (0 : ℚ) < (R : ℚ) + N + 1 := by linarith
      have hs : (1 : ℚ) / ((R : ℚ) + N) ^ 2 ≤
          2 / ((R : ℚ) + N) - 2 / ((R : ℚ) + N + 1) := by
        field_simp
        nlinarith
      rw [Finset.sum_range_succ]
      push_cast
      rw [show (R : ℚ) + ((N : ℚ) + 1) = (R : ℚ) + N + 1 by ring]
      linarith

/-- The reciprocal-square budget of any finite tail is at most 2/R. -/
theorem reciprocal_square_tail (U : Finset ℕ) {R : ℕ} (hR : 0 < R)
    (hmin : ∀ u ∈ U, R ≤ u) :
    ∑ u ∈ U, (1 : ℚ) / (u : ℚ) ^ 2 ≤ 2 / (R : ℚ) := by
  let N := U.sup id + 1
  have hsub : U ⊆ (Finset.range N).image (fun j => R + j) := by
    intro u hu
    have huN : u < N := by
      have h := Finset.le_sup (f := id) hu
      change u ≤ U.sup id at h
      dsimp [N]
      omega
    have hru := hmin u hu
    refine Finset.mem_image.mpr ⟨u - R, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  calc
    _ ≤ ∑ u ∈ (Finset.range N).image (fun j => R + j),
        (1 : ℚ) / (u : ℚ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = ∑ j ∈ Finset.range N, (1 : ℚ) / ((R : ℚ) + j) ^ 2 := by
      rw [Finset.sum_image (by
        intro a ha b hb hab
        change R + a = R + b at hab
        omega)]
      simp only [Nat.cast_add]
    _ ≤ 2 / (R : ℚ) - 2 / ((R : ℚ) + N) :=
      reciprocal_square_shifted_range R hR N
    _ ≤ 2 / (R : ℚ) := sub_le_self _ (by positivity)

/-- A physical source catalogue above R spends at most 2*n^2/R tilted mass.
Source injectivity is explicit; no nonreturn or length assumption is hidden. -/
theorem tilted_tail_catalogue (W : Finset (List ℕ))
    (source : List ℕ → ℕ) {n R : ℕ} (hn : 0 < n) (hR : 0 < R)
    (hmin : ∀ w ∈ W, R ≤ source w)
    (hm : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (he : ∀ w ∈ W, evalSyracuseWord w (source w) = n)
    (hinj : ∀ a ∈ W, ∀ b ∈ W, source a = source b → a = b) :
    ∑ w ∈ W, (wordWeight w) ^ 2 ≤ 2 * (n : ℚ) ^ 2 / R := by
  have hb (w : List ℕ) (hw : w ∈ W) :
      wordWeight w ≤ (n : ℚ) / source w := by
    have hu : 0 < source w := lt_of_lt_of_le hR (hmin w hw)
    have hp := reciprocalWeight_le_initial hu (hm w hw)
    rw [reciprocalWeight, he w hw] at hp
    have hu' : (0 : ℚ) < source w := by exact_mod_cast hu
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    exact (le_div_iff₀ hu').mpr (by
      simpa only [one_mul] using (div_le_div_iff₀ hn' hu').mp hp)
  calc
    _ ≤ ∑ w ∈ W, ((n : ℚ) / source w) ^ 2 := by
      apply Finset.sum_le_sum
      intro w hw
      have h := hb w hw
      have hnonneg := wordWeight_nonneg w
      have hdiv : (0 : ℚ) ≤ (n : ℚ) / source w := by positivity
      nlinarith
    _ = (n : ℚ) ^ 2 * ∑ w ∈ W, (1 : ℚ) / (source w : ℚ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = (n : ℚ) ^ 2 * ∑ u ∈ W.image source, (1 : ℚ) / (u : ℚ) ^ 2 := by
      rw [Finset.sum_image hinj]
    _ ≤ (n : ℚ) ^ 2 * (2 / R) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply reciprocal_square_tail _ hR
      intro u hu
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
      exact hmin w hw
    _ = _ := by ring

/-- Growth localization and source injectivity give a finite-horizon budget. -/
theorem tilted_horizon_catalogue (W : Finset (List ℕ))
    (source : List ℕ → ℕ) {n K R : ℕ} (hn : 0 < n) (hR : 0 < R)
    (hodd : ∀ w ∈ W, Odd (source w))
    (hm : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (he : ∀ w ∈ W, evalSyracuseWord w (source w) = n)
    (hk : ∀ w ∈ W, w.length ≤ K)
    (hscale : 3 ^ K * (R + 1) ≤ 2 ^ K * (n + 1))
    (hinj : ∀ a ∈ W, ∀ b ∈ W, source a = source b → a = b) :
    ∑ w ∈ W, (wordWeight w) ^ 2 ≤ 2 * (n : ℚ) ^ 2 / R := by
  apply tilted_tail_catalogue W source hn hR _ hm he hinj
  intro w hw
  exact source_lower_of_horizon (hodd w hw) (hm w hw) (he w hw) (hk w hw) hscale

/-- At one fixed depth the source injectivity is automatic, even on cycles. -/
theorem tilted_fixed_depth_tail (W : Finset (List ℕ))
    (source : List ℕ → ℕ) {n k R : ℕ} (hn : 0 < n) (hR : 0 < R)
    (hodd : ∀ w ∈ W, Odd (source w))
    (hm : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (he : ∀ w ∈ W, evalSyracuseWord w (source w) = n)
    (hk : ∀ w ∈ W, w.length = k)
    (hscale : 3 ^ k * (R + 1) ≤ 2 ^ k * (n + 1)) :
    ∑ w ∈ W, (wordWeight w) ^ 2 ≤ 2 * (n : ℚ) ^ 2 / R := by
  apply tilted_horizon_catalogue W source hn hR hodd hm he
    (fun w hw => le_of_eq (hk w hw)) hscale
  intro a ha b hb hab
  apply matches_eq_of_length_eq (hm a ha)
  · rw [hab]
    exact hm b hb
  · exact (hk a ha).trans (hk b hb).symm

/-- All depths up to K share the tail budget at a target without returns. -/
theorem tilted_nonreturn_horizon (W : Finset (List ℕ))
    (source : List ℕ → ℕ) {n K R : ℕ} (hn : 0 < n) (hR : 0 < R)
    (hreturn : ∀ j : ℕ, 0 < j → S^[j] n ≠ n)
    (hodd : ∀ w ∈ W, Odd (source w))
    (hm : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (he : ∀ w ∈ W, evalSyracuseWord w (source w) = n)
    (hk : ∀ w ∈ W, w.length ≤ K)
    (hscale : 3 ^ K * (R + 1) ≤ 2 ^ K * (n + 1)) :
    ∑ w ∈ W, (wordWeight w) ^ 2 ≤ 2 * (n : ℚ) ^ 2 / R := by
  have hP : NonrecurrentPool S ({n} : Set ℕ) := by
    intro r hr j hj hhit
    have hr' : r = n := Set.mem_singleton_iff.mp hr
    subst r
    exact hreturn j hj (Set.mem_singleton_iff.mp hhit)
  apply tilted_horizon_catalogue W source hn hR hodd hm he hk hscale
  intro a ha b hb hab
  apply word_eq_of_pool hP (hm a ha)
  · rw [hab]
    exact hm b hb
  · rw [he a ha]
    exact Set.mem_singleton n
  · rw [hab, he b hb]
    exact Set.mem_singleton n

end CollatzShadowing.FiniteHorizonBudget
