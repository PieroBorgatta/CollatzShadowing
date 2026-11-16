/-
Finite tilted-atom bound at a positive integer target.

For a fixed length, distinct exact words to the same target have distinct
positive sources. The reciprocal potential bounds each word weight by
n/source, and a finite reciprocal-square budget gives a uniform bound 2*n^2.

This is the finite arithmetic core of the multiplier-cutoff localization
investigated with rStation paper 146 (14 November 2026). It imports no random
law, weak-L2 theorem, infinite cutoff identity or integer-trace limit.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/

import CollatzShadowing.RootPoolBudget

namespace CollatzShadowing.IntegerAtomTilt

open WeightedVisits RootPoolBudget
open scoped BigOperators

private theorem reciprocal_square_range_budget (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 : ℚ) / ((j : ℚ) + 1) ^ 2) ≤
      2 - 2 / ((N : ℚ) + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      have hN : (0 : ℚ) ≤ N := by positivity
      have h1 : (0 : ℚ) < (N : ℚ) + 1 := by positivity
      have h2 : (0 : ℚ) < (N : ℚ) + 2 := by positivity
      have hstep : (1 : ℚ) / ((N : ℚ) + 1) ^ 2 ≤
          2 / ((N : ℚ) + 1) - 2 / ((N : ℚ) + 2) := by
        field_simp
        nlinarith
      rw [Finset.sum_range_succ]
      push_cast
      rw [show (N : ℚ) + 1 + 1 = (N : ℚ) + 2 by ring]
      linarith

/-- A finite set of natural integers, including zero if present, spends at
most two units of reciprocal-square mass; at zero division is zero. -/
theorem sum_reciprocal_sq_finset_le_two (U : Finset ℕ) :
    ∑ u ∈ U, (1 : ℚ) / (u : ℚ) ^ 2 ≤ 2 := by
  let N := U.sup id
  have hsub : U ⊆ Finset.range (N + 1) := Finset.subset_range_sup_succ U
  have hrange : (∑ u ∈ Finset.range (N + 1), (1 : ℚ) / (u : ℚ) ^ 2) ≤ 2 := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), div_zero, add_zero,
      Nat.cast_add, Nat.cast_one]
    have h := reciprocal_square_range_budget N
    have hp : (0 : ℚ) ≤ 2 / ((N : ℚ) + 1) := by positivity
    linarith
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro u hu hnot
    positivity)).trans hrange

/-- An exact word's homogeneous weight is at most its positive target. -/
theorem wordWeight_le_target {w : List ℕ} {u n : ℕ}
    (hu : 0 < u) (hn : 0 < n)
    (hm : SyracuseWordMatchesFrom w u) (he : evalSyracuseWord w u = n) :
    wordWeight w ≤ (n : ℚ) := by
  have hp := reciprocalWeight_le_initial hu hm
  rw [reciprocalWeight, he] at hp
  have hu' : (0 : ℚ) < u := by exact_mod_cast hu
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hc := (div_le_div_iff₀ hn' hu').mp hp
  have hule : (1 : ℚ) ≤ u := by exact_mod_cast hu
  have hw := wordWeight_nonneg w
  nlinarith

/-- Uniform tilted mass for a finite catalogue with distinct physical
sources. Lengths may vary; source injectivity is an explicit input. -/
theorem tilted_catalogue_le_of_source_injective
    (W : Finset (List ℕ)) (source : List ℕ → ℕ)
    (n : ℕ) (hn : 0 < n)
    (hpos : ∀ w ∈ W, 0 < source w)
    (hm : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (he : ∀ w ∈ W, evalSyracuseWord w (source w) = n)
    (hinj : ∀ a ∈ W, ∀ b ∈ W, source a = source b → a = b) :
    ∑ w ∈ W, (wordWeight w) ^ 2 ≤ 2 * (n : ℚ) ^ 2 := by
  have hbound (w : List ℕ) (hw : w ∈ W) :
      wordWeight w ≤ (n : ℚ) / source w := by
    have hp := reciprocalWeight_le_initial (hpos w hw) (hm w hw)
    rw [reciprocalWeight, he w hw] at hp
    have hu' : (0 : ℚ) < source w := by exact_mod_cast hpos w hw
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    exact (le_div_iff₀ hu').mpr (by
      simpa only [one_mul] using (div_le_div_iff₀ hn' hu').mp hp)
  calc
    _ ≤ ∑ w ∈ W, ((n : ℚ) / source w) ^ 2 := by
      apply Finset.sum_le_sum
      intro w hw
      have h := hbound w hw
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
    _ ≤ (n : ℚ) ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left (sum_reciprocal_sq_finset_le_two _) (sq_nonneg _)
    _ = 2 * (n : ℚ) ^ 2 := by ring

/-- At a fixed length, exact words automatically have distinct positive
sources. Cyclic targets and the empty word are allowed. -/
theorem tilted_integer_atom_le (W : Finset (List ℕ)) (source : List ℕ → ℕ)
    (n k : ℕ) (hn : 0 < n)
    (hpos : ∀ w ∈ W, 0 < source w)
    (hm : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (he : ∀ w ∈ W, evalSyracuseWord w (source w) = n)
    (hk : ∀ w ∈ W, w.length = k) :
    ∑ w ∈ W, (wordWeight w) ^ 2 ≤ 2 * (n : ℚ) ^ 2 := by
  apply tilted_catalogue_le_of_source_injective W source n hn hpos hm he
  intro a ha b hb hab
  apply matches_eq_of_length_eq (hm a ha)
  · rw [hab]
    exact hm b hb
  · exact (hk a ha).trans (hk b hb).symm

/-- At a nonreturning target the same tilted budget is shared by all
depths, rather than charged afresh at each depth. -/
theorem tilted_nonreturn_catalogue_le
    (W : Finset (List ℕ)) (source : List ℕ → ℕ) (n : ℕ) (hn : 0 < n)
    (hreturn : ∀ j : ℕ, 0 < j → S^[j] n ≠ n)
    (hpos : ∀ w ∈ W, 0 < source w)
    (hm : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (he : ∀ w ∈ W, evalSyracuseWord w (source w) = n) :
    ∑ w ∈ W, (wordWeight w) ^ 2 ≤ 2 * (n : ℚ) ^ 2 := by
  have hP : NonrecurrentPool S ({n} : Set ℕ) := by
    intro r hr j hj hhit
    have hr' : r = n := Set.mem_singleton_iff.mp hr
    subst r
    exact hreturn j hj (Set.mem_singleton_iff.mp hhit)
  apply tilted_catalogue_le_of_source_injective W source n hn hpos hm he
  intro a ha b hb hab
  apply word_eq_of_pool hP (hm a ha)
  · rw [hab]
    exact hm b hb
  · rw [he a ha]
    exact Set.mem_singleton n
  · rw [hab, he b hb]
    exact Set.mem_singleton n

end CollatzShadowing.IntegerAtomTilt
