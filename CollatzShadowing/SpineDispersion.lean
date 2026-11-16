/-
Finite collision budgets along a distinguished branch.

If the probability of the distinguished predecessor is R_i/R_(i+1),
with R positive and nondecreasing, all finite collision defects spend
a shared budget. The application to the canonical inverse Syracuse law
still requires its external trace identities. No mixing or lower bound,
infinite random process, or Collatz conclusion is imported here.

The first-split and squared-kernel mechanism is standard probability;
this is its finite algebraic integration in the present programme.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace CollatzShadowing.SpineDispersion

open scoped BigOperators

/-- A selected branch alone bounds the full collision defect from above.
No sign or total-mass assumptions are needed for this upper bound. -/
theorem collision_defect_le_selected {ι : Type*} (P : Finset ι)
    (p : ι → ℝ) {b : ι} (hb : b ∈ P) :
    1 - ∑ i ∈ P, (p i) ^ 2 ≤ 1 - (p b) ^ 2 := by
  have h := Finset.single_le_sum (fun i (_ : i ∈ P) => sq_nonneg (p i)) hb
  linarith

/-- A nonnegative subprobability catalogue has a nonnegative defect. -/
theorem collision_defect_nonneg {ι : Type*} (P : Finset ι)
    (p : ι → ℝ) (hpos : ∀ i ∈ P, 0 ≤ p i)
    (hmass : ∑ i ∈ P, p i ≤ 1) :
    0 ≤ 1 - ∑ i ∈ P, (p i) ^ 2 := by
  have hsq : (∑ i ∈ P, (p i) ^ 2) ≤ ∑ i ∈ P, p i := by
    apply Finset.sum_le_sum
    intro i hi
    have hp0 := hpos i hi
    have hp1 : p i ≤ 1 := (Finset.single_le_sum hpos hi).trans hmass
    nlinarith
  linarith

/-- Two distinct branches of mass at least a certify dispersion at least a.
This is a finite probability certificate, not an assertion that such
branches exist for the inverse Syracuse law. -/
theorem collision_defect_ge_of_two_branches {ι : Type*} (P : Finset ι)
    (p : ι → ℝ) {a : ℝ}
    (hpos : ∀ i ∈ P, 0 ≤ p i) (hmass : ∑ i ∈ P, p i ≤ 1)
    {b c : ι} (hb : b ∈ P) (hc : c ∈ P) (hne : b ≠ c)
    (hba : a ≤ p b) (hca : a ≤ p c) :
    a ≤ 1 - ∑ i ∈ P, (p i) ^ 2 := by
  classical
  have hpair {i j : ι} (hi : i ∈ P) (hj : j ∈ P) (hij : i ≠ j) :
      p i + p j ≤ 1 := by
    have hsub : ({i, j} : Finset ι) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hi
      · exact hj
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro x hx hnot
      exact hpos x hx)
    have hs : (∑ x ∈ ({i, j} : Finset ι), p x) = p i + p j := by
      simp [hij]
    rw [hs] at h
    exact h.trans hmass
  have hmax (i : ι) (hi : i ∈ P) : p i ≤ 1 - a := by
    by_cases hib : i = b
    · subst i
      have h := hpair hb hc hne
      linarith
    · have h := hpair hi hb hib
      linarith
  have hfactor : 0 ≤ 1 - a := by
    have hp := hpos b hb
    have hm := hmax b hb
    linarith
  have hsq : (∑ i ∈ P, (p i) ^ 2) ≤ (1 - a) * ∑ i ∈ P, p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h0 := hpos i hi
    have h1 := hmax i hi
    nlinarith
  have htotal := mul_le_mul_of_nonneg_left hmass hfactor
  nlinarith

/-- A family of lower allocations pays its total mass minus the largest
allocation. Applied to distinct physical parent witnesses, this permits
many moderate witnesses in place of two individually small witnesses.
The algebraic bound remains valid for signed lower allocations. -/
theorem collision_defect_ge_lower_allocations {ι : Type*} (P : Finset ι)
    (p lower : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hpos : ∀ i ∈ P, 0 ≤ p i) (hmass : ∑ i ∈ P, p i ≤ 1)
    (hlower : ∀ i ∈ P, lower i ≤ p i)
    (hmax : ∀ i ∈ P, lower i ≤ M) :
    (∑ i ∈ P, lower i) - M ≤ 1 - ∑ i ∈ P, (p i) ^ 2 := by
  have htotal : (∑ i ∈ P, lower i) ≤ ∑ i ∈ P, p i :=
    Finset.sum_le_sum hlower
  have hfactor : 0 ≤ 1 - (∑ i ∈ P, lower i) + M := by linarith
  have hpoint (i : ι) (hi : i ∈ P) :
      p i ≤ 1 - (∑ j ∈ P, lower j) + M := by
    have hs := Finset.single_le_sum
      (fun j hj => sub_nonneg.mpr (hlower j hj)) hi
    rw [Finset.sum_sub_distrib] at hs
    have hm := hmax i hi
    linarith
  have hsq : (∑ i ∈ P, (p i) ^ 2) ≤
      (1 - (∑ i ∈ P, lower i) + M) * ∑ i ∈ P, p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h0 := hpos i hi
    have h1 := hpoint i hi
    nlinarith
  have hs := mul_le_mul_of_nonneg_left hmass hfactor
  nlinarith

/-- The square defect of a positive ratio is paid by its monotone increment. -/
theorem ratio_square_defect_le {a x y : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hxy : x ≤ y) :
    1 - (x / y) ^ 2 ≤ 2 * (y - x) / a := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hay : a ≤ y := hax.trans hxy
  have hy : 0 < y := lt_of_lt_of_le ha hay
  have hp : 1 - (x / y) ^ 2 ≤ 2 * (1 - x / y) := by
    nlinarith [sq_nonneg (1 - x / y)]
  have hid : 1 - x / y = (y - x) / y := by
    field_simp
  have hdiv : (y - x) / y ≤ (y - x) / a := by
    apply (div_le_div_iff₀ hy ha).mpr
    exact mul_le_mul_of_nonneg_left hay (sub_nonneg.mpr hxy)
  rw [hid] at hp
  calc
    _ ≤ 2 * ((y - x) / y) := hp
    _ ≤ 2 * ((y - x) / a) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = _ := by ring

private theorem sum_increment (R : ℕ → ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, (R (i + 1) - R i) = R N - R 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- Every finite prefix spends at most its total normalized-trace increase. -/
theorem ratio_square_prefix_budget (R : ℕ → ℝ) (N : ℕ) {a : ℝ}
    (ha : 0 < a) (hfloor : ∀ i ≤ N, a ≤ R i)
    (hmono : ∀ i < N, R i ≤ R (i + 1)) :
    (∑ i ∈ Finset.range N, (1 - (R i / R (i + 1)) ^ 2)) ≤
      (2 / a) * (R N - R 0) := by
  calc
    _ ≤ ∑ i ∈ Finset.range N, 2 * (R (i + 1) - R i) / a := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN := Finset.mem_range.mp hi
      exact ratio_square_defect_le ha (hfloor i (by omega)) (hmono i hiN)
    _ = (2 / a) * ∑ i ∈ Finset.range N, (R (i + 1) - R i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [sum_increment]

/-- Finite physical branch catalogues share the same dispersion budget.
If p_i is a probability law, the summand is its two-copy disagreement.
For a truncated catalogue containing the selected branch it is an upper
bound for the disagreement of any larger probability catalogue. -/
theorem collision_spine_budget {ι : Type*}
    (R : ℕ → ℝ) (N : ℕ) (P : ℕ → Finset ι)
    (p : ℕ → ι → ℝ) (branch : ℕ → ι) {a : ℝ}
    (ha : 0 < a) (hfloor : ∀ i ≤ N, a ≤ R i)
    (hmono : ∀ i < N, R i ≤ R (i + 1))
    (hbranch : ∀ i < N, branch i ∈ P i)
    (hratio : ∀ i < N, p i (branch i) = R i / R (i + 1)) :
    (∑ i ∈ Finset.range N, (1 - ∑ j ∈ P i, (p i j) ^ 2)) ≤
      (2 / a) * (R N - R 0) := by
  apply le_trans _ (ratio_square_prefix_budget R N ha hfloor hmono)
  apply Finset.sum_le_sum
  intro i hi
  have hiN := Finset.mem_range.mp hi
  have hb := collision_defect_le_selected (P i) (p i) (hbranch i hiN)
  rw [hratio i hiN] at hb
  exact hb

end CollatzShadowing.SpineDispersion
