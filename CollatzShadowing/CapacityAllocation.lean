/-
Finite capacity allocation and its threshold certificate.

This is an independently proved local integration of the finite profile
mechanism described by Idris Ali Shaik, CollatzConvergencePositiveDensity,
commit f0fda887ee60dc8ac4ef0d864935148b03734726,
Counting/ProfileThreshold and Counting/ProfileDuality (Apache-2.0).
No external source module, optimizer, or analytic mass estimate is imported.

The application must supply actual physical cells, a proved capacity cap,
their scores, and a lower bound on their selected mass. None of these
premises follows merely from separate marginal distributions.

AI-assisted development: Codex with Piero Borgatta, 2026-11-13.
-/

import CollatzShadowing.WeightedCounting

namespace CollatzShadowing.CapacityAllocation

open scoped BigOperators

variable {ι : Type*}

/-- The pointwise hinge bound for one capped cell. Scores may be signed. -/
theorem capped_cell_bound {c h C t : ℝ} (hc : 0 ≤ c) (hcap : c ≤ C) :
    c * h ≤ t * c + C * max (h - t) 0 := by
  calc
    c * h = c * t + c * (h - t) := by ring
    _ ≤ c * t + c * max (h - t) 0 :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (le_max_left _ _) hc)
    _ ≤ c * t + C * max (h - t) 0 :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right hcap (le_max_right _ _))
    _ = t * c + C * max (h - t) 0 := by ring

/-- Sum the same physical-cell inequalities without replacing their scores
by a uniform maximum. -/
theorem mass_le_threshold_cost (I : Finset ι) (c h : ι → ℝ) (C t : ℝ)
    (hc : ∀ r ∈ I, 0 ≤ c r) (hcap : ∀ r ∈ I, c r ≤ C) :
    (∑ r ∈ I, c r * h r) ≤
      t * (∑ r ∈ I, c r) + C * ∑ r ∈ I, max (h r - t) 0 := by
  calc
    _ ≤ ∑ r ∈ I, (t * c r + C * max (h r - t) 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact capped_cell_bound (hc r hr) (hcap r hr)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- A lower selected mass produces a lower allocation bound. The mass
estimate p is an explicit input, not a new analytic conclusion. -/
theorem threshold_lower_bound (I : Finset ι) (c h : ι → ℝ) {C p t : ℝ}
    (hc : ∀ r ∈ I, 0 ≤ c r) (hcap : ∀ r ∈ I, c r ≤ C)
    (hpaid : p ≤ ∑ r ∈ I, c r * h r) (ht : 0 < t) :
    max (p - C * ∑ r ∈ I, max (h r - t) 0) 0 / t ≤ ∑ r ∈ I, c r := by
  have hcost := hpaid.trans (mass_le_threshold_cost I c h C t hc hcap)
  have hsum : 0 ≤ ∑ r ∈ I, c r := Finset.sum_nonneg hc
  apply (div_le_iff₀ ht).mpr
  apply max_le
  · nlinarith
  · exact mul_nonneg hsum ht.le

/-- Above the threshold cells are filled to capacity; below it they are
empty. Ties may have any allocation satisfying the application bounds. -/
def IsThresholdAllocation (I : Finset ι) (c h : ι → ℝ) (C t : ℝ) : Prop :=
  (∀ r ∈ I, t < h r → c r = C) ∧
    (∀ r ∈ I, h r < t → c r = 0)

/-- A threshold allocation saturates each hinge inequality, including ties. -/
theorem threshold_cell_identity (I : Finset ι) (c h : ι → ℝ) (C t : ℝ)
    (hthreshold : IsThresholdAllocation I c h C t) {r : ι} (hr : r ∈ I) :
    c r * h r = t * c r + C * max (h r - t) 0 := by
  rcases lt_trichotomy (h r) t with hlt | heq | hgt
  · rw [hthreshold.2 r hr hlt, max_eq_right (by linarith : h r - t ≤ 0)]
    ring
  · rw [heq]
    simp only [sub_self, max_self, mul_zero, add_zero]
    ring
  · rw [hthreshold.1 r hr hgt, max_eq_left (by linarith : 0 ≤ h r - t)]
    ring

/-- An exact mass and a threshold allocation certify equality in the bound.
This theorem does not assert existence of a feasible allocation. -/
theorem threshold_allocation_exact (I : Finset ι) (c h : ι → ℝ) {C p t : ℝ}
    (hc : ∀ r ∈ I, 0 ≤ c r) (ht : 0 < t)
    (hthreshold : IsThresholdAllocation I c h C t)
    (hpaid : (∑ r ∈ I, c r * h r) = p) :
    (∑ r ∈ I, c r) =
      max (p - C * ∑ r ∈ I, max (h r - t) 0) 0 / t := by
  have hsum : 0 ≤ ∑ r ∈ I, c r := Finset.sum_nonneg hc
  have he : p = t * (∑ r ∈ I, c r) + C * ∑ r ∈ I, max (h r - t) 0 := by
    rw [← hpaid]
    calc
      _ = ∑ r ∈ I, (t * c r + C * max (h r - t) 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact threshold_cell_identity I c h C t hthreshold hr
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hnonneg : 0 ≤ p - C * ∑ r ∈ I, max (h r - t) 0 := by
    nlinarith
  rw [max_eq_left hnonneg]
  apply (eq_div_iff ht.ne').mpr
  nlinarith

/-- A threshold certificate is a lower bound for every competing capped
allocation that pays the same demand. If the certificate itself respects
the cap, this certifies finite optimality without an imported optimizer. -/
theorem threshold_certificate_le_competitor (I : Finset ι) (c d h : ι → ℝ)
    {C p t : ℝ} (hc : ∀ r ∈ I, 0 ≤ c r)
    (hd : ∀ r ∈ I, 0 ≤ d r) (hcap : ∀ r ∈ I, d r ≤ C) (ht : 0 < t)
    (hthreshold : IsThresholdAllocation I c h C t)
    (hpaid : (∑ r ∈ I, c r * h r) = p)
    (hdemand : p ≤ ∑ r ∈ I, d r * h r) :
    (∑ r ∈ I, c r) ≤ ∑ r ∈ I, d r := by
  rw [threshold_allocation_exact I c h hc ht hthreshold hpaid]
  exact threshold_lower_bound I d h hd hcap hdemand ht

/-- The old maximum-score bound is the special threshold at an upper bound.
A smaller threshold may improve it when high-score capacity is limited. -/
theorem threshold_at_score_upper_bound (I : Finset ι) (h : ι → ℝ)
    {C p H : ℝ} (hp : 0 ≤ p) (hupper : ∀ r ∈ I, h r ≤ H) :
    max (p - C * ∑ r ∈ I, max (h r - H) 0) 0 / H = p / H := by
  have hzero : (∑ r ∈ I, max (h r - H) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    exact max_eq_right (sub_nonpos.mpr (hupper r hr))
  rw [hzero, mul_zero, sub_zero, max_eq_left hp]

end CollatzShadowing.CapacityAllocation
