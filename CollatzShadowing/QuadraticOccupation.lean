/-
Squared reciprocal potential and recurrent tilted-atom budgets.

These finite statements allow repeated visits and periodic targets. Finiteness
of the integer tilted Green function was already stated in rStation paper 9/v1,
Proposition 11 (21 October 2026). The local contribution is an explicit squared
dissipation proof and its slightly sharper constant, not a novelty claim for
Green finiteness. No random law or infinite series theorem is imported.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/

import CollatzShadowing.IntegerAtomTilt

namespace CollatzShadowing.QuadraticOccupation

open WeightedVisits
open scoped BigOperators

/-- The exact decrement of the square of the reciprocal potential. -/
def squareLoss (x k : ℕ) : ℚ :=
  (weight x k) ^ 2 * (6 * (S^[k] x : ℚ) + 1) /
    ((S^[k] x : ℚ) ^ 2 * (3 * (S^[k] x : ℚ) + 1) ^ 2)

/-- The normalization converting quadratic loss at n to squared word weight. -/
def visitConstant (n : ℕ) : ℚ :=
  (n : ℚ) ^ 2 * (3 * (n : ℚ) + 1) ^ 2 / (6 * (n : ℚ) + 1)

theorem visitConstant_nonneg (n : ℕ) : 0 ≤ visitConstant n := by
  unfold visitConstant
  positivity

theorem squareLoss_pos {x : ℕ} (hx : 0 < x) (k : ℕ) :
    0 < squareLoss x k := by
  have hn : (0 : ℚ) < (S^[k] x : ℚ) := by exact_mod_cast orbit_pos hx k
  have hw := weight_pos x k
  unfold squareLoss
  positivity

/-- Exact squared dissipation; no oddness or nonreturn hypothesis is needed. -/
theorem potential_sq_sub_succ {x : ℕ} (hx : 0 < x) (k : ℕ) :
    (potential x k) ^ 2 - (potential x (k + 1)) ^ 2 = squareLoss x k := by
  have hn : (0 : ℚ) < (S^[k] x : ℚ) := by exact_mod_cast orbit_pos hx k
  have ha : (0 : ℚ) < 3 * (S^[k] x : ℚ) + 1 := by positivity
  rw [potential_succ hx]
  unfold potential squareLoss
  field_simp
  ring

/-- The finite quadratic loss telescopes from time zero. -/
theorem sum_squareLoss_range {x : ℕ} (hx : 0 < x) (N : ℕ) :
    ∑ k ∈ Finset.range N, squareLoss x k =
      1 / (x : ℚ) ^ 2 - (potential x N) ^ 2 := by
  induction N with
  | zero => simp [potential, weight_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, ← potential_sq_sub_succ hx N]
      ring

/-- Any finite set of times spends at most the initial squared potential. -/
theorem sum_squareLoss_finset_le {x : ℕ} (hx : 0 < x) (H : Finset ℕ) :
    ∑ k ∈ H, squareLoss x k ≤ 1 / (x : ℚ) ^ 2 := by
  calc
    _ ≤ ∑ k ∈ Finset.range (H.sup id + 1), squareLoss x k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_range_sup_succ H)
        (fun k _ _ => le_of_lt (squareLoss_pos hx k))
    _ = 1 / (x : ℚ) ^ 2 - (potential x (H.sup id + 1)) ^ 2 :=
      sum_squareLoss_range hx _
    _ ≤ 1 / (x : ℚ) ^ 2 := sub_le_self _ (sq_nonneg _)

/-- A finite set of visits to a target, including repeated cyclic visits. -/
theorem sum_weight_sq_visits_le {x n : ℕ} (hx : 0 < x) (H : Finset ℕ)
    (hvisits : ∀ k ∈ H, S^[k] x = n) :
    ∑ k ∈ H, (weight x k) ^ 2 ≤ visitConstant n / (x : ℚ) ^ 2 := by
  have hfactor := visitConstant_nonneg n
  have hsum : (∑ k ∈ H, (weight x k) ^ 2) =
      visitConstant n * ∑ k ∈ H, squareLoss x k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hn : (0 : ℚ) < (S^[k] x : ℚ) := by exact_mod_cast orbit_pos hx k
    have hr : (0 : ℚ) < (n : ℚ) := by simpa [hvisits k hk] using hn
    have ha : (0 : ℚ) < 3 * (n : ℚ) + 1 := by positivity
    have hb : (0 : ℚ) < 6 * (n : ℚ) + 1 := by positivity
    unfold squareLoss visitConstant
    rw [hvisits k hk]
    field_simp
  rw [hsum]
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left (sum_squareLoss_finset_le hx H) hfactor

/-- Exact words from one source spend the same quadratic visit budget.
Distinct words have distinct lengths, even when the target has returns. -/
theorem sum_wordWeight_sq_fiber_le {x n : ℕ} (hx : 0 < x)
    (W : Finset (List ℕ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w x)
    (htarget : ∀ w ∈ W, evalSyracuseWord w x = n) :
    ∑ w ∈ W, (wordWeight w) ^ 2 ≤ visitConstant n / (x : ℚ) ^ 2 := by
  have hinj : ∀ w ∈ W, ∀ v ∈ W, w.length = v.length → w = v := by
    intro w hw v hv hlen
    exact matches_eq_of_length_eq (hmatch w hw) (hmatch v hv) hlen
  have hsum : (∑ w ∈ W, (wordWeight w) ^ 2) =
      ∑ k ∈ W.image List.length, (weight x k) ^ 2 := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro w hw
    rw [wordWeight_eq_weight_of_matches (hmatch w hw)]
  rw [hsum]
  apply sum_weight_sq_visits_le hx
  intro k hk
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
  rw [← evalSyracuseWord_eq_iterate_of_matches w x (hmatch w hw)]
  exact htarget w hw

/-- A finite catalogue with arbitrary repeated sources. No injectivity,
fixed depth, first-arrival or nonreturn assumption is required. -/
theorem tilted_catalogue_le (W : Finset (List ℕ))
    (source : List ℕ → ℕ) (n : ℕ)
    (hpos : ∀ w ∈ W, 0 < source w)
    (hm : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (he : ∀ w ∈ W, evalSyracuseWord w (source w) = n) :
    ∑ w ∈ W, (wordWeight w) ^ 2 ≤ 2 * visitConstant n := by
  have hgroup : (∑ w ∈ W, (wordWeight w) ^ 2) =
      ∑ u ∈ W.image source, ∑ w ∈ W with source w = u, (wordWeight w) ^ 2 := by
    rw [Finset.sum_fiberwise_of_maps_to
      (fun w hw => Finset.mem_image_of_mem source hw)]
  have hfiber (u : ℕ) (hu : u ∈ W.image source) :
      (∑ w ∈ W with source w = u, (wordWeight w) ^ 2) ≤
        visitConstant n / (u : ℚ) ^ 2 := by
    obtain ⟨v, hv, hsource⟩ := Finset.mem_image.mp hu
    have hu' : 0 < u := by rw [← hsource]; exact hpos v hv
    apply sum_wordWeight_sq_fiber_le hu'
    · intro w hw
      obtain ⟨hw', hwu⟩ := Finset.mem_filter.mp hw
      simpa only [hwu] using hm w hw'
    · intro w hw
      obtain ⟨hw', hwu⟩ := Finset.mem_filter.mp hw
      simpa only [hwu] using he w hw'
  rw [hgroup]
  calc
    _ ≤ ∑ u ∈ W.image source, visitConstant n / (u : ℚ) ^ 2 :=
      Finset.sum_le_sum hfiber
    _ = visitConstant n * ∑ u ∈ W.image source, (1 : ℚ) / (u : ℚ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ ≤ visitConstant n * 2 :=
      mul_le_mul_of_nonneg_left
        (IntegerAtomTilt.sum_reciprocal_sq_finset_le_two _)
        (visitConstant_nonneg n)
    _ = _ := by ring

end CollatzShadowing.QuadraticOccupation
