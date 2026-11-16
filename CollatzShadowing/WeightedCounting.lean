/-
Finite weighted counting with controlled multiplicity. The fiber estimate is
an explicit hypothesis: no analytic estimate or Collatz termination statement
is assumed implicitly.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-24.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace CollatzShadowing
namespace WeightedCounting

open scoped BigOperators

variable {ι : Type*}

/-- Group a weighted sum by its distinct sources, without requiring the source
map to be injective. -/
theorem sum_grouped_by_source (W : Finset ι) (source : ι → ℕ)
    (mass : ι → ℝ) (g : ℕ → ℝ) :
    (∑ i ∈ W, mass i * g (source i)) =
      ∑ x ∈ W.image source, (∑ i ∈ W with source i = x, mass i) * g x := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_image_of_mem source hi) (fun i => mass i * g (source i))]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- A `K/x` bound on every fiber gives a `K/X` counting bound for sources
at least `X`. Only the test function needs to be nonnegative; the statement
also applies to signed masses satisfying the same fiber bound. -/
theorem weighted_sum_le_image_sum (W : Finset ι) (source : ι → ℕ)
    (mass : ι → ℝ) {K X : ℝ} (hK : 0 ≤ K) (hX : 0 < X)
    (hsource : ∀ i ∈ W, X ≤ (source i : ℝ))
    (hfiber : ∀ x ∈ W.image source,
      (∑ i ∈ W with source i = x, mass i) ≤ K / (x : ℝ))
    (g : ℕ → ℝ) (hg : ∀ x ∈ W.image source, 0 ≤ g x) :
    (∑ i ∈ W, mass i * g (source i)) ≤
      (K / X) * ∑ x ∈ W.image source, g x := by
  rw [sum_grouped_by_source, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact mul_le_mul_of_nonneg_right
    ((hfiber _ (Finset.mem_image_of_mem source hi)).trans
      (div_le_div_of_nonneg_left hK hX (hsource i hi)))
    (hg _ (Finset.mem_image_of_mem source hi))

/-- Total mass is bounded by the number of distinct sources times `K/X`. -/
theorem sum_mass_le_card_image (W : Finset ι) (source : ι → ℕ)
    (mass : ι → ℝ) {K X : ℝ} (hK : 0 ≤ K) (hX : 0 < X)
    (hsource : ∀ i ∈ W, X ≤ (source i : ℝ))
    (hfiber : ∀ x ∈ W.image source,
      (∑ i ∈ W with source i = x, mass i) ≤ K / (x : ℝ)) :
    (∑ i ∈ W, mass i) ≤ (K / X) * (W.image source).card := by
  simpa using weighted_sum_le_image_sum W source mass hK hX hsource hfiber
    (fun _ => 1) (by intro x hx; norm_num)

/-- Positive total mass yields a lower bound on distinct sources, even when
many indices have the same source. -/
theorem card_image_lower_bound (W : Finset ι) (source : ι → ℕ)
    (mass : ι → ℝ) {K X η : ℝ} (hK : 0 < K) (hX : 0 < X)
    (hsource : ∀ i ∈ W, X ≤ (source i : ℝ))
    (hfiber : ∀ x ∈ W.image source,
      (∑ i ∈ W with source i = x, mass i) ≤ K / (x : ℝ))
    (hmass : η ≤ ∑ i ∈ W, mass i) :
    η * X / K ≤ ((W.image source).card : ℝ) := by
  have hbound := hmass.trans
    (sum_mass_le_card_image W source mass hK.le hX hsource hfiber)
  apply (div_le_iff₀ hK).mpr
  have hmul := (le_div_iff₀ hX).mp
    (show η ≤ ((W.image source).card : ℝ) * K / X by
      simpa only [div_mul_eq_mul_div, mul_comm K] using hbound)
  exact hmul

/-- A selected or damped mass bounded pointwise by the original mass obeys the
same weighted counting estimate. Nonnegative selected weights are a special
case; no additional positivity hypothesis is needed here. -/
theorem weighted_sum_selected_le_image_sum (W : Finset ι) (source : ι → ℕ)
    (mass selected : ι → ℝ) {K X : ℝ} (hK : 0 ≤ K) (hX : 0 < X)
    (hsource : ∀ i ∈ W, X ≤ (source i : ℝ))
    (hfiber : ∀ x ∈ W.image source,
      (∑ i ∈ W with source i = x, mass i) ≤ K / (x : ℝ))
    (hselected : ∀ i ∈ W, selected i ≤ mass i)
    (g : ℕ → ℝ) (hg : ∀ x ∈ W.image source, 0 ≤ g x) :
    (∑ i ∈ W, selected i * g (source i)) ≤
      (K / X) * ∑ x ∈ W.image source, g x := by
  apply weighted_sum_le_image_sum W source selected hK hX hsource _ g hg
  intro x hx
  apply le_trans _ (hfiber x hx)
  apply Finset.sum_le_sum
  intro i hi
  exact hselected i (Finset.mem_filter.mp hi).1

/-- The lower bound also follows from a selected submass. -/
theorem card_image_selected_lower_bound (W : Finset ι) (source : ι → ℕ)
    (mass selected : ι → ℝ) {K X η : ℝ} (hK : 0 < K) (hX : 0 < X)
    (hsource : ∀ i ∈ W, X ≤ (source i : ℝ))
    (hfiber : ∀ x ∈ W.image source,
      (∑ i ∈ W with source i = x, mass i) ≤ K / (x : ℝ))
    (hselected : ∀ i ∈ W, selected i ≤ mass i)
    (hmass : η ≤ ∑ i ∈ W, selected i) :
    η * X / K ≤ ((W.image source).card : ℝ) := by
  apply card_image_lower_bound W source mass hK hX hsource hfiber
  exact hmass.trans (Finset.sum_le_sum hselected)

/-- Pure algebraic extraction of a main-term lower bound from the displayed
Mazur-type inequality. The analytic inequality and error threshold remain
explicit hypotheses; this theorem does not prove them. -/
theorem mazur_main_term_lower_bound {U K C : ℝ} (m : ℕ)
    (hm : 0 < m) (herror : 132 * K * C ≤ (m : ℝ) ^ 2)
    (hestimate : (2 : ℝ) / 3 ≤
      (8 / 9 : ℝ) * 3 ^ m * U + 44 * K * C / (m : ℝ) ^ 2) :
    3 / (8 * (3 : ℝ) ^ m) ≤ U := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hpow : (0 : ℝ) < 3 ^ m := by positivity
  have hsmall : 44 * K * C / (m : ℝ) ^ 2 ≤ (1 : ℝ) / 3 := by
    apply (div_le_iff₀ hm2).mpr
    linarith
  apply (div_le_iff₀ (show (0 : ℝ) < 8 * 3 ^ m by positivity)).mpr
  nlinarith

end WeightedCounting
end CollatzShadowing
