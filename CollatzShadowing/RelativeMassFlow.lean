/-
Finite relative-mass transport with explicit image congestion.

This interface records the quantitative obligation suggested by the November
root-pool/fan-allocation review. It supplies no analytic lower mass estimate,
no comparison of asymptotic basin densities, and no termination theorem.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-11-13.
-/

import CollatzShadowing.WeightedCounting

namespace CollatzShadowing.RelativeMassFlow

open scoped BigOperators

variable {α β ι : Type*}

/-- A bound on every image's total incoming charge bounds the total flow.
The finite incidence relation must be supplied by the application. -/
theorem total_flow_le_capacity (U : Finset α) (V : Finset β)
    (q : α → β → ℝ) (M : ℝ)
    (hload : ∀ v ∈ V, ∑ u ∈ U, q u v ≤ M) :
    (∑ u ∈ U, ∑ v ∈ V, q u v) ≤ M * (V.card : ℝ) := by
  calc
    _ = ∑ v ∈ V, ∑ u ∈ U, q u v := Finset.sum_comm
    _ ≤ ∑ _v ∈ V, M := Finset.sum_le_sum hload
    _ = _ := by simp [mul_comm]

/-- A relative lower mass and bounded image congestion force distinct images.
The relative lower mass is an explicit, unproved input. -/
theorem relative_mass_le_image_capacity (U : Finset α) (V : Finset β)
    (q : α → β → ℝ) (η M E : ℝ)
    (hmass : η * (U.card : ℝ) - E ≤ ∑ u ∈ U, ∑ v ∈ V, q u v)
    (hload : ∀ v ∈ V, ∑ u ∈ U, q u v ≤ M) :
    η * (U.card : ℝ) - E ≤ M * (V.card : ℝ) :=
  hmass.trans (total_flow_le_capacity U V q M hload)

/-- Dividing by the positive load gives the distinct-image count. -/
theorem card_images_lower_bound (U : Finset α) (V : Finset β)
    (q : α → β → ℝ) (η M E : ℝ) (hM : 0 < M)
    (hmass : η * (U.card : ℝ) - E ≤ ∑ u ∈ U, ∑ v ∈ V, q u v)
    (hload : ∀ v ∈ V, ∑ u ∈ U, q u v ≤ M) :
    (η * (U.card : ℝ) - E) / M ≤ (V.card : ℝ) := by
  apply (div_le_iff₀ hM).mpr
  simpa only [mul_comm M] using
    relative_mass_le_image_capacity U V q η M E hmass hload

/-- At source scale X and image scale D*X, the net coefficient is η/(D*M).
This is finite algebra, not an asymptotic density assertion. -/
theorem scaled_card_images_lower_bound (U : Finset α) (V : Finset β)
    (q : α → β → ℝ) {η M E D X δ ε : ℝ}
    (hη : 0 ≤ η) (hM : 0 < M) (hD : 0 < D) (hX : 0 < X)
    (hbase : δ * X ≤ (U.card : ℝ)) (herror : E ≤ ε * X)
    (hmass : η * (U.card : ℝ) - E ≤ ∑ u ∈ U, ∑ v ∈ V, q u v)
    (hload : ∀ v ∈ V, ∑ u ∈ U, q u v ≤ M) :
    (η * δ - ε) / (D * M) ≤ (V.card : ℝ) / (D * X) := by
  have hbound := relative_mass_le_image_capacity U V q η M E hmass hload
  have hbase' := mul_le_mul_of_nonneg_left hbase hη
  apply (div_le_div_iff₀ (mul_pos hD hM) (mul_pos hD hX)).mpr
  have hnet : (η * δ - ε) * X ≤ M * (V.card : ℝ) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hnet hD.le]

/-- Pairwise disjoint finite image sets fit in a common finite cutoff. -/
theorem sum_card_disjoint_le [DecidableEq β] (I : Finset ι)
    (V : ι → Finset β) (A : Finset β)
    (hdisjoint : (↑I : Set ι).PairwiseDisjoint V)
    (hsub : ∀ i ∈ I, V i ⊆ A) :
    (∑ i ∈ I, ((V i).card : ℝ)) ≤ (A.card : ℝ) := by
  have hunion : I.biUnion V ⊆ A := by
    intro v hv
    obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hv
    exact hsub i hi hv
  have hc : (∑ i ∈ I, (V i).card) ≤ A.card := by
    rw [← Finset.card_biUnion hdisjoint]
    exact Finset.card_le_card hunion
  exact_mod_cast hc

/-- Combining relative flows into disjoint blocks gives one finite budget.
No limiting operation or uniform cutoff in infinitely many blocks is used. -/
theorem disjoint_block_flow_budget [DecidableEq β]
    (I : Finset ι) (U : Finset α) (V : ι → Finset β) (A : Finset β)
    (q : ι → α → β → ℝ) (η M : ℝ) (E : ι → ℝ) (hM : 0 ≤ M)
    (hdisjoint : (↑I : Set ι).PairwiseDisjoint V)
    (hsub : ∀ i ∈ I, V i ⊆ A)
    (hmass : ∀ i ∈ I,
      η * (U.card : ℝ) - E i ≤ ∑ u ∈ U, ∑ v ∈ V i, q i u v)
    (hload : ∀ i ∈ I, ∀ v ∈ V i, ∑ u ∈ U, q i u v ≤ M) :
    (I.card : ℝ) * η * (U.card : ℝ) - ∑ i ∈ I, E i ≤ M * (A.card : ℝ) := by
  have hsum : (∑ i ∈ I, (η * (U.card : ℝ) - E i)) ≤
      ∑ i ∈ I, M * ((V i).card : ℝ) := by
    apply Finset.sum_le_sum
    intro i hi
    exact relative_mass_le_image_capacity U (V i) (q i) η M (E i)
      (hmass i hi) (hload i hi)
  have hpack := mul_le_mul_of_nonneg_left (sum_card_disjoint_le I V A hdisjoint hsub) hM
  calc
    _ = ∑ i ∈ I, (η * (U.card : ℝ) - E i) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ i ∈ I, M * ((V i).card : ℝ) := hsum
    _ = M * ∑ i ∈ I, ((V i).card : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ M * (A.card : ℝ) := hpack

end CollatzShadowing.RelativeMassFlow
