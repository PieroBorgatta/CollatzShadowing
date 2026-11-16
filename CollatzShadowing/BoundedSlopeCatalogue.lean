/-
Finiteness of exact predecessor words with bounded homogeneous slope.

The reciprocal slope bound is wordWeight >= 1/R. The recurrent quadratic
occupation budget bounds the cardinality of every finite subcatalogue,
hence the full set is finite. Length and exponent-sum cutoffs are merely
existential; no algorithmic bound on hitting times is obtained.

Integer tilted budgets, including cyclic targets, were already public in
rStation paper 9/v1, Proposition 11. This is their finite set-theoretic
integration, not a priority claim for Green finiteness or the full recoding
obstruction. No S-unit inequality or asymptotic transport theorem is imported.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/

import CollatzShadowing.QuadraticOccupation
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Floor.Semiring

namespace CollatzShadowing.BoundedSlopeCatalogue

open WeightedVisits QuadraticOccupation RootPoolBudget
open scoped BigOperators

/-- Exact positive-source words ending at n, with reciprocal slope at most R.
Oddness, first arrival and nonreturn are not required. -/
def catalogue (n : ℕ) (R : ℚ) : Set (List ℕ) :=
  {w | ∃ u : ℕ, 0 < u ∧ SyracuseWordMatchesFrom w u ∧
    evalSyracuseWord w u = n ∧ 1 / R ≤ wordWeight w}

private noncomputable def source (n : ℕ) (R : ℚ) (w : List ℕ) : ℕ := by
  classical
  exact if h : w ∈ catalogue n R then Classical.choose h else 0

private theorem source_spec {n : ℕ} {R : ℚ} {w : List ℕ}
    (hw : w ∈ catalogue n R) :
    0 < source n R w ∧ SyracuseWordMatchesFrom w (source n R w) ∧
      evalSyracuseWord w (source n R w) = n ∧ 1 / R ≤ wordWeight w := by
  simpa only [source, dif_pos hw] using Classical.choose_spec hw

/-- Every finite subcatalogue has an explicit cardinality bound, with cycles
and arbitrarily many repeated source visits allowed. -/
theorem subcatalogue_card_le {n : ℕ} {R : ℚ} (hR : 0 < R)
    (W : Finset (List ℕ)) (hW : ∀ w ∈ W, w ∈ catalogue n R) :
    (W.card : ℚ) ≤ 2 * visitConstant n * R ^ 2 := by
  classical
  have hbudget := tilted_catalogue_le W (source n R) n
    (fun w hw => (source_spec (hW w hw)).1)
    (fun w hw => (source_spec (hW w hw)).2.1)
    (fun w hw => (source_spec (hW w hw)).2.2.1)
  have hterm (w : List ℕ) (hw : w ∈ W) :
      (1 : ℚ) ≤ (wordWeight w) ^ 2 * R ^ 2 := by
    have hwgt := (source_spec (hW w hw)).2.2.2
    have hmul : (1 : ℚ) ≤ wordWeight w * R := (div_le_iff₀ hR).mp hwgt
    nlinarith [sq_nonneg (wordWeight w * R - 1)]
  calc
    (W.card : ℚ) = ∑ _w ∈ W, (1 : ℚ) := by simp
    _ ≤ ∑ w ∈ W, (wordWeight w) ^ 2 * R ^ 2 := Finset.sum_le_sum hterm
    _ = (∑ w ∈ W, (wordWeight w) ^ 2) * R ^ 2 := by rw [Finset.sum_mul]
    _ ≤ 2 * visitConstant n * R ^ 2 :=
      mul_le_mul_of_nonneg_right hbudget (sq_nonneg R)

/-- The full set of bounded-slope exact words is finite, including periodic
targets. This does not give a computable maximum word length. -/
theorem catalogue_finite (n : ℕ) {R : ℚ} (hR : 0 < R) :
    (catalogue n R).Finite := by
  classical
  by_contra hnot
  have hinf : (catalogue n R).Infinite := hnot
  let B : ℚ := 2 * visitConstant n * R ^ 2
  obtain ⟨t, ht, htfin, htcard⟩ :=
    hinf.exists_subset_ncard_eq (Nat.ceil B + 1)
  have hW : ∀ w ∈ htfin.toFinset, w ∈ catalogue n R := by
    intro w hw
    exact ht (htfin.mem_toFinset.mp hw)
  have hb := subcatalogue_card_le hR htfin.toFinset hW
  have hc : htfin.toFinset.card = Nat.ceil B + 1 := by
    rw [← Set.ncard_eq_toFinset_card t htfin, htcard]
  rw [hc] at hb
  have hceil : B ≤ (Nat.ceil B : ℚ) := Nat.le_ceil B
  change ((Nat.ceil B + 1 : ℕ) : ℚ) ≤ B at hb
  push_cast at hb
  linarith

/-- The finite full catalogue inherits the same numerical cardinality bound.
This bounds its size, not the positions of its words in an enumeration. -/
theorem catalogue_ncard_le (n : ℕ) {R : ℚ} (hR : 0 < R) :
    ((catalogue n R).ncard : ℚ) ≤ 2 * visitConstant n * R ^ 2 := by
  classical
  have hfin := catalogue_finite n hR
  rw [Set.ncard_eq_toFinset_card _ hfin]
  apply subcatalogue_card_le hR
  intro w hw
  exact hfin.mem_toFinset.mp hw

/-- Finiteness yields length and total-exponent bounds only existentially.
No numerical cutoff or effective hitting-time assertion is supplied. -/
theorem catalogue_parameter_bounds (n : ℕ) {R : ℚ} (hR : 0 < R) :
    ∃ K A : ℕ, ∀ w ∈ catalogue n R, w.length ≤ K ∧ w.sum ≤ A := by
  have hfin := catalogue_finite n hR
  obtain ⟨K, hK⟩ := (hfin.image List.length).bddAbove
  obtain ⟨A, hA⟩ := (hfin.image (fun w : List ℕ => w.sum)).bddAbove
  refine ⟨K, A, ?_⟩
  intro w hw
  exact ⟨hK (Set.mem_image_of_mem List.length hw),
    hA (Set.mem_image_of_mem (fun w : List ℕ => w.sum) hw)⟩

/-- A bounded-slope word has a positive source at most R*n. This explicit
source bound is distinct from the existential time bounds above. -/
theorem catalogue_source_bound {n : ℕ} {R : ℚ} (hR : 0 < R)
    {w : List ℕ} (hw : w ∈ catalogue n R) :
    ∃ u : ℕ, 0 < u ∧ SyracuseWordMatchesFrom w u ∧
      evalSyracuseWord w u = n ∧ (u : ℚ) ≤ R * n := by
  obtain ⟨u, hu, hm, he, hwgt⟩ := hw
  refine ⟨u, hu, hm, he, ?_⟩
  have hn : 0 < n := by
    rw [← he, evalSyracuseWord_eq_iterate_of_matches w u hm]
    exact orbit_pos hu _
  have hu' : (0 : ℚ) < u := by exact_mod_cast hu
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hp := reciprocalWeight_le_initial hu hm
  rw [reciprocalWeight, he] at hp
  have hc : wordWeight w * (u : ℚ) ≤ n := by
    simpa only [one_mul] using (div_le_div_iff₀ hn' hu').mp hp
  have hmul := mul_le_mul_of_nonneg_right ((div_le_iff₀ hR).mp hwgt) hu'.le
  calc
    (u : ℚ) ≤ (wordWeight w * R) * u := by simpa only [one_mul] using hmul
    _ = (wordWeight w * u) * R := by ring
    _ ≤ (n : ℚ) * R := mul_le_mul_of_nonneg_right hc hR.le
    _ = R * n := by ring

end CollatzShadowing.BoundedSlopeCatalogue
