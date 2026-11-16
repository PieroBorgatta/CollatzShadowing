/-
A shared occupation budget for exact words with different endpoints.

The normalization is the exact dissipative loss.  No analytic lower mass
estimate, root-pool coverage, or comparison between basin densities is
asserted here.  Labels representing the same word must share a load budget.

AI-assisted development: Codex with Piero Borgatta, 2026-11-13.

The nonrecurrent-pool interface below is an independently proved local
integration of the root-pool mechanism described by Idris Ali Shaik in
CollatzConvergencePositiveDensity, commit
f0fda887ee60dc8ac4ef0d864935148b03734726, Roots/Antichain and Roots/PoolCharge.
No external source module or analytic theorem is imported.
-/

import CollatzShadowing.WeightedWords
import CollatzShadowing.WeightedCounting
import Mathlib.Data.Rat.BigOperators

namespace CollatzShadowing.RootPoolBudget

open scoped BigOperators
open WeightedVisits

/-- The word weight divided by its endpoint occupation constant. -/
def normalizedWeight (w : List ℕ) (x : ℕ) : ℚ :=
  wordWeight w / ((evalSyracuseWord w x : ℚ) *
    (3 * (evalSyracuseWord w x : ℚ) + 1))

theorem normalizedWeight_nonneg (w : List ℕ) (x : ℕ) :
    0 ≤ normalizedWeight w x := by
  unfold normalizedWeight
  exact div_nonneg (wordWeight_nonneg w) (by positivity)

/-- For an exact word the normalized weight is the loss at its actual time. -/
theorem normalizedWeight_eq_loss {w : List ℕ} {x : ℕ}
    (hmatch : SyracuseWordMatchesFrom w x) :
    normalizedWeight w x = loss x w.length := by
  unfold normalizedWeight loss
  rw [wordWeight_eq_weight_of_matches hmatch,
    evalSyracuseWord_eq_iterate_of_matches w x hmatch]

/-- Different exact words from one source have different lengths, so all
endpoints share one dissipative budget. Empty words and returns are allowed. -/
theorem sum_normalizedWeight_le {x : ℕ} (hx : 0 < x)
    (W : Finset (List ℕ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w x) :
    ∑ w ∈ W, normalizedWeight w x ≤ 1 / (x : ℚ) := by
  have hinj : ∀ w ∈ W, ∀ v ∈ W, w.length = v.length → w = v := by
    intro w hw v hv hlen
    exact matches_eq_of_length_eq (hmatch w hw) (hmatch v hv) hlen
  have hsum : ∑ w ∈ W, normalizedWeight w x =
      ∑ k ∈ W.image List.length, loss x k := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro w hw
    exact normalizedWeight_eq_loss (hmatch w hw)
  rw [hsum]
  exact sum_loss_finset_le hx _

/-- A pointwise selected submass has the same endpoint-independent budget. -/
theorem sum_selected_le {x : ℕ} (hx : 0 < x)
    (W : Finset (List ℕ)) (selected : List ℕ → ℚ)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w x)
    (hselected : ∀ w ∈ W, selected w ≤ normalizedWeight w x) :
    ∑ w ∈ W, selected w ≤ 1 / (x : ℚ) := by
  exact (Finset.sum_le_sum hselected).trans (sum_normalizedWeight_le hx W hmatch)

/-- Labels may duplicate words, provided their total coefficient per word
is at most M. A nonnegative coefficient hypothesis is unnecessary for this
upper bound; applications with probability allocations are a special case. -/
theorem sum_labeled_normalizedWeight_le {ι : Type*}
    {x : ℕ} (hx : 0 < x) (I : Finset ι)
    (word : ι → List ℕ) (coefficient : ι → ℚ) {M : ℚ} (hM : 0 ≤ M)
    (hmatch : ∀ i ∈ I, SyracuseWordMatchesFrom (word i) x)
    (hload : ∀ w ∈ I.image word,
      (∑ i ∈ I with word i = w, coefficient i) ≤ M) :
    ∑ i ∈ I, coefficient i * normalizedWeight (word i) x ≤ M / (x : ℚ) := by
  have hgroup : (∑ i ∈ I, coefficient i * normalizedWeight (word i) x) =
      ∑ w ∈ I.image word,
        (∑ i ∈ I with word i = w, coefficient i) * normalizedWeight w x := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem word hi)
      (fun i => coefficient i * normalizedWeight (word i) x)]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [hgroup]
  calc
    _ ≤ ∑ w ∈ I.image word, M * normalizedWeight w x := by
      apply Finset.sum_le_sum
      intro w hw
      exact mul_le_mul_of_nonneg_right (hload w hw) (normalizedWeight_nonneg w x)
    _ = M * ∑ w ∈ I.image word, normalizedWeight w x := by rw [Finset.mul_sum]
    _ ≤ M * (1 / (x : ℚ)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply sum_normalizedWeight_le hx
      intro w hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact hmatch i hi
    _ = M / (x : ℚ) := by ring

/-- The shared budget persists after grouping words by their actual source.
Different endpoints and repeated visits need no separate constants. -/
theorem normalized_source_fiber_bound (W : Finset (List ℕ))
    (source : List ℕ → ℕ)
    (hpositive : ∀ w ∈ W, 0 < source w)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (x : ℕ) (hx : x ∈ W.image source) :
    ∑ w ∈ W.filter (fun w => source w = x),
      (normalizedWeight w (source w) : ℝ) ≤ 1 / (x : ℝ) := by
  obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hx
  have hxpos : 0 < x := hvx ▸ hpositive v hv
  have hm : ∀ w ∈ W.filter (fun w => source w = x), SyracuseWordMatchesFrom w x := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hw, heq⟩
    simpa only [heq] using hmatch w hw
  have hq := sum_normalizedWeight_le hxpos (W.filter (fun w => source w = x)) hm
  have hreal := (Rat.cast_le (K := ℝ)).mpr hq
  have hsum :
      (∑ w ∈ W.filter (fun w => source w = x),
        (normalizedWeight w (source w) : ℝ)) =
      ∑ w ∈ W.filter (fun w => source w = x), (normalizedWeight w x : ℝ) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [(Finset.mem_filter.mp hw).2]
  rw [hsum]
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hreal

/-- A lower bound on the normalized selected mass yields distinct sources.
The lower mass estimate remains an explicit assumption of this theorem. -/
theorem distinct_sources_of_normalized_mass (W : Finset (List ℕ))
    (source : List ℕ → ℕ) (selected : List ℕ → ℝ)
    {X η : ℝ} (hX : 0 < X)
    (hsource : ∀ w ∈ W, X ≤ (source w : ℝ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (hselected : ∀ w ∈ W, selected w ≤ (normalizedWeight w (source w) : ℝ))
    (hmass : η ≤ ∑ w ∈ W, selected w) :
    η * X ≤ ((W.image source).card : ℝ) := by
  have hpositive : ∀ w ∈ W, 0 < source w := by
    intro w hw
    exact_mod_cast lt_of_lt_of_le hX (hsource w hw)
  have hfiber : ∀ x ∈ W.image source,
      (∑ w ∈ W with source w = x, selected w) ≤ 1 / (x : ℝ) := by
    intro x hx
    apply le_trans _ (normalized_source_fiber_bound W source hpositive hmatch x hx)
    apply Finset.sum_le_sum
    intro w hw
    exact hselected w (Finset.mem_filter.mp hw).1
  simpa using WeightedCounting.card_image_lower_bound W source selected
    (by norm_num : (0 : ℝ) < 1) hX hsource hfiber hmass

/-- A pool has no positive-time orbit connection, including a return to
the same member. This condition is stronger than separate nonreturn of
each root: it also excludes two distinct roots on one orbit. -/
def NonrecurrentPool {α : Type*} (f : α → α) (P : Set α) : Prop :=
  ∀ r ∈ P, ∀ k : ℕ, 0 < k → f^[k] r ∉ P

/-- Two visits to a nonrecurrent pool must have identical times. -/
theorem pool_visit_time_unique {α : Type*} {f : α → α} {P : Set α}
    (hP : NonrecurrentPool f P) {x : α} {i j : ℕ}
    (hi : f^[i] x ∈ P) (hj : f^[j] x ∈ P) : i = j := by
  by_contra hne
  have hord : i < j ∨ j < i := by omega
  rcases hord with hij | hji
  · apply hP _ hi (j - i) (Nat.sub_pos_of_lt hij)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hij)]
    exact hj
  · apply hP _ hj (i - j) (Nat.sub_pos_of_lt hji)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel (Nat.le_of_lt hji)]
    exact hi

/-- An exact word entering the pool is unique for a fixed source. -/
theorem word_eq_of_pool {P : Set ℕ} (hP : NonrecurrentPool S P)
    {w v : List ℕ} {x : ℕ}
    (hw : SyracuseWordMatchesFrom w x) (hv : SyracuseWordMatchesFrom v x)
    (hwP : evalSyracuseWord w x ∈ P) (hvP : evalSyracuseWord v x ∈ P) :
    w = v := by
  apply matches_eq_of_length_eq hw hv
  apply pool_visit_time_unique hP
  · simpa only [evalSyracuseWord_eq_iterate_of_matches w x hw] using hwP
  · simpa only [evalSyracuseWord_eq_iterate_of_matches v x hv] using hvP

/-- Reciprocal endpoint charge, stronger than the dissipative normalization
when nonrecurrence of the entire pool is available. -/
def reciprocalWeight (w : List ℕ) (x : ℕ) : ℚ :=
  wordWeight w / (evalSyracuseWord w x : ℚ)

/-- One exact path never spends more than the source reciprocal potential. -/
theorem reciprocalWeight_le_initial {w : List ℕ} {x : ℕ} (hx : 0 < x)
    (hmatch : SyracuseWordMatchesFrom w x) :
    reciprocalWeight w x ≤ 1 / (x : ℚ) := by
  have hsum : 0 ≤ ∑ k ∈ Finset.range w.length, loss x k := by
    exact Finset.sum_nonneg (fun k _ => le_of_lt (loss_pos hx k))
  rw [sum_loss_range hx] at hsum
  have hpot : potential x w.length ≤ 1 / (x : ℚ) := by linarith
  simpa only [reciprocalWeight, potential,
    wordWeight_eq_weight_of_matches hmatch,
    evalSyracuseWord_eq_iterate_of_matches w x hmatch] using hpot

/-- A finite catalogue of distinct exact words ending in a nonrecurrent
pool spends one reciprocal charge in total, independently of pool size.
The result proves an upper charge bound, not existence of root mass. -/
theorem sum_reciprocalWeight_pool_le {P : Set ℕ}
    (hP : NonrecurrentPool S P) {x : ℕ} (hx : 0 < x)
    (W : Finset (List ℕ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w x)
    (hroot : ∀ w ∈ W, evalSyracuseWord w x ∈ P) :
    ∑ w ∈ W, reciprocalWeight w x ≤ 1 / (x : ℚ) := by
  classical
  rcases W.eq_empty_or_nonempty with hW | ⟨w, hw⟩
  · simp [hW]
  · have hsingle : W = {w} := by
      apply Finset.ext
      intro v
      constructor
      · intro hv
        exact Finset.mem_singleton.mpr
          (word_eq_of_pool hP (hmatch v hv) (hmatch w hw) (hroot v hv) (hroot w hw))
      · intro hv
        simpa only [Finset.mem_singleton.mp hv] using hw
    rw [hsingle, Finset.sum_singleton]
    exact reciprocalWeight_le_initial hx (hmatch w hw)

/-- Metadata may label the same physical word more than once. An explicit
coefficient load per word preserves the sharp pool charge. -/
theorem sum_labeled_reciprocalWeight_pool_le {ι : Type*}
    {P : Set ℕ} (hP : NonrecurrentPool S P) {x : ℕ} (hx : 0 < x)
    (I : Finset ι) (word : ι → List ℕ) (coefficient : ι → ℚ)
    {M : ℚ} (hM : 0 ≤ M)
    (hmatch : ∀ i ∈ I, SyracuseWordMatchesFrom (word i) x)
    (hroot : ∀ i ∈ I, evalSyracuseWord (word i) x ∈ P)
    (hload : ∀ w ∈ I.image word,
      (∑ i ∈ I with word i = w, coefficient i) ≤ M) :
    ∑ i ∈ I, coefficient i * reciprocalWeight (word i) x ≤ M / (x : ℚ) := by
  have hgroup : (∑ i ∈ I, coefficient i * reciprocalWeight (word i) x) =
      ∑ w ∈ I.image word,
        (∑ i ∈ I with word i = w, coefficient i) * reciprocalWeight w x := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image_of_mem word hi)
      (fun i => coefficient i * reciprocalWeight (word i) x)]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [hgroup]
  calc
    _ ≤ ∑ w ∈ I.image word, M * reciprocalWeight w x := by
      apply Finset.sum_le_sum
      intro w hw
      apply mul_le_mul_of_nonneg_right (hload w hw)
      exact div_nonneg (wordWeight_nonneg w) (by positivity)
    _ = M * ∑ w ∈ I.image word, reciprocalWeight w x := by rw [Finset.mul_sum]
    _ ≤ M * (1 / (x : ℚ)) := by
      apply mul_le_mul_of_nonneg_left _ hM
      apply sum_reciprocalWeight_pool_le hP hx
      · intro w hw
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
        exact hmatch i hi
      · intro w hw
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
        exact hroot i hi
    _ = M / (x : ℚ) := by ring

end CollatzShadowing.RootPoolBudget
