/-
Weighted counting for finite families of exact Syracuse predecessor words.
The source map need not be injective: repeated visits are controlled by
the universal occupation bound. No analytic mixing estimate is assumed
to have been established by this module.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-24.
-/

import CollatzShadowing.WeightedWords
import CollatzShadowing.WeightedCounting
import Mathlib.Data.Rat.BigOperators

namespace CollatzShadowing
namespace WeightedPredecessors

open scoped BigOperators

/-- Uniform multiplier in the weighted occupation bound at a fixed target. -/
def occupationConstant (R : ℕ) : ℝ := (R : ℝ) * (3 * (R : ℝ) + 1)

theorem occupationConstant_nonneg (R : ℕ) : 0 ≤ occupationConstant R := by
  unfold occupationConstant
  positivity

theorem occupationConstant_pos {R : ℕ} (hR : 0 < R) :
    0 < occupationConstant R := by
  unfold occupationConstant
  positivity

/-- A source fiber consists of exact paths on the same deterministic orbit.
Its total mass is bounded even when the target returns to itself. -/
theorem word_fiber_bound (W : Finset (List ℕ)) (source : List ℕ → ℕ) (R : ℕ)
    (hpositive : ∀ w ∈ W, 0 < source w)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (x : ℕ) (hx : x ∈ W.image source) :
    ∑ w ∈ W.filter (fun w => source w = x), (WeightedVisits.wordWeight w : ℝ) ≤
      occupationConstant R / (x : ℝ) := by
  have hxpos : 0 < x := by
    rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
    exact hpositive w hw
  have hm : ∀ w ∈ W.filter (fun w => source w = x), SyracuseWordMatchesFrom w x := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hw, heq⟩
    simpa only [heq] using hmatch w hw
  have ht : ∀ w ∈ W.filter (fun w => source w = x), evalSyracuseWord w x = R := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hw, heq⟩
    simpa only [heq] using htarget w hw
  have hq := WeightedVisits.sum_wordWeight_fiber_le hxpos
    (W.filter (fun w => source w = x)) hm ht
  unfold occupationConstant
  have hreal := (Rat.cast_le (K := ℝ)).mpr hq
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using hreal

/-- Selected nonnegative path weights may be smaller than the affine weights.
Only the upper comparison is needed for this fiber estimate. -/
theorem selected_fiber_bound (W : Finset (List ℕ)) (source : List ℕ → ℕ)
    (R : ℕ) (selected : List ℕ → ℝ)
    (hpositive : ∀ w ∈ W, 0 < source w)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (hselected : ∀ w ∈ W, selected w ≤ (WeightedVisits.wordWeight w : ℝ))
    (x : ℕ) (hx : x ∈ W.image source) :
    ∑ w ∈ W.filter (fun w => source w = x), selected w ≤
      occupationConstant R / (x : ℝ) := by
  calc
    _ ≤ ∑ w ∈ W.filter (fun w => source w = x), (WeightedVisits.wordWeight w : ℝ) :=
      Finset.sum_le_sum (fun w hw => hselected w (Finset.mem_filter.mp hw).1)
    _ ≤ _ := word_fiber_bound W source R hpositive hmatch htarget x hx

/-- Quantitative replacement for source injectivity in a weighted sum. -/
theorem selected_weighted_source_bound
    (W : Finset (List ℕ)) (source : List ℕ → ℕ) (R : ℕ)
    (selected : List ℕ → ℝ) {X : ℝ} (hX : 0 < X)
    (hsource : ∀ w ∈ W, X ≤ (source w : ℝ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (hselected : ∀ w ∈ W, selected w ≤ (WeightedVisits.wordWeight w : ℝ))
    (g : ℕ → ℝ) (hg : ∀ x ∈ W.image source, 0 ≤ g x) :
    (∑ w ∈ W, selected w * g (source w)) ≤
      (occupationConstant R / X) * ∑ x ∈ W.image source, g x := by
  have hpositive : ∀ w ∈ W, 0 < source w := by
    intro w hw
    exact_mod_cast lt_of_lt_of_le hX (hsource w hw)
  exact WeightedCounting.weighted_sum_le_image_sum W source selected
    (occupationConstant_nonneg R) hX hsource
    (selected_fiber_bound W source R selected hpositive hmatch htarget hselected) g hg

/-- Positive selected mass forces many distinct positive sources. -/
theorem distinct_sources_lower_bound
    (W : Finset (List ℕ)) (source : List ℕ → ℕ) {R : ℕ} (hR : 0 < R)
    (selected : List ℕ → ℝ) {X η : ℝ} (hX : 0 < X)
    (hsource : ∀ w ∈ W, X ≤ (source w : ℝ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (hselected : ∀ w ∈ W, selected w ≤ (WeightedVisits.wordWeight w : ℝ))
    (hmass : η ≤ ∑ w ∈ W, selected w) :
    η * X / occupationConstant R ≤ ((W.image source).card : ℝ) := by
  have hpositive : ∀ w ∈ W, 0 < source w := by
    intro w hw
    exact_mod_cast lt_of_lt_of_le hX (hsource w hw)
  exact WeightedCounting.card_image_lower_bound W source selected
    (occupationConstant_pos hR) hX hsource
    (selected_fiber_bound W source R selected hpositive hmatch htarget hselected) hmass

/-- Expand a finite odd-input Syracuse path to the ordinary Collatz map,
allowing an arbitrary target rather than just the target `1`. -/
theorem classical_hits_of_accelerated_hits {x R k : ℕ}
    (hodd : Odd x) (hhit : S^[k] x = R) :
    ∃ j : ℕ, collatzStep^[j] x = R := by
  induction k generalizing x with
  | zero => exact ⟨0, by simpa using hhit⟩
  | succ k ih =>
      have htail : S^[k] (S x) = R := by
        simpa [Function.iterate_succ, Function.comp_apply] using hhit
      obtain ⟨j, hj⟩ := ih (syracuse_odd x) htail
      exact ⟨j + (syracuseExponent x + 1), by
        rw [Function.iterate_add, Function.comp_apply,
          collatzStep_iterate_syracuse hodd, hj]⟩

/-- The mathematical finite predecessor set. Its membership predicate is
not asserted to be decidable by a terminating orbit search. -/
noncomputable def ordinaryPredecessorsBelow (R N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun x => 0 < x ∧ ∃ j, collatzStep^[j] x = R)

theorem source_image_subset_predecessors
    (W : Finset (List ℕ)) (source : List ℕ → ℕ) (R N : ℕ)
    (hpositive : ∀ w ∈ W, 0 < source w)
    (hodd : ∀ w ∈ W, Odd (source w))
    (hupper : ∀ w ∈ W, source w < N)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R) :
    W.image source ⊆ ordinaryPredecessorsBelow R N := by
  classical
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  have hhit : S^[w.length] (source w) = R := by
    rw [← evalSyracuseWord_eq_iterate_of_matches w (source w) (hmatch w hw)]
    exact htarget w hw
  simpa only [ordinaryPredecessorsBelow, Finset.mem_filter, Finset.mem_range] using
    And.intro (hupper w hw) (And.intro (hpositive w hw)
      (classical_hits_of_accelerated_hits (hodd w hw) hhit))

/-- A selected mass lower bound implies a count of actual ordinary Collatz
predecessors below a cutoff, without a no-return assumption. -/
theorem ordinary_predecessor_count_of_mass
    (W : Finset (List ℕ)) (source : List ℕ → ℕ) {R : ℕ} (hR : 0 < R)
    (N : ℕ) (selected : List ℕ → ℝ) {X η : ℝ} (hX : 0 < X)
    (hsource : ∀ w ∈ W, X ≤ (source w : ℝ))
    (hodd : ∀ w ∈ W, Odd (source w))
    (hupper : ∀ w ∈ W, source w < N)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (hselected : ∀ w ∈ W, selected w ≤ (WeightedVisits.wordWeight w : ℝ))
    (hmass : η ≤ ∑ w ∈ W, selected w) :
    η * X / occupationConstant R ≤ ((ordinaryPredecessorsBelow R N).card : ℝ) := by
  have hpositive : ∀ w ∈ W, 0 < source w := by
    intro w hw
    exact_mod_cast lt_of_lt_of_le hX (hsource w hw)
  have hcard := Finset.card_le_card
    (source_image_subset_predecessors W source R N hpositive hodd hupper hmatch htarget)
  exact (distinct_sources_lower_bound W source hR selected hX hsource hmatch
    htarget hselected hmass).trans (by exact_mod_cast hcard)

/-- The finite counting conclusion from an explicit analytic main-term/error
inequality. That inequality, its error budget, and the exact path family
are hypotheses, not results of this development. -/
theorem conditional_predecessor_count
    (W : Finset (List ℕ)) (source : List ℕ → ℕ) {R : ℕ} (hR : 0 < R)
    (N m : ℕ) (selected : List ℕ → ℝ) {X C : ℝ}
    (hX : 0 < X) (hscale : (N : ℝ) = 32 * X) (hm : 0 < m)
    (hsource : ∀ w ∈ W, X ≤ (source w : ℝ))
    (hodd : ∀ w ∈ W, Odd (source w))
    (hupper : ∀ w ∈ W, source w < N)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (hselected : ∀ w ∈ W, selected w ≤ (WeightedVisits.wordWeight w : ℝ))
    (herror : 132 * occupationConstant R * C ≤ (m : ℝ) ^ 2)
    (hestimate : (2 : ℝ) / 3 ≤
      (8 / 9 : ℝ) * 3 ^ m * (∑ w ∈ W, selected w) +
        44 * occupationConstant R * C / (m : ℝ) ^ 2) :
    (3 / (256 * occupationConstant R * (3 : ℝ) ^ m)) * (N : ℝ) ≤
      ((ordinaryPredecessorsBelow R N).card : ℝ) := by
  have hmass := WeightedCounting.mazur_main_term_lower_bound m hm herror hestimate
  have hcount := ordinary_predecessor_count_of_mass W source hR N selected hX
    hsource hodd hupper hmatch htarget hselected hmass
  have hK := occupationConstant_pos hR
  have hcoeff : (3 / (256 * occupationConstant R * (3 : ℝ) ^ m)) * (N : ℝ) =
      (3 / (8 * (3 : ℝ) ^ m)) * X / occupationConstant R := by
    rw [hscale]
    field_simp
    ring
  rw [hcoeff]
  exact hcount

end WeightedPredecessors
end CollatzShadowing
