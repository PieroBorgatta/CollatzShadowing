/-
Exact-word counting at a Syracuse target with no positive return. A source
can reach such a target at only one time, so its word fiber has at most one
member and total affine weight at most R/x. The resulting counting bound
uses K=R. Analytic mass and error estimates remain explicit hypotheses.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-24.
-/

import CollatzShadowing.TwoSeed
import CollatzShadowing.WeightedPredecessors

namespace CollatzShadowing
namespace NonreturnCounting

open scoped BigOperators

/-- Two visits to a target with no positive return occur at the same time. -/
theorem visit_time_eq_of_noReturn {x R k l : ℕ}
    (hNoReturn : TwoSeed.NoPositiveReturn R)
    (hk : S^[k] x = R) (hl : S^[l] x = R) : k = l := by
  have hle : ∀ {i j : ℕ}, S^[i] x = R → S^[j] x = R → i ≤ j → i = j := by
    intro i j hi hj hij
    by_contra hne
    have hpos : 0 < j - i := by omega
    apply hNoReturn (j - i) hpos
    calc
      S^[j - i] R = S^[j - i] (S^[i] x) := by rw [hi]
      _ = S^[j] x := by rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij]
      _ = R := hj
  rcases le_total k l with h | h
  · exact hle hk hl h
  · exact (hle hl hk h).symm

/-- Exact words from one source to a non-returning target are identical,
including the possibility of the empty word. -/
theorem matches_eq_of_target_eq {w v : List ℕ} {x R : ℕ}
    (hNoReturn : TwoSeed.NoPositiveReturn R)
    (hw : SyracuseWordMatchesFrom w x) (hv : SyracuseWordMatchesFrom v x)
    (hwt : evalSyracuseWord w x = R) (hvt : evalSyracuseWord v x = R) :
    w = v := by
  apply WeightedVisits.matches_eq_of_length_eq hw hv
  apply visit_time_eq_of_noReturn hNoReturn
  · exact (evalSyracuseWord_eq_iterate_of_matches w x hw).symm.trans hwt
  · exact (evalSyracuseWord_eq_iterate_of_matches v x hv).symm.trans hvt

/-- The nonnegative affine offset gives an individual word weight bound;
no non-return assumption is needed for this step. -/
theorem wordWeight_le_target_div {w : List ℕ} {x R : ℕ} (hx : 0 < x)
    (hmatch : SyracuseWordMatchesFrom w x) (htarget : evalSyracuseWord w x = R) :
    WeightedVisits.wordWeight w ≤ (R : ℚ) / (x : ℚ) := by
  have haff := evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w x hmatch
  rw [htarget] at haff
  have hnat : 3 ^ w.length * x ≤ R * 2 ^ w.sum := by
    rw [Nat.mul_comm R, haff]
    exact Nat.le_add_right _ _
  have hxq : (0 : ℚ) < x := by exact_mod_cast hx
  unfold WeightedVisits.wordWeight
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ w.sum) hxq).mpr
  exact_mod_cast hnat

/-- A finite fiber of exact words to a non-returning target contains at
most one word, and therefore has weight at most R/x. -/
theorem sum_wordWeight_fiber_le {x R : ℕ} (hx : 0 < x)
    (hNoReturn : TwoSeed.NoPositiveReturn R) (W : Finset (List ℕ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w x)
    (htarget : ∀ w ∈ W, evalSyracuseWord w x = R) :
    ∑ w ∈ W, WeightedVisits.wordWeight w ≤ (R : ℚ) / (x : ℚ) := by
  classical
  rcases W.eq_empty_or_nonempty with hW | ⟨w, hw⟩
  · simp only [hW, Finset.sum_empty]
    positivity
  · have hsingle : W = {w} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hw, fun v hv => matches_eq_of_target_eq hNoReturn
        (hmatch v hv) (hmatch w hw) (htarget v hv) (htarget w hw)⟩
    rw [hsingle, Finset.sum_singleton]
    exact wordWeight_le_target_div hx (hmatch w hw) (htarget w hw)

/-- The source map is injective on any such finite exact-word family. -/
theorem source_injOn (W : Finset (List ℕ)) (source : List ℕ → ℕ) {R : ℕ}
    (hNoReturn : TwoSeed.NoPositiveReturn R)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R) :
    Set.InjOn source (↑W : Set (List ℕ)) := by
  intro w hw v hv hsource
  exact matches_eq_of_target_eq hNoReturn (hmatch w hw)
    (by simpa only [← hsource] using hmatch v hv) (htarget w hw)
    (by simpa only [← hsource] using htarget v hv)

/-- Real-valued source-fiber estimate with the sharper multiplier K=R. -/
theorem word_fiber_bound (W : Finset (List ℕ)) (source : List ℕ → ℕ) (R : ℕ)
    (hNoReturn : TwoSeed.NoPositiveReturn R)
    (hpositive : ∀ w ∈ W, 0 < source w)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (x : ℕ) (hx : x ∈ W.image source) :
    ∑ w ∈ W.filter (fun w => source w = x), (WeightedVisits.wordWeight w : ℝ) ≤
      (R : ℝ) / (x : ℝ) := by
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
  have hq := sum_wordWeight_fiber_le hxpos hNoReturn
    (W.filter (fun w => source w = x)) hm ht
  have hreal := (Rat.cast_le (K := ℝ)).mpr hq
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_natCast] using hreal

theorem selected_fiber_bound (W : Finset (List ℕ)) (source : List ℕ → ℕ)
    (R : ℕ) (hNoReturn : TwoSeed.NoPositiveReturn R) (selected : List ℕ → ℝ)
    (hpositive : ∀ w ∈ W, 0 < source w)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (hselected : ∀ w ∈ W, selected w ≤ (WeightedVisits.wordWeight w : ℝ))
    (x : ℕ) (hx : x ∈ W.image source) :
    ∑ w ∈ W.filter (fun w => source w = x), selected w ≤ (R : ℝ) / (x : ℝ) := by
  calc
    _ ≤ ∑ w ∈ W.filter (fun w => source w = x), (WeightedVisits.wordWeight w : ℝ) :=
      Finset.sum_le_sum (fun w hw => hselected w (Finset.mem_filter.mp hw).1)
    _ ≤ _ := word_fiber_bound W source R hNoReturn hpositive hmatch htarget x hx

/-- The sharper source-count estimate for an explicitly assumed mass bound. -/
theorem distinct_sources_lower_bound
    (W : Finset (List ℕ)) (source : List ℕ → ℕ) {R : ℕ} (hR : 0 < R)
    (hNoReturn : TwoSeed.NoPositiveReturn R)
    (selected : List ℕ → ℝ) {X η : ℝ} (hX : 0 < X)
    (hsource : ∀ w ∈ W, X ≤ (source w : ℝ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (hselected : ∀ w ∈ W, selected w ≤ (WeightedVisits.wordWeight w : ℝ))
    (hmass : η ≤ ∑ w ∈ W, selected w) :
    η * X / (R : ℝ) ≤ ((W.image source).card : ℝ) := by
  have hpositive : ∀ w ∈ W, 0 < source w := by
    intro w hw
    exact_mod_cast lt_of_lt_of_le hX (hsource w hw)
  exact WeightedCounting.card_image_lower_bound W source selected
    (by exact_mod_cast hR) hX hsource
    (selected_fiber_bound W source R hNoReturn selected hpositive hmatch htarget hselected)
    hmass

/-- Count ordinary Collatz predecessors, using the existing exact bridge
from positive odd Syracuse sources to the ordinary Collatz map. -/
theorem ordinary_predecessor_count_of_mass
    (W : Finset (List ℕ)) (source : List ℕ → ℕ) {R : ℕ} (hR : 0 < R)
    (hNoReturn : TwoSeed.NoPositiveReturn R)
    (N : ℕ) (selected : List ℕ → ℝ) {X η : ℝ} (hX : 0 < X)
    (hsource : ∀ w ∈ W, X ≤ (source w : ℝ))
    (hodd : ∀ w ∈ W, Odd (source w))
    (hupper : ∀ w ∈ W, source w < N)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (hselected : ∀ w ∈ W, selected w ≤ (WeightedVisits.wordWeight w : ℝ))
    (hmass : η ≤ ∑ w ∈ W, selected w) :
    η * X / (R : ℝ) ≤ ((WeightedPredecessors.ordinaryPredecessorsBelow R N).card : ℝ) := by
  have hpositive : ∀ w ∈ W, 0 < source w := by
    intro w hw
    exact_mod_cast lt_of_lt_of_le hX (hsource w hw)
  have hcard := Finset.card_le_card
    (WeightedPredecessors.source_image_subset_predecessors W source R N
      hpositive hodd hupper hmatch htarget)
  exact (distinct_sources_lower_bound W source hR hNoReturn selected hX hsource hmatch
    htarget hselected hmass).trans (by exact_mod_cast hcard)

/-- A conditional quantitative predecessor count with K=R. The analytic
inequality, error budget and finite word family are inputs; this theorem
does not establish an unconditional density or termination statement. -/
theorem conditional_predecessor_count
    (W : Finset (List ℕ)) (source : List ℕ → ℕ) {R : ℕ} (hR : 0 < R)
    (hNoReturn : TwoSeed.NoPositiveReturn R)
    (N m : ℕ) (selected : List ℕ → ℝ) {X C : ℝ}
    (hX : 0 < X) (hscale : (N : ℝ) = 32 * X) (hm : 0 < m)
    (hsource : ∀ w ∈ W, X ≤ (source w : ℝ))
    (hodd : ∀ w ∈ W, Odd (source w))
    (hupper : ∀ w ∈ W, source w < N)
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w (source w))
    (htarget : ∀ w ∈ W, evalSyracuseWord w (source w) = R)
    (hselected : ∀ w ∈ W, selected w ≤ (WeightedVisits.wordWeight w : ℝ))
    (herror : 132 * (R : ℝ) * C ≤ (m : ℝ) ^ 2)
    (hestimate : (2 : ℝ) / 3 ≤
      (8 / 9 : ℝ) * 3 ^ m * (∑ w ∈ W, selected w) +
        44 * (R : ℝ) * C / (m : ℝ) ^ 2) :
    (3 / (256 * (R : ℝ) * (3 : ℝ) ^ m)) * (N : ℝ) ≤
      ((WeightedPredecessors.ordinaryPredecessorsBelow R N).card : ℝ) := by
  have hmass := WeightedCounting.mazur_main_term_lower_bound m hm herror hestimate
  have hcount := ordinary_predecessor_count_of_mass W source hR hNoReturn N selected hX
    hsource hodd hupper hmatch htarget hselected hmass
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hcoeff : (3 / (256 * (R : ℝ) * (3 : ℝ) ^ m)) * (N : ℝ) =
      (3 / (8 * (3 : ℝ) ^ m)) * X / (R : ℝ) := by
    rw [hscale]
    field_simp
    ring
  rw [hcoeff]
  exact hcount

end NonreturnCounting
end CollatzShadowing
