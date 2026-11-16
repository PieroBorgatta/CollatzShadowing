/-
Transfer of the universal weighted visit bound to exact Syracuse exponent
words. Distinct words following one starting value have distinct lengths;
therefore a word fiber can be counted as a finite set of orbit visits.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-24.
-/

import CollatzShadowing.WeightedVisits

namespace CollatzShadowing
namespace WeightedVisits

open scoped BigOperators

/-- Exact exponent words of the same length from the same state coincide. -/
theorem matches_eq_of_length_eq {w v : List ℕ} {x : ℕ}
    (hw : SyracuseWordMatchesFrom w x)
    (hv : SyracuseWordMatchesFrom v x)
    (hlen : w.length = v.length) : w = v := by
  induction w generalizing v x with
  | nil =>
      cases v with
      | nil => rfl
      | cons b rest => simp at hlen
  | cons a rest ih =>
      cases v with
      | nil => simp at hlen
      | cons b tail =>
          rcases hw with ⟨ha, hrest⟩
          rcases hv with ⟨hb, htail⟩
          have hab : a = b := ha.symm.trans hb
          have hrestlen : rest.length = tail.length := by simpa using hlen
          exact congrArg₂ List.cons hab (ih hrest htail hrestlen)

/-- Splitting an orbit exponent sum at its first step. -/
theorem exponentSum_succ_first (x k : ℕ) :
    exponentSum x (k + 1) = syracuseExponent x + exponentSum (S x) k := by
  induction k with
  | zero => simp [exponentSum]
  | succ k ih =>
      rw [exponentSum, ih, exponentSum]
      simp [Function.iterate_succ_apply, Nat.add_assoc]

/-- The sum recorded by an exact word is the exponent sum of the actual orbit. -/
theorem word_sum_eq_exponentSum {w : List ℕ} {x : ℕ}
    (hmatch : SyracuseWordMatchesFrom w x) :
    w.sum = exponentSum x w.length := by
  induction w generalizing x with
  | nil => simp [exponentSum]
  | cons a rest ih =>
      rcases hmatch with ⟨ha, hrest⟩
      simp only [List.sum_cons, List.length_cons, exponentSum_succ_first]
      rw [ha, ih hrest]

/-- Multiplicative affine weight associated with an exponent word. -/
def wordWeight (w : List ℕ) : ℚ := 3 ^ w.length / 2 ^ w.sum

theorem wordWeight_pos (w : List ℕ) : 0 < wordWeight w := by
  unfold wordWeight
  positivity

theorem wordWeight_nonneg (w : List ℕ) : 0 ≤ wordWeight w :=
  le_of_lt (wordWeight_pos w)

/-- On exact words, word weights agree with the weights of actual visits. -/
theorem wordWeight_eq_weight_of_matches {w : List ℕ} {x : ℕ}
    (hmatch : SyracuseWordMatchesFrom w x) :
    wordWeight w = weight x w.length := by
  simp only [wordWeight, weight, word_sum_eq_exponentSum hmatch]

/-- Universal bound for a finite fiber of distinct exact exponent words.
Repeated visits to the target, including visits on a cycle, are allowed.
The empty word is allowed as well. -/
theorem sum_wordWeight_fiber_le {x R : ℕ} (hx : 0 < x)
    (W : Finset (List ℕ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w x)
    (htarget : ∀ w ∈ W, evalSyracuseWord w x = R) :
    ∑ w ∈ W, wordWeight w ≤
      (R : ℚ) * (3 * (R : ℚ) + 1) / (x : ℚ) := by
  have hinj : ∀ w ∈ W, ∀ v ∈ W, w.length = v.length → w = v := by
    intro w hw v hv hlen
    exact matches_eq_of_length_eq (hmatch w hw) (hmatch v hv) hlen
  have hsum : ∑ w ∈ W, wordWeight w =
      ∑ k ∈ W.image List.length, weight x k := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro w hw
    exact wordWeight_eq_weight_of_matches (hmatch w hw)
  rw [hsum]
  apply sum_weight_visits_le hx
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨w, hw, rfl⟩
  rw [← evalSyracuseWord_eq_iterate_of_matches w x (hmatch w hw)]
  exact htarget w hw

end WeightedVisits
end CollatzShadowing
