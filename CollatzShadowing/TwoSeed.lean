/-
Two distinct preimages of one point cannot both be periodic. For Syracuse,
the explicit lift n ↦ 4*n+1 preserves the next state, so a bounded pair of
positive odd candidates always contains a point with no positive return.
This is a non-return statement, not a proof of Collatz termination, and the
existence proof does not decide which member of the pair works.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-24.
-/

import CollatzShadowing.CollatzBridge
import Mathlib.Dynamics.PeriodicPts.Defs

namespace CollatzShadowing
namespace TwoSeed

/-- Distinct preimages cannot both be periodic, for any deterministic map. -/
theorem noReturn_or_noReturn_of_same_image
    {α : Type*} (f : α → α) {x y : α}
    (hne : x ≠ y) (himage : f x = f y) :
    (∀ k : ℕ, 0 < k → (f^[k]) x ≠ x) ∨
      (∀ k : ℕ, 0 < k → (f^[k]) y ≠ y) := by
  classical
  by_cases hx : ∀ k : ℕ, 0 < k → (f^[k]) x ≠ x
  · exact Or.inl hx
  · push Not at hx
    obtain ⟨p, hp, hpx⟩ := hx
    right
    intro q hq hqy
    have hxp : Function.IsPeriodicPt f p x := hpx
    have hyp : Function.IsPeriodicPt f q y := hqy
    exact hne (hxp.eq_of_apply_eq hyp hp hq himage)

/-- No positive Syracuse iterate returns to its starting state. -/
def NoPositiveReturn (n : ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → S^[k] n ≠ n

/-- An explicit increasing family of preimages of the same Syracuse state. -/
def lift (n : ℕ) : ℕ := 4 * n + 1

theorem lt_lift (n : ℕ) : n < lift n := by
  unfold lift
  omega

theorem lift_pos (n : ℕ) : 0 < lift n := by
  unfold lift
  omega

theorem lift_odd (n : ℕ) : Odd (lift n) := by
  exact ⟨2 * n, by unfold lift; omega⟩

/-- Multiplying `3*n+1` by four adds two to the removed exponent and leaves
the odd part unchanged. No parity or positivity assumption on `n` is needed. -/
theorem lift_exponent_and_step (n : ℕ) :
    syracuseExponent (lift n) = syracuseExponent n + 2 ∧ S (lift n) = S n := by
  have hbase : syracuseNumerator n = 2 ^ syracuseExponent n * S n := by
    have h := pow_mul_syracuseStepWithExponent_eq_of_exponent (n := n) rfl
    simpa only [syracuseStepWithExponent, S, syracuseNumerator] using h.symm
  apply syracuseStep_of_num_eq_two_pow_mul_odd _ (syracuse_odd n)
  calc
    syracuseNumerator (lift n) = 4 * syracuseNumerator n := by
      simp only [lift, syracuseNumerator]
      ring
    _ = 2 ^ (syracuseExponent n + 2) * S n := by
      rw [hbase, pow_add]
      norm_num
      ring

theorem lift_step (n : ℕ) : S (lift n) = S n :=
  (lift_exponent_and_step n).2

/-- One of the two explicit candidates has no positive return, even if the
common target lies on a cycle. -/
theorem two_seed_noReturn (n : ℕ) :
    NoPositiveReturn n ∨ NoPositiveReturn (lift n) :=
  noReturn_or_noReturn_of_same_image S (Nat.ne_of_lt (lt_lift n)) (lift_step n).symm

/-- With an odd positive starting candidate, both members of the bounded
pair are odd and positive. -/
theorem exists_nonreturn_seed {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    ∃ R : ℕ, (R = n ∨ R = lift n) ∧ n ≤ R ∧ R ≤ lift n ∧
      0 < R ∧ Odd R ∧ S R = S n ∧ NoPositiveReturn R := by
  rcases two_seed_noReturn n with h | h
  · exact ⟨n, Or.inl rfl, le_rfl, (lt_lift n).le, hn, hodd, rfl, h⟩
  · exact ⟨lift n, Or.inr rfl, (lt_lift n).le, le_rfl,
      lift_pos n, lift_odd n, lift_step n, h⟩

/-- All members of the lift family have the same Syracuse image. -/
theorem lift_iterate_step (n k : ℕ) : S (lift^[k] n) = S n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', lift_step, ih]

theorem lift_iterate_lower_bound (n k : ℕ) : n + k ≤ lift^[k] n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hgrowth := lt_lift (lift^[k] n)
      omega

theorem lift_iterate_succ_odd (n k : ℕ) : Odd (lift^[k + 1] n) := by
  rw [Function.iterate_succ_apply']
  exact lift_odd _

/-- Closed formula without natural-number division. -/
theorem lift_iterate_formula (n k : ℕ) :
    3 * lift^[k] n + 1 = 4 ^ k * (3 * n + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        3 * lift^[k + 1] n + 1 = 4 * (3 * lift^[k] n + 1) := by
          rw [Function.iterate_succ_apply']
          unfold lift
          ring
        _ = 4 * (4 ^ k * (3 * n + 1)) := by rw [ih]
        _ = 4 ^ (k + 1) * (3 * n + 1) := by rw [pow_succ]; ring

/-- Above every prescribed height, one of two adjacent explicit lifts is an
odd positive preimage with no positive return. The upper bound is explicit. -/
theorem exists_nonreturn_seed_above (n X : ℕ) :
    ∃ R : ℕ,
      (R = lift^[X + 1] n ∨ R = lift^[X + 2] n) ∧
      X < R ∧ R ≤ lift^[X + 2] n ∧ Odd R ∧
      S R = S n ∧ NoPositiveReturn R := by
  have hheight : X < lift^[X + 1] n := by
    have h := lift_iterate_lower_bound n (X + 1)
    omega
  have hnext : lift (lift^[X + 1] n) = lift^[X + 2] n := by
    exact (Function.iterate_succ_apply' lift (X + 1) n).symm
  rcases two_seed_noReturn (lift^[X + 1] n) with h | h
  · refine ⟨lift^[X + 1] n, Or.inl rfl, hheight, ?_,
      lift_iterate_succ_odd n X, lift_iterate_step n (X + 1), h⟩
    rw [← hnext]
    exact (lt_lift _).le
  · refine ⟨lift^[X + 2] n, Or.inr rfl, ?_, le_rfl,
      lift_iterate_succ_odd n (X + 1), lift_iterate_step n (X + 2), ?_⟩
    · rw [← hnext]
      exact hheight.trans (lt_lift _)
    · simpa only [hnext] using h

end TwoSeed
end CollatzShadowing
