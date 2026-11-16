/-
An exact dissipation identity and a universal weighted bound for visits of
an accelerated Syracuse orbit. These bounds do not assert termination.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-24.
-/

import CollatzShadowing.CollatzBridge

namespace CollatzShadowing
namespace WeightedVisits

open scoped BigOperators

/-- The exponent removed in the first `k` accelerated steps. -/
def exponentSum (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => exponentSum x k + syracuseExponent (S^[k] x)

/-- The multiplicative part of the affine `k`-step Syracuse iterate. -/
def weight (x k : ℕ) : ℚ := 3 ^ k / 2 ^ exponentSum x k

/-- The remaining reciprocal potential along the actual orbit. -/
def potential (x k : ℕ) : ℚ := weight x k / (S^[k] x : ℚ)

/-- The exact potential lost at time `k`. -/
def loss (x k : ℕ) : ℚ :=
  weight x k / ((S^[k] x : ℚ) * (3 * (S^[k] x : ℚ) + 1))

theorem orbit_pos {x : ℕ} (hx : 0 < x) (k : ℕ) : 0 < S^[k] x := by
  cases k with
  | zero => simpa using hx
  | succ k => exact syracuse_iterate_succ_pos k x

theorem weight_pos (x k : ℕ) : 0 < weight x k := by
  unfold weight
  positivity

theorem weight_zero (x : ℕ) : weight x 0 = 1 := by
  simp [weight, exponentSum]

theorem weight_succ (x k : ℕ) :
    weight x (k + 1) =
      3 * weight x k / (2 : ℚ) ^ syracuseExponent (S^[k] x) := by
  unfold weight
  rw [exponentSum, pow_add, pow_succ]
  ring

theorem orbit_step (x k : ℕ) :
    (2 : ℚ) ^ syracuseExponent (S^[k] x) * (S^[k + 1] x : ℚ) =
      3 * (S^[k] x : ℚ) + 1 := by
  have h := pow_mul_syracuseStepWithExponent_eq_of_exponent
    (n := S^[k] x) rfl
  have hnat : 2 ^ syracuseExponent (S^[k] x) * S^[k + 1] x =
      3 * S^[k] x + 1 := by
    simpa [syracuseStepWithExponent, S, syracuseNumerator,
      Function.iterate_succ_apply'] using h
  exact_mod_cast hnat

/-- The factor `2^a` cancels exactly between weight and orbit state. -/
theorem potential_succ {x : ℕ} (hx : 0 < x) (k : ℕ) :
    potential x (k + 1) = 3 * weight x k / (3 * (S^[k] x : ℚ) + 1) := by
  have hn : (0 : ℚ) < (S^[k] x : ℚ) := by exact_mod_cast orbit_pos hx k
  have hm : (0 : ℚ) < (S^[k + 1] x : ℚ) := by
    exact_mod_cast orbit_pos hx (k + 1)
  have hd : (0 : ℚ) < 2 ^ syracuseExponent (S^[k] x) := by positivity
  have hstep := orbit_step x k
  unfold potential
  rw [weight_succ, ← hstep]
  field_simp

/-- Exact dissipation, including time zero and visits to the fixed point `1`. -/
theorem potential_sub_succ {x : ℕ} (hx : 0 < x) (k : ℕ) :
    potential x k - potential x (k + 1) = loss x k := by
  have hn : (0 : ℚ) < (S^[k] x : ℚ) := by exact_mod_cast orbit_pos hx k
  have ha : (0 : ℚ) < 3 * (S^[k] x : ℚ) + 1 := by positivity
  rw [potential_succ hx]
  unfold potential loss
  field_simp
  ring

theorem potential_pos {x : ℕ} (hx : 0 < x) (k : ℕ) :
    0 < potential x k := by
  have hn : (0 : ℚ) < (S^[k] x : ℚ) := by exact_mod_cast orbit_pos hx k
  exact div_pos (weight_pos x k) hn

theorem loss_pos {x : ℕ} (hx : 0 < x) (k : ℕ) : 0 < loss x k := by
  have hn : (0 : ℚ) < (S^[k] x : ℚ) := by exact_mod_cast orbit_pos hx k
  unfold loss
  exact div_pos (weight_pos x k) (by positivity)

/-- Telescoping of the exact loss along any finite initial orbit segment. -/
theorem sum_loss_range {x : ℕ} (hx : 0 < x) (N : ℕ) :
    ∑ k ∈ Finset.range N, loss x k = 1 / (x : ℚ) - potential x N := by
  induction N with
  | zero => simp [potential, weight_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, ← potential_sub_succ hx N]
      ring

theorem sum_loss_range_le {x : ℕ} (hx : 0 < x) (N : ℕ) :
    ∑ k ∈ Finset.range N, loss x k ≤ 1 / (x : ℚ) := by
  rw [sum_loss_range hx]
  exact sub_le_self _ (le_of_lt (potential_pos hx N))

/-- Every finite set of distinct times consumes at most the initial potential. -/
theorem sum_loss_finset_le {x : ℕ} (hx : 0 < x) (H : Finset ℕ) :
    ∑ k ∈ H, loss x k ≤ 1 / (x : ℚ) := by
  calc
    ∑ k ∈ H, loss x k ≤ ∑ k ∈ Finset.range (H.sup id + 1), loss x k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_range_sup_succ H)
        (fun k _ _ => le_of_lt (loss_pos hx k))
    _ ≤ 1 / (x : ℚ) := sum_loss_range_le hx _

/-- Universal weighted visit bound. No nonperiodicity or termination assumption
is needed, and `H` may contain time zero. -/
theorem sum_weight_visits_le {x R : ℕ} (hx : 0 < x) (H : Finset ℕ)
    (hvisits : ∀ k ∈ H, S^[k] x = R) :
    ∑ k ∈ H, weight x k ≤ (R : ℚ) * (3 * (R : ℚ) + 1) / (x : ℚ) := by
  have hfactor : (0 : ℚ) ≤ (R : ℚ) * (3 * (R : ℚ) + 1) := by positivity
  have hsum : (∑ k ∈ H, weight x k) =
      ((R : ℚ) * (3 * (R : ℚ) + 1)) * ∑ k ∈ H, loss x k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hn : (0 : ℚ) < (S^[k] x : ℚ) := by exact_mod_cast orbit_pos hx k
    have hr : (0 : ℚ) < (R : ℚ) := by simpa [hvisits k hk] using hn
    unfold loss
    rw [hvisits k hk]
    field_simp
  rw [hsum]
  simpa [div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left (sum_loss_finset_le hx H) hfactor

end WeightedVisits
end CollatzShadowing
