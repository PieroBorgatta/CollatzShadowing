/-
A sufficient finite descent certificate for the accelerated Syracuse map.
The conclusion is a visit below the threshold at or before the stated time;
it does not assert termination or that the final state is below the threshold.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-25.
-/

import CollatzShadowing.WeightedVisits

namespace CollatzShadowing
namespace DescentCertificate

open scoped BigOperators
open WeightedVisits

/-- Dissipation bounds the potential by its initial value. -/
theorem potential_le_initial {x : ℕ} (hx : 0 < x) (k : ℕ) :
    potential x k ≤ 1 / (x : ℚ) := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range k, loss x j := by
    exact Finset.sum_nonneg (fun j _ => le_of_lt (loss_pos hx j))
  rw [sum_loss_range hx] at hsum
  linarith

/-- Above a positive threshold, each loss is bounded by a fixed budget. -/
theorem loss_le_budget {x N k : ℕ} (hx : 0 < x) (hN : 0 < N)
    (hy : N ≤ S^[k] x) :
    loss x k ≤ 1 / (3 * (N : ℚ) * (x : ℚ)) := by
  have hxq : (0 : ℚ) < x := by exact_mod_cast hx
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hyq : (N : ℚ) ≤ S^[k] x := by exact_mod_cast hy
  have hpos : (0 : ℚ) < S^[k] x := by exact_mod_cast orbit_pos hx k
  have hpot := potential_le_initial hx k
  have hloss : loss x k = potential x k / (3 * (S^[k] x : ℚ) + 1) := by
    unfold loss potential
    rw [div_div]
  rw [hloss]
  calc
    potential x k / (3 * (S^[k] x : ℚ) + 1) ≤
        (1 / (x : ℚ)) / (3 * (S^[k] x : ℚ) + 1) := by
      exact div_le_div_of_nonneg_right hpot (by positivity)
    _ ≤ (1 / (x : ℚ)) / (3 * (N : ℚ)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    _ = 1 / (3 * (N : ℚ) * (x : ℚ)) := by ring

/-- If the orbit has stayed above `N`, the cumulative loss has a linear bound. -/
theorem potential_lower_bound {x N k : ℕ} (hx : 0 < x) (hN : 0 < N)
    (hstay : ∀ j < k, N ≤ S^[j] x) :
    (3 * (N : ℚ) - k) / (3 * (N : ℚ) * (x : ℚ)) ≤ potential x k := by
  have hxq : (0 : ℚ) < x := by exact_mod_cast hx
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hsum : ∑ j ∈ Finset.range k, loss x j ≤
      (k : ℚ) / (3 * (N : ℚ) * (x : ℚ)) := by
    calc
      ∑ j ∈ Finset.range k, loss x j ≤
          ∑ j ∈ Finset.range k, 1 / (3 * (N : ℚ) * (x : ℚ)) := by
        exact Finset.sum_le_sum (fun j hj =>
          loss_le_budget hx hN (hstay j (Finset.mem_range.mp hj)))
      _ = (k : ℚ) / (3 * (N : ℚ) * (x : ℚ)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  rw [sum_loss_range hx] at hsum
  have hid : (3 * (N : ℚ) - k) / (3 * (N : ℚ) * (x : ℚ)) =
      1 / (x : ℚ) - (k : ℚ) / (3 * (N : ℚ) * (x : ℚ)) := by
    field_simp
  rw [hid]
  linarith

/-- An integer certificate for a visit below `N` at or before time `k`.
The exponent sum is taken along the actual orbit; no estimate of the additive
term is omitted. -/
theorem exists_descent_of_certificate {x N k : ℕ} (hx : 0 < x) (hN : 0 < N)
    (hk : k < 3 * N)
    (hcert : 3 ^ (k + 1) * x < 2 ^ exponentSum x k * (3 * N - k)) :
    ∃ j ≤ k, S^[j] x < N := by
  by_contra hno
  push Not at hno
  have hxq : (0 : ℚ) < x := by exact_mod_cast hx
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hyq : (N : ℚ) ≤ S^[k] x := by exact_mod_cast hno k le_rfl
  have hlow := potential_lower_bound hx hN (fun j hj => hno j (le_of_lt hj))
  have hupp : potential x k ≤ weight x k / (N : ℚ) := by
    exact div_le_div_of_nonneg_left (le_of_lt (weight_pos x k)) hNq hyq
  have hbound := le_trans hlow hupp
  unfold weight at hbound
  rw [div_div] at hbound
  have hcross := (div_le_div_iff₀ (by positivity : (0 : ℚ) < 3 * N * x)
    (by positivity : (0 : ℚ) < 2 ^ exponentSum x k * N)).mp hbound
  have hsub : ((3 * N - k : ℕ) : ℚ) = 3 * (N : ℚ) - k := by
    rw [Nat.cast_sub (le_of_lt hk)]
    push_cast
    rfl
  have hcertq : (3 : ℚ) ^ (k + 1) * x <
      2 ^ exponentSum x k * ((3 * N - k : ℕ) : ℚ) := by
    exact_mod_cast hcert
  rw [hsub] at hcertq
  rw [pow_succ] at hcertq
  have hscaled := mul_lt_mul_of_pos_right hcertq hNq
  nlinarith

/-- A conservative horizon and a lower bound on the actual exponent sum also
give a certificate. The hypotheses concern this particular finite orbit;
the theorem supplies no automatic bound on that sum. -/
theorem exists_descent_of_budget {x N k K H : ℕ} (hx : 0 < x) (hN : 0 < N)
    (hk : k ≤ K) (hK : K < 3 * N) (hH : H ≤ exponentSum x k)
    (hcert : 3 ^ (K + 1) * x < 2 ^ H * (3 * N - K)) :
    ∃ j ≤ k, S^[j] x < N := by
  apply exists_descent_of_certificate hx hN (lt_of_le_of_lt hk hK)
  calc
    3 ^ (k + 1) * x ≤ 3 ^ (K + 1) * x := by
      exact Nat.mul_le_mul_right x
        (Nat.pow_le_pow_right (by decide : 1 ≤ (3 : ℕ)) (by omega))
    _ < 2 ^ H * (3 * N - K) := hcert
    _ ≤ 2 ^ exponentSum x k * (3 * N - k) := by
      exact Nat.mul_le_mul
        (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hH) (by omega)

end DescentCertificate
end CollatzShadowing
