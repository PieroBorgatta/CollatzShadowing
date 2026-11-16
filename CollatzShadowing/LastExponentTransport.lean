/-
Exact transport obtained by increasing the final Syracuse exponent, and
its unavoidable source-height cost. The congruence quotient is an explicit
input; no uniform density comparison or global termination is assumed.

Reference: notes/post_v6_basin_transport_2026-09-26/RESULTS_IT.md.
Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-26.
-/

import CollatzShadowing.ExactCylinders

namespace CollatzShadowing
namespace LastExponentTransport

/-- An exact odd affine endpoint certifies the actual valuations and value. -/
theorem matches_and_endpoint_of_affine (w : List ℕ) (x y : ℕ)
    (hw : w ≠ []) (hpos : ∀ a ∈ w, 0 < a) (hy : Odd y)
    (haff : 3 ^ w.length * x + syracuseWordConst w = 2 ^ w.sum * y) :
    SyracuseWordMatchesFrom w x ∧ evalSyracuseWord w x = y := by
  have hmatch : SyracuseWordMatchesFrom w x := by
    apply (syracuseWordMatches_iff_exactResidue w x hw hpos).mpr
    unfold syracuseWordAffineNumerator
    rw [haff, syracuseWordExactResidueModulus, pow_succ, Nat.mul_mod_mul_left]
    simp [Nat.odd_iff.mp hy]
  refine ⟨hmatch, ?_⟩
  have heq := evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w x hmatch
  rw [haff] at heq
  exact mul_left_cancel₀ (by positivity : (2 : ℕ) ^ w.sum ≠ 0) heq

/-- The affine constant is independent of the last exponent. -/
theorem last_constant_unchanged (w : List ℕ) (a b : ℕ) :
    syracuseWordConst (w ++ [a]) = syracuseWordConst (w ++ [b]) := by
  simp only [syracuseWordConst_append_singleton]

/-- A nonnegative congruence correction constructs a genuine new source.
All earlier exponents remain unchanged; this does not compare basin masses. -/
theorem last_exponent_transport (w : List ℕ) (a d x n y q : ℕ)
    (hw : ∀ b ∈ w, 0 < b) (ha : 0 < a) (hy : Odd y)
    (hmatch : SyracuseWordMatchesFrom (w ++ [a]) x)
    (htarget : evalSyracuseWord (w ++ [a]) x = n)
    (hcorrection : 2 ^ d * y = n + 3 ^ (w.length + 1) * q) :
    SyracuseWordMatchesFrom (w ++ [a + d]) (x + 2 ^ (w.sum + a) * q) ∧
      evalSyracuseWord (w ++ [a + d]) (x + 2 ^ (w.sum + a) * q) = y := by
  have hwordpos : ∀ b ∈ w ++ [a + d], 0 < b := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hw b hb
    · simp only [List.mem_singleton] at hb
      omega
  apply matches_and_endpoint_of_affine _ _ _ (by simp) hwordpos hy
  have hsource := evalSyracuseWord_mul_pow_sum_eq_affine_of_matches
    (w ++ [a]) x hmatch
  rw [htarget] at hsource
  simp only [List.sum_append, List.sum_singleton, List.length_append,
    List.length_singleton] at hsource ⊢
  rw [← last_constant_unchanged w a (a + d)]
  have hp : 2 ^ (w.sum + (a + d)) = 2 ^ (w.sum + a) * 2 ^ d := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp, mul_assoc, hcorrection]
  nlinarith

/-- Increasing the target forces a positive congruence quotient. -/
theorem correction_positive {d n y k q : ℕ} (hny : n < y)
    (hcorrection : 2 ^ d * y = n + 3 ^ k * q) : 0 < q := by
  have hp : 1 ≤ (2 : ℕ) ^ d := Nat.one_le_pow d 2 (by omega)
  have hge : y ≤ 2 ^ d * y := by nlinarith
  by_contra hq
  have hz : q = 0 := by omega
  simp only [hz, mul_zero, add_zero] at hcorrection
  omega

/-- Cross-multiplied strict height loss: x'/x > 1 + 3^k/n when x,n>0.
The statement uses natural arithmetic and retains the exact affine offset. -/
theorem transport_height_cost {k A C x n q : ℕ}
    (hC : 0 < C) (hq : 0 < q)
    (haff : 3 ^ k * x + C = 2 ^ A * n) :
    (n + 3 ^ k) * x < n * (x + 2 ^ A * q) := by
  have hp : 2 ^ A ≤ 2 ^ A * q := by
    exact Nat.le_mul_of_pos_right _ hq
  have hn : n * 2 ^ A ≤ n * (2 ^ A * q) := Nat.mul_le_mul_left n hp
  nlinarith

/-- Every positive source transported upward by this scheme pays the cost.
No hypothesis about the density, return time, or convergence is used. -/
theorem last_exponent_height_cost (w : List ℕ) (a d x n y q : ℕ)
    (hmatch : SyracuseWordMatchesFrom (w ++ [a]) x)
    (htarget : evalSyracuseWord (w ++ [a]) x = n) (hny : n < y)
    (hcorrection : 2 ^ d * y = n + 3 ^ (w.length + 1) * q) :
    (n + 3 ^ (w.length + 1)) * x <
      n * (x + 2 ^ (w.sum + a) * q) := by
  have hsource := evalSyracuseWord_mul_pow_sum_eq_affine_of_matches
    (w ++ [a]) x hmatch
  rw [htarget] at hsource
  simp only [List.sum_append, List.sum_singleton, List.length_append,
    List.length_singleton] at hsource
  exact transport_height_cost
    (syracuseWordConst_pos_of_ne_nil (by simp : w ++ [a] ≠ []))
    (correction_positive hny hcorrection) hsource.symm

/-- A proposed factor D cannot hold once the depth exceeds its arithmetic
budget. This only excludes the stated last-exponent transport scheme. -/
theorem not_bounded_height {k A C x n q D : ℕ}
    (hC : 0 < C) (hq : 0 < q)
    (haff : 3 ^ k * x + C = 2 ^ A * n)
    (hdepth : D * n ≤ n + 3 ^ k) :
    ¬ x + 2 ^ A * q ≤ D * x := by
  intro hbound
  have hcost := transport_height_cost hC hq haff
  have hleft := Nat.mul_le_mul_right x hdepth
  have hright := Nat.mul_le_mul_left n hbound
  nlinarith

end LastExponentTransport
end CollatzShadowing
