/-
A conditional transfer certificate between quadratically related starts.
The relative weight inequality is an explicit hypothesis, not an invariant
proved here. In particular this file does not establish an induction on levels.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-25.
-/

import CollatzShadowing.DescentCertificate

namespace CollatzShadowing
namespace QuadraticTransfer

open WeightedVisits

/-- A relative bound on the two multiplicative weights controls the upper
homogeneous endpoint. The lower affine correction can only help the assumed
bound `w * X < N`. -/
theorem homogeneous_upper_bound {X N c w u : ℚ}
    (hN : 0 < N) (hNX : N ≤ X) (hc : 1 ≤ c)
    (hw : 0 < w) (hu : 0 ≤ u) (hlower : w * X < N)
    (hrelative : c * u ≤ 96 * w ^ 2) :
    u * (X + c * X ^ 2) < 96 * N ^ 2 + 96 * N := by
  have hX : 0 < X := lt_of_lt_of_le hN hNX
  have hwN : w * N ≤ w * X := mul_le_mul_of_nonneg_left hNX (le_of_lt hw)
  have hw1 : w < 1 := by
    apply (mul_lt_mul_iff_left₀ hN).mp
    simpa using lt_of_le_of_lt hwN hlower
  have huw : u ≤ 96 * w := by
    have hcu : u ≤ c * u := by
      simpa using mul_le_mul_of_nonneg_right hc hu
    have hwsq : w ^ 2 ≤ w := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left (le_of_lt hw1) (le_of_lt hw)
    exact le_trans (le_trans hcu hrelative)
      (mul_le_mul_of_nonneg_left hwsq (by norm_num))
  have hlinear : u * X ≤ 96 * (w * X) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right huw (le_of_lt hX)
  have hquadratic : u * c * X ^ 2 ≤ 96 * (w * X) ^ 2 := by
    calc
      u * c * X ^ 2 = (c * u) * X ^ 2 := by ring
      _ ≤ (96 * w ^ 2) * X ^ 2 :=
        mul_le_mul_of_nonneg_right hrelative (sq_nonneg X)
      _ = 96 * (w * X) ^ 2 := by ring
  have hsquare : (w * X) ^ 2 < N ^ 2 := by
    have hproduct : 0 < (N - w * X) * (N + w * X) :=
      mul_pos (sub_pos.mpr hlower) (by positivity)
    nlinarith
  nlinarith

/-- Rational form of the finite certificate; the weight is evaluated on the
actual upper orbit. -/
theorem exists_descent_of_weight {x N k : ℕ} (hx : 0 < x) (hN : 0 < N)
    (hk : k < 3 * N)
    (hcert : 3 * weight x k * (x : ℚ) < 3 * (N : ℚ) - k) :
    ∃ j ≤ k, S^[j] x < N := by
  apply DescentCertificate.exists_descent_of_certificate hx hN hk
  have hid : 3 * weight x k * (x : ℚ) =
      ((3 : ℚ) ^ (k + 1) * x) / 2 ^ exponentSum x k := by
    unfold weight
    rw [pow_succ]
    ring
  rw [hid] at hcert
  have hcross := (div_lt_iff₀ (by positivity :
    (0 : ℚ) < 2 ^ exponentSum x k)).mp hcert
  have hsub : ((3 * N - k : ℕ) : ℚ) = 3 * (N : ℚ) - k := by
    rw [Nat.cast_sub (le_of_lt hk)]
    push_cast
    rfl
  rw [← hsub] at hcross
  have hcast : (3 : ℚ) ^ (k + 1) * x <
      2 ^ exponentSum x k * ((3 * N - k : ℕ) : ℚ) := by
    simpa only [mul_comm] using hcross
  exact_mod_cast hcast

/-- A sufficient conditional transfer. The relative-weight bound and horizon
are assumptions, and no claim is made that every level admits such a time. -/
theorem exists_descent_of_relative_weight {X N c ell : ℕ} {w : ℚ}
    (hN : 0 < N) (hNX : N ≤ X) (hc : 1 ≤ c) (hw : 0 < w)
    (hlower : w * (X : ℚ) < N)
    (hrelative : (c : ℚ) * weight (X + c * X ^ 2) ell ≤ 96 * w ^ 2)
    (hell : ell ≤ N) :
    ∃ j ≤ ell, S^[j] (X + c * X ^ 2) < 96 * N ^ 2 + 704 * N + 1287 := by
  let Y := X + c * X ^ 2
  let M := 96 * N ^ 2 + 704 * N + 1287
  have hX : 0 < X := lt_of_lt_of_le hN hNX
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hNM : N ≤ M := by dsimp [M]; nlinarith
  have htime : ell < 3 * M := by omega
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hNXq : (N : ℚ) ≤ X := by exact_mod_cast hNX
  have hcq : (1 : ℚ) ≤ c := by exact_mod_cast hc
  have hellq : (ell : ℚ) ≤ N := by exact_mod_cast hell
  have hbound := homogeneous_upper_bound hNq hNXq hcq hw
    (le_of_lt (weight_pos Y ell)) hlower hrelative
  have hbound' : weight Y ell * (Y : ℚ) <
      96 * (N : ℚ) ^ 2 + 96 * N := by
    simpa only [Y, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using hbound
  apply exists_descent_of_weight hY hM htime
  have hMcast : (M : ℚ) = 96 * (N : ℚ) ^ 2 + 704 * N + 1287 := by
    dsimp [M]
    push_cast
    rfl
  rw [hMcast]
  nlinarith

/-- The same transfer starting from an actual descent of the lower orbit.
The new hypothesis still concerns the weight of the upper orbit. -/
theorem exists_descent_of_lower_descent {X N c k ell : ℕ}
    (hN : 0 < N) (hNX : N ≤ X) (hc : 1 ≤ c)
    (hlower : S^[k] X < N)
    (hrelative : (c : ℚ) * weight (X + c * X ^ 2) ell ≤
      96 * weight X k ^ 2)
    (hell : ell ≤ N) :
    ∃ j ≤ ell, S^[j] (X + c * X ^ 2) < 96 * N ^ 2 + 704 * N + 1287 := by
  have hX : 0 < X := lt_of_lt_of_le hN hNX
  have hXq : (0 : ℚ) < X := by exact_mod_cast hX
  have horbit : (0 : ℚ) < S^[k] X := by exact_mod_cast orbit_pos hX k
  have hpot := DescentCertificate.potential_le_initial hX k
  unfold potential at hpot
  have hcross := (div_le_div_iff₀ horbit hXq).mp hpot
  have hlin : weight X k * (X : ℚ) ≤ (S^[k] X : ℚ) := by
    simpa using hcross
  apply exists_descent_of_relative_weight hN hNX hc (weight_pos X k)
    (lt_of_le_of_lt hlin (by exact_mod_cast hlower)) hrelative hell

end QuadraticTransfer
end CollatzShadowing
