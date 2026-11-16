/-
Arithmetic bounds for signed changes of the final Syracuse exponent.
These are finite affine and congruence statements. The distinct-image
density-zero theorem is a separate paper argument, not a Lean claim here.
Reference: notes/post_v6_signed_mass_2026-09-26/PROOF_IT.md.
Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-26.
-/

import CollatzShadowing.LastExponentTransport

namespace CollatzShadowing
namespace SignedTransport

/-- A common nonnegative affine offset increases relative expansion. -/
theorem affine_comparison {P R C x z s t : ℕ}
    (hP : 0 < P) (hx : P * x + C = R * s)
    (hz : P * z + C = R * t) (hst : s ≤ t) :
    t * x ≤ s * z := by
  have h1 := congrArg (fun a : ℕ => t * a) hx
  have h2 := congrArg (fun a : ℕ => s * a) hz
  have hc := Nat.mul_le_mul_right C hst
  nlinarith

/-- Distinct odd integers cannot differ by an integral power of two. -/
theorem odd_ne_two_pow_mul {n y : ℕ} (hn : Odd n) (hy : Odd y)
    (hne : n ≠ y) (d : ℕ) : n ≠ 2 ^ d * y := by
  cases d with
  | zero => simpa using hne
  | succ d =>
      intro heq
      have hmod := Nat.odd_iff.mp hn
      rw [heq] at hmod
      simp [pow_succ, Nat.mul_mod] at hmod

/-- A ternary congruence between distinct odd targets and a binary lift
must have at least one representative as large as its modulus. -/
theorem congruent_shift_requires_large {m n y d : ℕ}
    (hn : Odd n) (hy : Odd y) (hne : n ≠ y)
    (hmod : Nat.ModEq m n (2 ^ d * y)) :
    m ≤ max n (2 ^ d * y) := by
  by_contra h
  have hnlt : n < m := by omega
  have hylt : 2 ^ d * y < m := by omega
  have heq : n = 2 ^ d * y := by
    have hm := hmod
    change n % m = (2 ^ d * y) % m at hm
    simpa [Nat.mod_eq_of_lt hnlt, Nat.mod_eq_of_lt hylt] using hm
  exact odd_ne_two_pow_mul hn hy hne d heq

/-- Actual words differing by an increase in their final exponent obey
the multiplicative expansion bound whenever the scaled target increases. -/
theorem positive_shift_expands (w : List ℕ) (a d x z n y : ℕ)
    (hx : SyracuseWordMatchesFrom (w ++ [a]) x)
    (hz : SyracuseWordMatchesFrom (w ++ [a + d]) z)
    (hxn : evalSyracuseWord (w ++ [a]) x = n)
    (hzy : evalSyracuseWord (w ++ [a + d]) z = y)
    (hscale : n ≤ 2 ^ d * y) : 2 ^ d * y * x ≤ n * z := by
  have h1 := evalSyracuseWord_mul_pow_sum_eq_affine_of_matches (w ++ [a]) x hx
  have h2 := evalSyracuseWord_mul_pow_sum_eq_affine_of_matches (w ++ [a + d]) z hz
  rw [hxn] at h1
  rw [hzy, ← LastExponentTransport.last_constant_unchanged w a (a + d)] at h2
  simp only [List.sum_append, List.sum_singleton, List.length_append,
    List.length_singleton] at h1 h2
  have hp : 2 ^ (w.sum + (a + d)) = 2 ^ (w.sum + a) * 2 ^ d := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp, mul_assoc] at h2
  exact affine_comparison (by positivity) h1.symm h2.symm hscale

/-- Decreasing the final exponent sufficiently compresses source height.
This bounds distinct images even when arbitrarily many inputs collide. -/
theorem negative_shift_compresses (w : List ℕ) (a d x z n y : ℕ)
    (hx : SyracuseWordMatchesFrom (w ++ [a + d]) x)
    (hz : SyracuseWordMatchesFrom (w ++ [a]) z)
    (hxn : evalSyracuseWord (w ++ [a + d]) x = n)
    (hzy : evalSyracuseWord (w ++ [a]) z = y)
    (hscale : y ≤ 2 ^ d * n) : 2 ^ d * n * z ≤ y * x := by
  exact positive_shift_expands w a d z x y n hz hx hzy hxn hscale

/-- Multiplying both sources by their common dyadic part preserves
the cross-multiplied bound used for ordinary Collatz predecessors. -/
theorem lift_comparison {L R x z : ℕ} (h : L * x ≤ R * z) (e : ℕ) :
    L * (2 ^ e * x) ≤ R * (2 ^ e * z) := by
  have hm := Nat.mul_le_mul_left (2 ^ e) h
  nlinarith

end SignedTransport
end CollatzShadowing
