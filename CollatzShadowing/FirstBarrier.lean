/-
The exact first-barrier test for a finite accelerated Syracuse word.

For a matched word `w`, write

  M = 2^(sum(w)+1),   D = 2^sum(w) - 3^length(w),   C = C_w.

The extra bit in `M` is essential: divisibility by `2^sum(w)` only says
that the prescribed affine endpoint is integral, while congruence modulo
`2^(sum(w)+1)` also records that this endpoint is odd and hence that the
last prescribed valuation is exact.

If `r = n % M`, then `r ≤ n`.  On a contracting prefix (`D > 0`), the
strict inequality `C < D*r` therefore implies `C < D*n`, which is exactly
the affine inequality forcing the matched endpoint below its source.

This is the local arithmetic kernel of a possible first-barrier proof.  It
does not claim that every infinite exponent word eventually meets such a
barrier.
-/

import CollatzShadowing.CycleConstraints

namespace CollatzShadowing

/-- The dyadic modulus retaining integrality and oddness of a word endpoint. -/
def syracuseWordExactResidueModulus (w : List ℕ) : ℕ :=
  2 ^ (w.sum + 1)

/-- The positive affine denominator of a contracting finite word. -/
def syracuseWordBarrierDenominator (w : List ℕ) : ℕ :=
  2 ^ w.sum - 3 ^ w.length

/--
A matched nonempty word makes its affine numerator congruent to `2^sum(w)`
modulo `2^(sum(w)+1)`.  This is the exact extra-bit condition saying that
the endpoint after division by `2^sum(w)` is odd.
-/
theorem syracuseWordAffine_mod_exactResidueModulus_of_matches
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hlen : 0 < w.length) :
    (3 ^ w.length * n + syracuseWordConst w)
        % syracuseWordExactResidueModulus w
      = 2 ^ w.sum := by
  have haffine :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch
  have hodd := evalSyracuseWord_odd_of_matches hmatch hlen
  rcases hodd with ⟨k, hk⟩
  rw [← haffine, hk]
  simp only [syracuseWordExactResidueModulus, pow_add, pow_one]
  rw [Nat.mul_mod_mul_left]
  simp [Nat.add_mod]

/--
Exact residue-versus-barrier exclusion.

If the least nonnegative representative `r = n mod 2^(sum(w)+1)` already
lies strictly above the real affine barrier `C_w / D_w`, then the matched
word must end below its source.
-/
theorem evalSyracuseWord_lt_of_exactResidue_above_barrier
    {w : List ℕ} {n r : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hresidue : n % syracuseWordExactResidueModulus w = r)
    (hcontract : 3 ^ w.length < 2 ^ w.sum)
    (habove :
      syracuseWordConst w
        < syracuseWordBarrierDenominator w * r) :
    evalSyracuseWord w n < n := by
  have hdenpos : 0 < syracuseWordBarrierDenominator w := by
    unfold syracuseWordBarrierDenominator
    exact Nat.sub_pos_of_lt hcontract
  have hrle : r ≤ n := by
    rw [← hresidue]
    exact Nat.mod_le _ _
  have hscaled :
      syracuseWordBarrierDenominator w * r
        ≤ syracuseWordBarrierDenominator w * n :=
    Nat.mul_le_mul_left _ hrle
  have hC :
      syracuseWordConst w
        < syracuseWordBarrierDenominator w * n :=
    habove.trans_le hscaled
  apply evalSyracuseWord_lt_of_affine_contracting_of_matches hmatch
  unfold syracuseWordBarrierDenominator at hC
  rw [Nat.sub_mul] at hC
  omega

/--
Contrapositive form: a contracting matched prefix which has not dropped
forces its exact dyadic representative to remain at or below the barrier.
-/
theorem exactResidue_le_barrier_of_matched_nonDrop
    {w : List ℕ} {n r : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hresidue : n % syracuseWordExactResidueModulus w = r)
    (hcontract : 3 ^ w.length < 2 ^ w.sum)
    (hnondrop : n ≤ evalSyracuseWord w n) :
    syracuseWordBarrierDenominator w * r
      ≤ syracuseWordConst w := by
  by_contra h
  have habove :
      syracuseWordConst w
        < syracuseWordBarrierDenominator w * r := by
    omega
  have hdrop :=
    evalSyracuseWord_lt_of_exactResidue_above_barrier
      hmatch hresidue hcontract habove
  omega

/--
The signed barrier gap is exactly the signed displacement of the matched
endpoint, scaled by `2^sum(w)`.

This identity is an important limitation: evaluating the barrier at the
actual source is not an independent ranking argument; it is algebraically
equivalent to testing whether that source drops.
-/
theorem syracuseWordBarrierGapInt_eq_scaledDisplacement
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n) :
    ((((2 : ℤ) ^ w.sum - (3 : ℤ) ^ w.length) * (n : ℤ))
        - (syracuseWordConst w : ℤ))
      =
      (2 : ℤ) ^ w.sum
        * ((n : ℤ) - (evalSyracuseWord w n : ℤ)) := by
  have hnat :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch
  have hz :
      (2 : ℤ) ^ w.sum * (evalSyracuseWord w n : ℤ)
        =
        (3 : ℤ) ^ w.length * (n : ℤ)
          + (syracuseWordConst w : ℤ) := by
    exact_mod_cast hnat
  linarith

/--
On every matched word, the source-above-barrier inequality is
equivalent—not merely sufficient—to strict descent of the endpoint.  In the
noncontracting case the truncated natural denominator is zero and both sides
are false.
-/
theorem evalSyracuseWord_lt_iff_source_above_barrier
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n) :
    evalSyracuseWord w n < n
      ↔ syracuseWordConst w
          < syracuseWordBarrierDenominator w * n := by
  have haffine :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch
  constructor
  · intro hdrop
    have hpow : 0 < 2 ^ w.sum := pow_pos (by norm_num) _
    have hscaled :
        2 ^ w.sum * evalSyracuseWord w n
          < 2 ^ w.sum * n :=
      (Nat.mul_lt_mul_left hpow).2 hdrop
    rw [haffine] at hscaled
    unfold syracuseWordBarrierDenominator
    rw [Nat.sub_mul]
    omega
  · intro habove
    apply evalSyracuseWord_lt_of_affine_contracting_of_matches hmatch
    unfold syracuseWordBarrierDenominator at habove
    rw [Nat.sub_mul] at habove
    omega

end CollatzShadowing
