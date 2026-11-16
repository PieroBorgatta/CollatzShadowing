/-
Exact 2-adic progress across changes of phantom label.

The pair `(D,C)` represents the numerator `D*n+C`, i.e. 2-adic distance
from the formal negative point `-C/D`.  Suppose an actual Syracuse branch
sends `n` to `m` with exponent `e`:

  2^e * m = 3*n + 1.

If a source label `(D,C)` and a destination label `(D',C')` satisfy

  3*D' = q*D,      D' + 2^e*C' = q*C

for an odd rescaling `q`, then the corresponding numerators satisfy

  2^e * (D'*m+C') = q * (D*n+C).

Consequently their 2-adic precisions differ by exactly `e`.  This is a
switching trace law: the phantom label may change at every edge, including
normalization by odd factors, without resetting the progress counter.

The final theorem records the complementary obstruction.  If the shift `C`
may instead be chosen freely at a switch, then at any odd state one can make
`nu2(n+C)` equal any prescribed value.  Arbitrary "best phantom" relabeling
therefore cannot define a well-founded rank.
-/

import CollatzShadowing.CollatzBridge

namespace CollatzShadowing

/-- Numerator measuring 2-adic proximity to the formal point `-C/D`. -/
def switchingPhantomNumerator (D C n : ℕ) : ℕ :=
  D * n + C

/-- Natural 2-adic precision for a possibly changing affine phantom label. -/
def switchingPhantomPrecision (D C n : ℕ) : ℕ :=
  nu2Nat (switchingPhantomNumerator D C n)

/--
Algebraic core of a compatible phantom-label switch.

The odd factor `q` permits harmless renormalization of `(D,C)`.  Oddness is
not needed for this identity, but is used by the valuation theorem below.
-/
theorem switchingPhantom_scaled_identity
    {D C D' C' e q n m : ℕ}
    (hstep : 2 ^ e * m = 3 * n + 1)
    (hcoeff : 3 * D' = q * D)
    (hconst : D' + 2 ^ e * C' = q * C) :
    2 ^ e * switchingPhantomNumerator D' C' m
      =
    q * switchingPhantomNumerator D C n := by
  unfold switchingPhantomNumerator
  calc
    2 ^ e * (D' * m + C')
        = D' * (2 ^ e * m) + 2 ^ e * C' := by ring
    _ = D' * (3 * n + 1) + 2 ^ e * C' := by rw [hstep]
    _ = (3 * D') * n + (D' + 2 ^ e * C') := by ring
    _ = (q * D) * n + q * C := by rw [hcoeff, hconst]
    _ = q * (D * n + C) := by ring

/--
Exact precision loss across a compatible change of affine phantom label.

This is the edge-local trace condition needed by a cyclic certificate:
labels may switch, but the same numerator must be transported up to an odd
factor.
-/
theorem switchingPhantomPrecision_after_step_add_exponent
    {D C D' C' e q n m : ℕ}
    (hstep : 2 ^ e * m = 3 * n + 1)
    (hcoeff : 3 * D' = q * D)
    (hconst : D' + 2 ^ e * C' = q * C)
    (hq : Odd q)
    (hleft : switchingPhantomNumerator D' C' m ≠ 0)
    (hright : switchingPhantomNumerator D C n ≠ 0) :
    switchingPhantomPrecision D' C' m + e
      =
    switchingPhantomPrecision D C n := by
  have hscaled :=
    switchingPhantom_scaled_identity hstep hcoeff hconst
  have hq_ne : q ≠ 0 := by
    rcases hq with ⟨r, hr⟩
    omega
  have hq_not_dvd : ¬ 2 ∣ q := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr hdiv)
  have hq_val : padicValNat 2 q = 0 :=
    padicValNat.eq_zero_of_not_dvd hq_not_dvd
  unfold switchingPhantomPrecision nu2Nat
  calc
    padicValNat 2 (switchingPhantomNumerator D' C' m) + e
        =
      padicValNat 2
        (2 ^ e * switchingPhantomNumerator D' C' m) := by
          symm
          exact
            padicValNat_base_pow_mul
              (p := 2)
              (n := switchingPhantomNumerator D' C' m)
              (by norm_num) hleft e
    _ =
      padicValNat 2
        (q * switchingPhantomNumerator D C n) := by rw [hscaled]
    _ =
      padicValNat 2 q
        + padicValNat 2 (switchingPhantomNumerator D C n) := by
          exact padicValNat.mul hq_ne hright
    _ = padicValNat 2 (switchingPhantomNumerator D C n) := by
          rw [hq_val]
          omega

/-- Every positive-exponent compatible switch strictly consumes precision. -/
theorem switchingPhantomPrecision_after_step_lt
    {D C D' C' e q n m : ℕ}
    (hstep : 2 ^ e * m = 3 * n + 1)
    (hcoeff : 3 * D' = q * D)
    (hconst : D' + 2 ^ e * C' = q * C)
    (hq : Odd q)
    (he : 0 < e)
    (hleft : switchingPhantomNumerator D' C' m ≠ 0)
    (hright : switchingPhantomNumerator D C n ≠ 0) :
    switchingPhantomPrecision D' C' m
      <
    switchingPhantomPrecision D C n := by
  have htax :=
    switchingPhantomPrecision_after_step_add_exponent
      hstep hcoeff hconst hq hleft hright
  omega

/-! Concrete one-step switches behind the three shortest templates. -/

/-- The all-`1` phantom keeps label `1` and consumes one bit. -/
theorem switchingPrecision_one_to_one
    {n m : ℕ}
    (hstep : 2 * m = 3 * n + 1) :
    nu2Nat (m + 1) + 1 = nu2Nat (n + 1) := by
  simpa [switchingPhantomPrecision, switchingPhantomNumerator] using
    (switchingPhantomPrecision_after_step_add_exponent
      (D := 1) (C := 1) (D' := 1) (C' := 1)
      (e := 1) (q := 3) (n := n) (m := m)
      (by norm_num at hstep ⊢; exact hstep)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [switchingPhantomNumerator])
      (by simp [switchingPhantomNumerator]))

/-- The exponent-`1` edge switches the `[1,2]` label `5` to label `7`. -/
theorem switchingPrecision_five_to_seven
    {n m : ℕ}
    (hstep : 2 * m = 3 * n + 1) :
    nu2Nat (m + 7) + 1 = nu2Nat (n + 5) := by
  simpa [switchingPhantomPrecision, switchingPhantomNumerator] using
    (switchingPhantomPrecision_after_step_add_exponent
      (D := 1) (C := 5) (D' := 1) (C' := 7)
      (e := 1) (q := 3) (n := n) (m := m)
      (by norm_num at hstep ⊢; exact hstep)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [switchingPhantomNumerator])
      (by simp [switchingPhantomNumerator]))

/-- The exponent-`2` edge switches label `7` back to label `5`. -/
theorem switchingPrecision_seven_to_five
    {n m : ℕ}
    (hstep : 4 * m = 3 * n + 1) :
    nu2Nat (m + 5) + 2 = nu2Nat (n + 7) := by
  simpa [switchingPhantomPrecision, switchingPhantomNumerator] using
    (switchingPhantomPrecision_after_step_add_exponent
      (D := 1) (C := 7) (D' := 1) (C' := 5)
      (e := 2) (q := 3) (n := n) (m := m)
      (by norm_num at hstep ⊢; exact hstep)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [switchingPhantomNumerator])
      (by simp [switchingPhantomNumerator]))

/--
No-go for unconstrained phantom switching.

At an odd state `n`, choosing the new shift

  C_k = (2^k - 1) * n

makes `n + C_k = 2^k*n`, hence gives precision exactly `k`.  Thus a rank
which is allowed to reset `(D,C)` freely can jump to any requested height
without the orbit making progress.
-/
theorem arbitrary_phantom_shift_can_set_precision
    {n : ℕ} (hn : Odd n) (k : ℕ) :
    switchingPhantomPrecision 1 ((2 ^ k - 1) * n) n = k := by
  have hpow_pos : 0 < (2 : ℕ) ^ k :=
    pow_pos (by norm_num) k
  have hone : 1 ≤ 2 ^ k := by omega
  have hsum : 1 + (2 ^ k - 1) = 2 ^ k := by omega
  have hnum :
      switchingPhantomNumerator 1 ((2 ^ k - 1) * n) n
        = 2 ^ k * n := by
    unfold switchingPhantomNumerator
    calc
      1 * n + (2 ^ k - 1) * n
          = (1 + (2 ^ k - 1)) * n := by ring
      _ = 2 ^ k * n := by rw [hsum]
  unfold switchingPhantomPrecision
  rw [hnum, nu2Nat]
  exact padicValNat_two_pow_mul_odd hn

end CollatzShadowing
