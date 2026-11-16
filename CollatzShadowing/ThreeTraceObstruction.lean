/-
An exact obstruction to a size-change argument based only on

  nu2Nat (n + 1), nu2Nat (n + 5), nu2Nat (n + 7).

The macro lasso `[1] ; [1, 2]` is the exponent word `[1, 1, 2]`.
Its affine map is `(27*n + 19)/16` and its formal 2-adic fixed point is
`-19/11`.  Natural integers can approach this point to arbitrary 2-adic
precision.  Along such an approach the three displayed precisions alternate

  (3, 2, 1) -> (2, 5, 1) -> (3, 2, 1),

while the omitted precision `nu2Nat (11*n + 19)` loses four bits per lasso.

The small recurrence below gives explicit natural approximants without a
search.
-/

import CollatzShadowing.SwitchingPrecision

namespace CollatzShadowing

/-- The three short-template precisions, in the order `1, 5, 7`. -/
def shortTraceTriple (n : ℕ) : ℕ × ℕ × ℕ :=
  (nu2Nat (n + 1), nu2Nat (n + 5), nu2Nat (n + 7))

/--
Multiplication by an odd natural does not change a finite 2-adic valuation;
this factorized form is convenient for the exact lasso calculations below.
-/
theorem nu2Nat_eq_of_odd_mul_eq_two_pow_mul_odd
    {q x k u : ℕ}
    (hq : Odd q) (hu : Odd u)
    (h : q * x = 2 ^ k * u) :
    nu2Nat x = k := by
  have hq_ne : q ≠ 0 := by
    rcases hq with ⟨v, hv⟩
    omega
  have hu_ne : u ≠ 0 := by
    rcases hu with ⟨v, hv⟩
    omega
  have hrhs_ne : 2 ^ k * u ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hu_ne
  have hx_ne : x ≠ 0 := by
    intro hx
    rw [hx, Nat.mul_zero] at h
    exact hrhs_ne h.symm
  have hq_not_dvd : ¬ 2 ∣ q := by
    intro hd
    exact (Nat.not_even_iff_odd.mpr hq) (even_iff_two_dvd.mpr hd)
  have hq_val : padicValNat 2 q = 0 :=
    padicValNat.eq_zero_of_not_dvd hq_not_dvd
  unfold nu2Nat
  have hv :
      padicValNat 2 (q * x) =
        padicValNat 2 (2 ^ k * u) := by rw [h]
  rw [padicValNat.mul hq_ne hx_ne, hq_val,
      padicValNat_two_pow_mul_odd hu] at hv
  omega

/--
An explicit tower of positive natural approximants to `-19/11`.

The recurrence raises the hidden precision by ten bits at a time.
-/
def threeTraceLassoSeed : ℕ → ℕ
  | 0 => 743
  | k + 1 => 1024 * threeTraceLassoSeed k + 1767

theorem threeTraceLassoSeed_invariant (k : ℕ) :
    11 * threeTraceLassoSeed k + 19 = 2 ^ (10 * k + 13) := by
  induction k with
  | zero =>
      norm_num [threeTraceLassoSeed]
  | succ k ih =>
      calc
        11 * threeTraceLassoSeed (k + 1) + 19
            = 1024 * (11 * threeTraceLassoSeed k + 19) := by
                simp only [threeTraceLassoSeed]
                ring
        _ = 1024 * 2 ^ (10 * k + 13) := by rw [ih]
        _ = 2 ^ (10 * (k + 1) + 13) := by
              rw [show 10 * (k + 1) + 13 = (10 * k + 13) + 10 by omega,
                  pow_add]
              norm_num
              ring

/--
Every sufficiently precise natural approximation to `-19/11` has the same
three short traces.  The odd multiplier `a` is intentionally arbitrary:
only the precision of the approximation matters.
-/
theorem shortTraceTriple_eq_boundary
    {a s n : ℕ}
    (ha : Odd a)
    (hnear : 11 * n + 19 = a * 2 ^ (s + 7)) :
    shortTraceTriple n = (3, 2, 1) := by
  have ha_pos : 0 < a := by
    rcases ha with ⟨v, hv⟩
    omega
  have hpow1 :
      a * 2 ^ (s + 7) = 8 * (a * 2 ^ (s + 4)) := by
    rw [show s + 7 = (s + 4) + 3 by omega, pow_add]
    norm_num
    ring
  have hpow5 :
      a * 2 ^ (s + 7) = 4 * (a * 2 ^ (s + 5)) := by
    rw [show s + 7 = (s + 5) + 2 by omega, pow_add]
    norm_num
    ring
  have hpow7 :
      a * 2 ^ (s + 7) = 2 * (a * 2 ^ (s + 6)) := by
    rw [show s + 7 = (s + 6) + 1 by omega, pow_add]
    norm_num
    ring
  have hu1 : Odd (a * 2 ^ (s + 4) - 1) := by
    refine ⟨a * 2 ^ (s + 3) - 1, ?_⟩
    have hsplit :
        a * 2 ^ (s + 4) = 2 * (a * 2 ^ (s + 3)) := by
      rw [show s + 4 = (s + 3) + 1 by omega, pow_add]
      norm_num
      ring
    have hpos : 1 ≤ a * 2 ^ (s + 3) := by
      have : 0 < a * 2 ^ (s + 3) :=
        Nat.mul_pos ha_pos (pow_pos (by norm_num) _)
      omega
    rw [hsplit]
    omega
  have hu5 : Odd (a * 2 ^ (s + 5) + 9) := by
    refine ⟨a * 2 ^ (s + 4) + 4, ?_⟩
    rw [show s + 5 = (s + 4) + 1 by omega, pow_add]
    norm_num
    ring
  have hu7 : Odd (a * 2 ^ (s + 6) + 29) := by
    refine ⟨a * 2 ^ (s + 5) + 14, ?_⟩
    rw [show s + 6 = (s + 5) + 1 by omega, pow_add]
    norm_num
    ring
  have h1 :
      11 * (n + 1) = 2 ^ 3 * (a * 2 ^ (s + 4) - 1) := by
    norm_num
    rw [hpow1] at hnear
    have hpos : 1 ≤ a * 2 ^ (s + 4) := by
      have : 0 < a * 2 ^ (s + 4) :=
        Nat.mul_pos ha_pos (pow_pos (by norm_num) _)
      omega
    omega
  have h5 :
      11 * (n + 5) = 2 ^ 2 * (a * 2 ^ (s + 5) + 9) := by
    norm_num
    rw [hpow5] at hnear
    omega
  have h7 :
      11 * (n + 7) = 2 ^ 1 * (a * 2 ^ (s + 6) + 29) := by
    norm_num
    rw [hpow7] at hnear
    omega
  unfold shortTraceTriple
  rw [nu2Nat_eq_of_odd_mul_eq_two_pow_mul_odd
        (by norm_num : Odd 11) hu1 h1,
      nu2Nat_eq_of_odd_mul_eq_two_pow_mul_odd
        (by norm_num : Odd 11) hu5 h5,
      nu2Nat_eq_of_odd_mul_eq_two_pow_mul_odd
        (by norm_num : Odd 11) hu7 h7]

theorem threeTraceLassoSeed_shortTraceTriple (k : ℕ) :
    shortTraceTriple (threeTraceLassoSeed k) = (3, 2, 1) := by
  apply shortTraceTriple_eq_boundary
      (a := 1) (s := 10 * k + 6)
  · norm_num
  · simpa [show (10 * k + 6) + 7 = 10 * k + 13 by omega] using
      threeTraceLassoSeed_invariant k

/--
The first explicit natural lasso segment.  It realizes the abstract trace
cycle `(3,2,1) -> (2,5,1) -> (3,2,1)` with exact Syracuse matches.
-/
theorem concrete_shortTrace_lasso :
    SyracuseWordMatchesFrom [1] 743
      ∧ evalSyracuseWord [1] 743 = 1115
      ∧ SyracuseWordMatchesFrom [1, 2] 1115
      ∧ evalSyracuseWord [1, 2] 1115 = 1255
      ∧ shortTraceTriple 743 = (3, 2, 1)
      ∧ shortTraceTriple 1115 = (2, 5, 1)
      ∧ shortTraceTriple 1255 = (3, 2, 1) := by
  have h743 :
      syracuseExponent 743 = 1 ∧ S 743 = 1115 := by
    apply syracuseStep_of_num_eq_two_pow_mul_odd
    · norm_num [syracuseNumerator]
    · exact ⟨557, by norm_num⟩
  have h1115 :
      syracuseExponent 1115 = 1 ∧ S 1115 = 1673 := by
    apply syracuseStep_of_num_eq_two_pow_mul_odd
    · norm_num [syracuseNumerator]
    · exact ⟨836, by norm_num⟩
  have h1673 :
      syracuseExponent 1673 = 2 ∧ S 1673 = 1255 := by
    apply syracuseStep_of_num_eq_two_pow_mul_odd
    · norm_num [syracuseNumerator]
    · exact ⟨627, by norm_num⟩
  have hmatch1 : SyracuseWordMatchesFrom [1] 743 := by
    exact ⟨h743.1, trivial⟩
  have hmatch12 : SyracuseWordMatchesFrom [1, 2] 1115 := by
    refine ⟨h1115.1, ?_⟩
    rw [h1115.2]
    exact ⟨h1673.1, trivial⟩
  have heval1 : evalSyracuseWord [1] 743 = 1115 := by
    calc
      evalSyracuseWord [1] 743 = S 743 := by
        simpa using evalSyracuseWord_eq_iterate_of_matches [1] 743 hmatch1
      _ = 1115 := h743.2
  have heval12 : evalSyracuseWord [1, 2] 1115 = 1255 := by
    have heval :=
      evalSyracuseWord_eq_iterate_of_matches [1, 2] 1115 hmatch12
    simpa [Function.iterate_succ_apply, h1115.2, h1673.2] using heval
  have ht743 : shortTraceTriple 743 = (3, 2, 1) := by
    simpa [threeTraceLassoSeed] using
      threeTraceLassoSeed_shortTraceTriple 0
  have ht1115 : shortTraceTriple 1115 = (2, 5, 1) := by
    have h1 : nu2Nat (1115 + 1) = 2 :=
      nu2Nat_eq_of_odd_mul_eq_two_pow_mul_odd
        (by norm_num : Odd 1) (by norm_num : Odd 279) (by norm_num)
    have h5 : nu2Nat (1115 + 5) = 5 :=
      nu2Nat_eq_of_odd_mul_eq_two_pow_mul_odd
        (by norm_num : Odd 1) (by norm_num : Odd 35) (by norm_num)
    have h7 : nu2Nat (1115 + 7) = 1 :=
      nu2Nat_eq_of_odd_mul_eq_two_pow_mul_odd
        (by norm_num : Odd 1) (by norm_num : Odd 561) (by norm_num)
    simp [shortTraceTriple, h1, h5, h7]
  have ht1255 : shortTraceTriple 1255 = (3, 2, 1) := by
    apply shortTraceTriple_eq_boundary
        (a := 27) (s := 2)
    · norm_num
    · norm_num
  exact
    ⟨hmatch1, heval1, hmatch12, heval12,
      ht743, ht1115, ht1255⟩

/-!
The compatible dynamic trace behind the same lasso.  These three identities
show why the lasso is an obstruction only for the short library
`C = 1,5,7`, not for compatible affine-label switching.
-/

theorem hiddenTrace_nineteen_to_twentyThree
    {n m : ℕ} (hstep : 2 * m = 3 * n + 1) :
    switchingPhantomPrecision 11 23 m + 1 =
      switchingPhantomPrecision 11 19 n := by
  apply switchingPhantomPrecision_after_step_add_exponent
      (D := 11) (C := 19) (D' := 11) (C' := 23)
      (e := 1) (q := 3) (n := n) (m := m)
  · simpa using hstep
  · norm_num
  · norm_num
  · norm_num
  · unfold switchingPhantomNumerator
    omega
  · unfold switchingPhantomNumerator
    omega

theorem hiddenTrace_twentyThree_to_twentyNine
    {n m : ℕ} (hstep : 2 * m = 3 * n + 1) :
    switchingPhantomPrecision 11 29 m + 1 =
      switchingPhantomPrecision 11 23 n := by
  apply switchingPhantomPrecision_after_step_add_exponent
      (D := 11) (C := 23) (D' := 11) (C' := 29)
      (e := 1) (q := 3) (n := n) (m := m)
  · simpa using hstep
  · norm_num
  · norm_num
  · norm_num
  · unfold switchingPhantomNumerator
    omega
  · unfold switchingPhantomNumerator
    omega

theorem hiddenTrace_twentyNine_to_nineteen
    {n m : ℕ} (hstep : 4 * m = 3 * n + 1) :
    switchingPhantomPrecision 11 19 m + 2 =
      switchingPhantomPrecision 11 29 n := by
  apply switchingPhantomPrecision_after_step_add_exponent
      (D := 11) (C := 29) (D' := 11) (C' := 19)
      (e := 2) (q := 3) (n := n) (m := m)
  · simpa using hstep
  · norm_num
  · norm_num
  · norm_num
  · unfold switchingPhantomNumerator
    omega
  · unfold switchingPhantomNumerator
    omega

/-- The compatible hidden precision loses exactly four bits per lasso. -/
theorem hiddenTrace_lasso_tax
    {n x y m : ℕ}
    (h₁ : 2 * x = 3 * n + 1)
    (h₂ : 2 * y = 3 * x + 1)
    (h₃ : 4 * m = 3 * y + 1) :
    switchingPhantomPrecision 11 19 m + 4 =
      switchingPhantomPrecision 11 19 n := by
  have h19 := hiddenTrace_nineteen_to_twentyThree h₁
  have h23 := hiddenTrace_twentyThree_to_twentyNine h₂
  have h29 := hiddenTrace_twentyNine_to_nineteen h₃
  omega

end CollatzShadowing
