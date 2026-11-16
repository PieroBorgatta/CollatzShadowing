/-
Exact precision loss near an expansive periodic Syracuse phantom.

For a prescribed exponent word `w`, write

  P = 3 ^ w.length,
  Q = 2 ^ w.sum,
  C = syracuseWordConst w,
  D = P - Q.

If `P > Q` and the word sends `n` to `m`, then

  Q * (D * m + C) = P * (D * n + C).

Since `P` is odd, the 2-adic valuation of the positive integer
`D * n + C` therefore loses exactly `w.sum` under one application of
the word. This is the arithmetic "precision tax" behind a cyclic
termination certificate for repetitions of an expansive phantom word.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-07-23.
-/

import CollatzShadowing.CollatzBridge

namespace CollatzShadowing

/-- Positive real-growth defect of an expansive exponent word. -/
def syracuseWordExpansionDefect (w : List ℕ) : ℕ :=
  3 ^ w.length - 2 ^ w.sum

/--
Integer numerator measuring 2-adic proximity to the negative formal fixed
point of an expansive word.

When `3^length > 2^sum`, the fixed point is
`-syracuseWordConst w / syracuseWordExpansionDefect w`; its denominator is
odd, so this natural-number numerator has the same 2-adic precision.
-/
def syracuseWordPhantomPrecisionNumerator (w : List ℕ) (n : ℕ) : ℕ :=
  syracuseWordExpansionDefect w * n + syracuseWordConst w

/-- The natural-valued 2-adic precision attached to an expansive word. -/
def syracuseWordPhantomPrecision (w : List ℕ) (n : ℕ) : ℕ :=
  nu2Nat (syracuseWordPhantomPrecisionNumerator w n)

/--
Core integer precision-tax identity.

This version deliberately assumes only the affine endpoint identity, so it
can be reused by certificate checkers that have already established their
word semantics by another route.
-/
theorem syracuseWord_precisionTax_scaled_identity_of_affine
    {w : List ℕ} {n m : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (haff :
      2 ^ w.sum * m =
        3 ^ w.length * n + syracuseWordConst w) :
    2 ^ w.sum *
        syracuseWordPhantomPrecisionNumerator w m
      =
    3 ^ w.length *
        syracuseWordPhantomPrecisionNumerator w n := by
  let P : ℕ := 3 ^ w.length
  let Q : ℕ := 2 ^ w.sum
  let C : ℕ := syracuseWordConst w
  let D : ℕ := P - Q
  have hDQ : D + Q = P := by
    exact Nat.sub_add_cancel (Nat.le_of_lt hexp)
  have haff' : Q * m = P * n + C := by
    simpa [P, Q, C] using haff
  change Q * (D * m + C) = P * (D * n + C)
  calc
    Q * (D * m + C) = D * (Q * m) + Q * C := by ring
    _ = D * (P * n + C) + Q * C := by rw [haff']
    _ = D * P * n + (D + Q) * C := by ring
    _ = D * P * n + P * C := by rw [hDQ]
    _ = P * (D * n + C) := by ring

/--
The precision-tax identity for an actually matched Syracuse exponent word.
-/
theorem syracuseWord_precisionTax_scaled_identity_of_matches
    {w : List ℕ} {n : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (hmatch : SyracuseWordMatchesFrom w n) :
    2 ^ w.sum *
        syracuseWordPhantomPrecisionNumerator w
          (evalSyracuseWord w n)
      =
    3 ^ w.length *
        syracuseWordPhantomPrecisionNumerator w n :=
  syracuseWord_precisionTax_scaled_identity_of_affine
    hexp
    (evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch)

/--
Exact valuation form of the precision tax.

One matched application of an expansive word consumes exactly `w.sum`
bits of 2-adic precision relative to its negative periodic phantom.
-/
theorem syracuseWordPhantomPrecision_after_eval_add_sum
    {w : List ℕ} {n : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (hmatch : SyracuseWordMatchesFrom w n) :
    syracuseWordPhantomPrecision w (evalSyracuseWord w n) + w.sum
      =
    syracuseWordPhantomPrecision w n := by
  have hw : w ≠ [] := by
    intro hw
    subst w
    simp at hexp
  have hCpos : 0 < syracuseWordConst w :=
    syracuseWordConst_pos_of_ne_nil hw
  have hleft_ne :
      syracuseWordPhantomPrecisionNumerator w
          (evalSyracuseWord w n) ≠ 0 := by
    unfold syracuseWordPhantomPrecisionNumerator
    omega
  have hright_ne :
      syracuseWordPhantomPrecisionNumerator w n ≠ 0 := by
    unfold syracuseWordPhantomPrecisionNumerator
    omega
  have hP_ne : 3 ^ w.length ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  have hPodd : Odd (3 ^ w.length) := by
    exact Odd.pow (by norm_num)
  have hPnotdvd : ¬ 2 ∣ 3 ^ w.length := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hPodd) (even_iff_two_dvd.mpr hdiv)
  have hPval : padicValNat 2 (3 ^ w.length) = 0 :=
    padicValNat.eq_zero_of_not_dvd hPnotdvd
  have hscaled :=
    syracuseWord_precisionTax_scaled_identity_of_matches hexp hmatch
  unfold syracuseWordPhantomPrecision nu2Nat
  calc
    padicValNat 2
          (syracuseWordPhantomPrecisionNumerator w
            (evalSyracuseWord w n))
        + w.sum
        =
      padicValNat 2
        (2 ^ w.sum *
          syracuseWordPhantomPrecisionNumerator w
            (evalSyracuseWord w n)) := by
          symm
          exact
            padicValNat_base_pow_mul
              (p := 2)
              (n :=
                syracuseWordPhantomPrecisionNumerator w
                  (evalSyracuseWord w n))
              (by norm_num) hleft_ne w.sum
    _ =
      padicValNat 2
        (3 ^ w.length *
          syracuseWordPhantomPrecisionNumerator w n) := by
          rw [hscaled]
    _ =
      padicValNat 2 (3 ^ w.length)
        + padicValNat 2
            (syracuseWordPhantomPrecisionNumerator w n) := by
          exact padicValNat.mul hP_ne hright_ne
    _ =
      padicValNat 2
        (syracuseWordPhantomPrecisionNumerator w n) := by
          rw [hPval]
          omega

/--
Telescoped precision tax for `k` consecutive matched copies of the same
expansive word.

Unlike a congruence-at-all-depths argument, this theorem follows the actual
finite word evaluator and records the exact remaining precision after every
matched block.
-/
theorem syracuseWordPhantomPrecision_after_iterate_add_mul_sum
    {w : List ℕ} {n k : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (hmatch :
      ∀ i < k,
        SyracuseWordMatchesFrom w
          ((evalSyracuseWord w)^[i] n)) :
    syracuseWordPhantomPrecision w
          ((evalSyracuseWord w)^[k] n)
        + k * w.sum
      =
    syracuseWordPhantomPrecision w n := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hprefix :
          ∀ i < k,
            SyracuseWordMatchesFrom w
              ((evalSyracuseWord w)^[i] n) := by
        intro i hi
        exact hmatch i (Nat.lt_succ_of_lt hi)
      have hlast :
          SyracuseWordMatchesFrom w
            ((evalSyracuseWord w)^[k] n) :=
        hmatch k (Nat.lt_succ_self k)
      have htax :=
        syracuseWordPhantomPrecision_after_eval_add_sum
          hexp hlast
      have hprevious := ih hprefix
      rw [Function.iterate_succ_apply']
      calc
        syracuseWordPhantomPrecision w
              (evalSyracuseWord w
                ((evalSyracuseWord w)^[k] n))
            + (k + 1) * w.sum
            =
          (syracuseWordPhantomPrecision w
                (evalSyracuseWord w
                  ((evalSyracuseWord w)^[k] n))
              + w.sum)
            + k * w.sum := by ring
        _ =
          syracuseWordPhantomPrecision w
              ((evalSyracuseWord w)^[k] n)
            + k * w.sum := by rw [htax]
        _ = syracuseWordPhantomPrecision w n := hprevious

/--
Every run of matched copies consumes `k * sum(w)` bits, so that quantity is
bounded by the initial phantom precision.
-/
theorem syracuseWord_matched_block_precision_budget
    {w : List ℕ} {n k : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (hmatch :
      ∀ i < k,
        SyracuseWordMatchesFrom w
          ((evalSyracuseWord w)^[i] n)) :
    k * w.sum ≤ syracuseWordPhantomPrecision w n := by
  have htax :=
    syracuseWordPhantomPrecision_after_iterate_add_mul_sum
      hexp hmatch
  omega

/--
Bit-length-facing version of the budget.  It connects the 2-adic trace to a
finite high-bit marker: the consumed precision cannot exceed the base-2
logarithm of the positive phantom numerator.
-/
theorem syracuseWord_matched_block_precision_budget_le_log
    {w : List ℕ} {n k : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (hmatch :
      ∀ i < k,
        SyracuseWordMatchesFrom w
          ((evalSyracuseWord w)^[i] n)) :
    k * w.sum ≤
      Nat.log 2 (syracuseWordPhantomPrecisionNumerator w n) := by
  exact
    (syracuseWord_matched_block_precision_budget hexp hmatch).trans
      (by
        unfold syracuseWordPhantomPrecision nu2Nat
        exact padicValNat_le_nat_log _)

/--
A positive-sum expansive word can match at most the initial number of
precision bits many consecutive blocks.
-/
theorem syracuseWord_matched_block_count_le_precision
    {w : List ℕ} {n k : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (hsum : 0 < w.sum)
    (hmatch :
      ∀ i < k,
        SyracuseWordMatchesFrom w
          ((evalSyracuseWord w)^[i] n)) :
    k ≤ syracuseWordPhantomPrecision w n := by
  have hbudget :=
    syracuseWord_matched_block_precision_budget hexp hmatch
  exact
    (Nat.le_mul_of_pos_right k hsum).trans hbudget

/-- A positive-sum matched block count is also bounded by a base-2 log. -/
theorem syracuseWord_matched_block_count_le_log
    {w : List ℕ} {n k : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (hsum : 0 < w.sum)
    (hmatch :
      ∀ i < k,
        SyracuseWordMatchesFrom w
          ((evalSyracuseWord w)^[i] n)) :
    k ≤ Nat.log 2 (syracuseWordPhantomPrecisionNumerator w n) := by
  have hbudget :=
    syracuseWord_matched_block_precision_budget_le_log
      hexp hmatch
  exact
    (Nat.le_mul_of_pos_right k hsum).trans hbudget

/--
Constructive exclusion of an infinite actual run of one positive-sum
expansive block.

The contradiction is witnessed after
`phantomPrecision(w,n) + 1` blocks; no compactness or limiting argument is
needed.
-/
theorem no_infinite_matched_expansive_word
    {w : List ℕ} {n : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (hsum : 0 < w.sum) :
    ¬ ∀ i : ℕ,
      SyracuseWordMatchesFrom w
        ((evalSyracuseWord w)^[i] n) := by
  intro hforever
  let k := syracuseWordPhantomPrecision w n + 1
  have hle :
      k ≤ syracuseWordPhantomPrecision w n :=
    syracuseWord_matched_block_count_le_precision
      hexp hsum (fun i _hi => hforever i)
  simp [k] at hle

/--
A positive-sum matched expansive word strictly lowers its phantom precision.
This is the well-founded progress fact intended for cyclic back-edges.
-/
theorem syracuseWordPhantomPrecision_after_eval_lt
    {w : List ℕ} {n : ℕ}
    (hexp : 2 ^ w.sum < 3 ^ w.length)
    (hsum : 0 < w.sum)
    (hmatch : SyracuseWordMatchesFrom w n) :
    syracuseWordPhantomPrecision w (evalSyracuseWord w n)
      <
    syracuseWordPhantomPrecision w n := by
  have htax :=
    syracuseWordPhantomPrecision_after_eval_add_sum hexp hmatch
  omega

end CollatzShadowing
