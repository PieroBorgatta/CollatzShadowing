/-
Exact arithmetic constraints on a positive periodic Syracuse word.

The existing affine-word theorem computes a matched finite endpoint.  This
module specializes it to an endpoint equal to its source, records the
classical cycle equation, and exposes two inexpensive consequences useful for
cycle searches:

* every nonempty positive cycle word is contracting;
* every divisor of its denominator must divide its word constant.

The final section gives a prefix barrier based at a minimum element of a
hypothetical cycle.  It is deliberately parameterized by a finite prefix and
does not assume the existence of any nontrivial cycle.
-/

import CollatzShadowing.Auxiliary
import CollatzShadowing.CollatzBridge

namespace CollatzShadowing

/--
Exact integer equation forced by a matched periodic Syracuse word:

`(2^sum(w) - 3^length(w)) * n = C_w`.

The integer formulation is valid before proving that the denominator is
positive.
-/
theorem syracuseWordCycleEquationInt
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hcycle : evalSyracuseWord w n = n) :
    (((2 : ℤ) ^ w.sum - (3 : ℤ) ^ w.length) * (n : ℤ))
      = (syracuseWordConst w : ℤ) := by
  have hnat :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch
  rw [hcycle] at hnat
  have hz :
      (2 : ℤ) ^ w.sum * (n : ℤ) =
        (3 : ℤ) ^ w.length * (n : ℤ)
          + (syracuseWordConst w : ℤ) := by
    exact_mod_cast hnat
  calc
    (((2 : ℤ) ^ w.sum - (3 : ℤ) ^ w.length) * (n : ℤ))
        = (2 : ℤ) ^ w.sum * (n : ℤ)
            - (3 : ℤ) ^ w.length * (n : ℤ) := by ring
    _ = (syracuseWordConst w : ℤ) := by omega

/--
A nonempty matched positive cycle word is necessarily contracting:
`3^length(w) < 2^sum(w)`.
-/
theorem syracuseWordCycleContracting
    {w : List ℕ} {n : ℕ}
    (hw : w ≠ []) (hn : 0 < n)
    (hmatch : SyracuseWordMatchesFrom w n)
    (hcycle : evalSyracuseWord w n = n) :
    3 ^ w.length < 2 ^ w.sum := by
  have heq := syracuseWordCycleEquationInt hmatch hcycle
  have hCnat := syracuseWordConst_pos_of_ne_nil hw
  have hC : (0 : ℤ) < (syracuseWordConst w : ℤ) := by
    exact_mod_cast hCnat
  have hnz : (0 : ℤ) < (n : ℤ) := by
    exact_mod_cast hn
  have hD :
      (0 : ℤ) < (2 : ℤ) ^ w.sum - (3 : ℤ) ^ w.length := by
    nlinarith
  exact_mod_cast (sub_pos.mp hD)

/-- Natural-number form of the exact cycle equation. -/
theorem syracuseWordCycleEquationNat
    {w : List ℕ} {n : ℕ}
    (hw : w ≠ []) (hn : 0 < n)
    (hmatch : SyracuseWordMatchesFrom w n)
    (hcycle : evalSyracuseWord w n = n) :
    (2 ^ w.sum - 3 ^ w.length) * n = syracuseWordConst w := by
  have hcontract := syracuseWordCycleContracting hw hn hmatch hcycle
  have hnat :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch
  rw [hcycle] at hnat
  rw [Nat.sub_mul]
  omega

/--
Modular cycle sieve.

Every divisor `m` of the positive cycle denominator
`2^sum(w) - 3^length(w)` must also divide `C_w`.  A single prime factor
violating this condition excludes the entire candidate word.
-/
theorem syracuseWordCycleModularSieve
    {w : List ℕ} {n m : ℕ}
    (hw : w ≠ []) (hn : 0 < n)
    (hmatch : SyracuseWordMatchesFrom w n)
    (hcycle : evalSyracuseWord w n = n)
    (hm : m ∣ 2 ^ w.sum - 3 ^ w.length) :
    m ∣ syracuseWordConst w := by
  have heq := syracuseWordCycleEquationNat hw hn hmatch hcycle
  rcases hm with ⟨k, hk⟩
  refine ⟨k * n, ?_⟩
  rw [← heq, hk]
  ring

open PhantomWord

/--
The prefix constant from the periodic-word development agrees with the
finite-word constant used by the natural-number Syracuse evaluator.
-/
theorem prefixC_eq_syracuseWordConst (w : PhantomWord) (j : ℕ) :
    w.prefixC j =
      syracuseWordConst ((List.range j).map w.aAt) := by
  induction j with
  | zero =>
      simp [PhantomWord.prefixC_zero, syracuseWordConst]
  | succ j ih =>
      rw [PhantomWord.prefixC_succ]
      rw [List.range_succ, List.map_append]
      simp only [List.map_singleton]
      rw [syracuseWordConst_append_singleton]
      rw [ih]
      rfl

/-- The full phantom-fold constant agrees with the finite-word constant. -/
theorem Cw_eq_syracuseWordConst (w : PhantomWord) :
    w.Cw = syracuseWordConst w.vals := by
  rw [← w.prefixC_length_eq_Cw]
  rw [prefixC_eq_syracuseWordConst]
  rw [w.map_aAt_range_length]

/--
If a matched prefix endpoint is no smaller than its source, then its exact
affine numerator cannot be smaller than the source scaled by `2^sum(w)`.

When the source is a minimum element of a hypothetical cycle, this applies to
every prefix of the cycle word.
-/
theorem minimumPrefixAffineBarrier
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hmin : n ≤ evalSyracuseWord w n) :
    2 ^ w.sum * n ≤
      3 ^ w.length * n + syracuseWordConst w := by
  calc
    2 ^ w.sum * n
        ≤ 2 ^ w.sum * evalSyracuseWord w n :=
      Nat.mul_le_mul_left _ hmin
    _ = 3 ^ w.length * n + syracuseWordConst w :=
      evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch

/--
If all proper prefixes up to depth `j` are noncontracting, then their affine
constant satisfies the elementary bound

`3 * C_j ≤ j * 3^j`.

The scaled form avoids division and is convenient for exact arithmetic.
-/
theorem three_mul_prefixC_le_of_noncontracting_proper_prefixes
    (w : PhantomWord) :
    ∀ j : ℕ,
      (∀ i < j, 2 ^ w.B i ≤ 3 ^ i) →
      3 * w.prefixC j ≤ j * 3 ^ j := by
  intro j
  induction j with
  | zero =>
      simp
  | succ j ih =>
      intro h
      have hprev : ∀ i < j, 2 ^ w.B i ≤ 3 ^ i := by
        intro i hi
        exact h i (Nat.lt_succ_of_lt hi)
      have hpow : 2 ^ w.B j ≤ 3 ^ j :=
        h j (Nat.lt_succ_self j)
      rw [PhantomWord.prefixC_succ]
      calc
        3 * (3 * w.prefixC j + 2 ^ w.B j)
            = 3 * (3 * w.prefixC j) + 3 * 2 ^ w.B j := by
                ring
        _ ≤ 3 * (j * 3 ^ j) + 3 * 3 ^ j := by
          exact Nat.add_le_add
            (Nat.mul_le_mul_left 3 (ih hprev))
            (Nat.mul_le_mul_left 3 hpow)
        _ = (j + 1) * 3 ^ (j + 1) := by
          rw [pow_succ]
          ring

/--
First-contracting-prefix bound based at a cycle minimum.

Suppose the first `j` entries of a periodic exponent word match the source
`n`, their endpoint is at least `n`, every earlier prefix is noncontracting,
and depth `j` is contracting.  Then

`3 * n ≤ j * 3^j`.

Thus any independent lower bound on a possible cycle minimum immediately
forces a lower bound on the first contracting-prefix depth.
-/
theorem three_mul_le_at_first_contracting_prefix
    (w : PhantomWord) (j n : ℕ)
    (hmatch :
      SyracuseWordMatchesFrom ((List.range j).map w.aAt) n)
    (hmin :
      n ≤ evalSyracuseWord ((List.range j).map w.aAt) n)
    (hproper : ∀ i < j, 2 ^ w.B i ≤ 3 ^ i)
    (hcross : 3 ^ j < 2 ^ w.B j) :
    3 * n ≤ j * 3 ^ j := by
  let p := (List.range j).map w.aAt
  have hbarrier := minimumPrefixAffineBarrier hmatch hmin
  have hsum : p.sum = w.B j := by
    rfl
  have hlen : p.length = j := by
    simp [p]
  have hconst : syracuseWordConst p = w.prefixC j := by
    exact (prefixC_eq_syracuseWordConst w j).symm
  change
    2 ^ p.sum * n ≤
      3 ^ p.length * n + syracuseWordConst p at hbarrier
  rw [hsum, hlen, hconst] at hbarrier
  have hgap : (3 ^ j + 1) * n ≤ 2 ^ w.B j * n := by
    exact Nat.mul_le_mul_right n hcross
  have hnC : n ≤ w.prefixC j := by
    apply Nat.le_of_add_le_add_left (a := 3 ^ j * n)
    calc
      3 ^ j * n + n = (3 ^ j + 1) * n := by ring
      _ ≤ 2 ^ w.B j * n := hgap
      _ ≤ 3 ^ j * n + w.prefixC j := hbarrier
  exact (Nat.mul_le_mul_left 3 hnC).trans
    (three_mul_prefixC_le_of_noncontracting_proper_prefixes
      w j hproper)

end CollatzShadowing
