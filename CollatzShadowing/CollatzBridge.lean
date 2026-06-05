/-
Conditional proof bridge from finite/descent information to Collatz-type
termination statements.

This file deliberately does not prove the Collatz conjecture.  It records
the exact global descent hypothesis that would be sufficient to turn the
accelerated Syracuse formalization into termination at `1`.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-20.
-/

import CollatzShadowing.Basic
import CollatzShadowing.WeakBridge
import Mathlib.Algebra.Ring.Parity

namespace CollatzShadowing

/-!
## Conditional Collatz bridge

The finite K16 Collatz-Wielandt certificates prove statements about
declared finite matrices.  They do not by themselves prove that every
integer orbit is captured by those matrices.

The bridge below isolates the missing mathematical obligation: every
positive odd integer different from `1` must have a finite accelerated
Syracuse iterate that is again positive odd and strictly smaller than
the starting integer.
-/

/-- The classical one-step Collatz map on natural numbers. -/
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- Classical Collatz termination, stated for positive natural numbers. -/
def ClassicalCollatzConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ k : ℕ, collatzStep^[k] n = 1

/-- Accelerated Syracuse termination for one initial value. -/
def acceleratedOrbitHitsOne (n : ℕ) : Prop :=
  ∃ k : ℕ, S^[k] n = 1

/--
Accelerated Collatz/Syracuse termination on positive odd natural
numbers.
-/
def AcceleratedCollatzConjecture : Prop :=
  ∀ n : ℕ, 0 < n → Odd n → acceleratedOrbitHitsOne n

/--
The global strict-descent hypothesis needed by the current finite-layer
program.

For every positive odd `n ≠ 1`, some finite accelerated Syracuse iterate
must be a positive odd integer strictly below `n`.  Proving this from the
phantom-shadowing finite certificates is the substantive missing step.
-/
def UniformStrictDescentHypothesis : Prop :=
  ∀ n : ℕ, 0 < n → Odd n → n ≠ 1 →
    ∃ k : ℕ, 0 < S^[k] n ∧ Odd (S^[k] n) ∧ S^[k] n < n

/-- On even inputs, the classical Collatz map is one halving step. -/
theorem collatzStep_of_even {n : ℕ} (h : Even n) :
    collatzStep n = n / 2 := by
  simp [collatzStep, h]

/-- On odd inputs, the classical Collatz map is the affine step `3n+1`. -/
theorem collatzStep_of_odd {n : ℕ} (h : Odd n) :
    collatzStep n = 3 * n + 1 := by
  simp [collatzStep, Nat.not_even_iff_odd.mpr h]

/--
If `2^k` divides `m`, then `k` classical Collatz steps from `m` are just
`k` halvings.
-/
theorem collatzStep_iterate_div_pow_two_of_pow_dvd
    (m k : ℕ) (h : 2 ^ k ∣ m) :
    collatzStep^[k] m = m / 2 ^ k := by
  induction k generalizing m with
  | zero =>
      simp
  | succ k ih =>
      have htwo_pow : 2 ∣ 2 ^ (k + 1) := by
        rw [pow_succ']
        exact dvd_mul_right 2 (2 ^ k)
      have htwo_m : 2 ∣ m := htwo_pow.trans h
      have heven_m : Even m := even_iff_two_dvd.mpr htwo_m
      have htail : 2 ^ k ∣ m / 2 := by
        rw [Nat.dvd_div_iff_mul_dvd htwo_m]
        simpa [pow_succ'] using h
      rw [Function.iterate_succ, Function.comp_apply,
        collatzStep_of_even heven_m, ih (m / 2) htail,
        Nat.div_div_eq_div_mul, pow_succ']

/-- The odd part of a positive natural number. -/
def natOddPart (n : ℕ) : ℕ :=
  n / 2 ^ nu2Nat n

theorem natOddPart_pos {n : ℕ} (hn : 0 < n) : 0 < natOddPart n := by
  have hdiv : 2 ^ nu2Nat n ∣ n := by
    simpa [nu2Nat] using (pow_padicValNat_dvd (p := 2) (n := n))
  have hpow_pos : 0 < 2 ^ nu2Nat n := pow_pos (by norm_num : 0 < (2 : ℕ)) _
  exact Nat.div_pos (Nat.le_of_dvd hn hdiv) hpow_pos

theorem natOddPart_odd {n : ℕ} (hn : 0 < n) : Odd (natOddPart n) := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  have hdiv : 2 ^ nu2Nat n ∣ n := by
    simpa [nu2Nat] using (pow_padicValNat_dvd (p := 2) (n := n))
  have hnot : ¬ 2 ∣ natOddPart n := by
    intro htwo
    have hpow_succ : 2 ^ (nu2Nat n + 1) ∣ n := by
      have hmul : 2 ^ nu2Nat n * 2 ∣ n :=
        (Nat.dvd_div_iff_mul_dvd hdiv).mp (by simpa [natOddPart] using htwo)
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc, nu2Nat] using hmul
    exact pow_succ_padicValNat_not_dvd (p := 2) (n := n) hn_ne hpow_succ
  exact Nat.not_even_iff_odd.mp (by
    intro heven
    exact hnot (even_iff_two_dvd.mp heven))

theorem collatzStep_iterate_natOddPart (n : ℕ) :
    collatzStep^[nu2Nat n] n = natOddPart n := by
  have hdiv : 2 ^ nu2Nat n ∣ n := by
    simpa [nu2Nat] using (pow_padicValNat_dvd (p := 2) (n := n))
  simpa [natOddPart] using
    collatzStep_iterate_div_pow_two_of_pow_dvd n (nu2Nat n) hdiv

theorem syracuse_pos (n : ℕ) : 0 < S n := by
  have hm_pos : 0 < syracuseNumerator n := by
    simp [syracuseNumerator]
  have hdiv : 2 ^ syracuseExponent n ∣ syracuseNumerator n := by
    simpa [syracuseExponent, syracuseNumerator, nu2Nat] using
      (pow_padicValNat_dvd (p := 2) (n := 3 * n + 1))
  have hpow_pos : 0 < 2 ^ syracuseExponent n :=
    pow_pos (by norm_num : 0 < (2 : ℕ)) _
  exact Nat.div_pos (Nat.le_of_dvd hm_pos hdiv) hpow_pos

theorem syracuse_odd (n : ℕ) : Odd (S n) := by
  have hm_pos : 0 < syracuseNumerator n := by
    simp [syracuseNumerator]
  have hm_ne : syracuseNumerator n ≠ 0 := Nat.ne_of_gt hm_pos
  have hdiv : 2 ^ syracuseExponent n ∣ syracuseNumerator n := by
    simpa [syracuseExponent, syracuseNumerator, nu2Nat] using
      (pow_padicValNat_dvd (p := 2) (n := 3 * n + 1))
  have hnot : ¬ 2 ∣ S n := by
    intro htwo
    have hpow_succ :
        2 ^ (syracuseExponent n + 1) ∣ syracuseNumerator n := by
      have hmul : 2 ^ syracuseExponent n * 2 ∣ syracuseNumerator n :=
        (Nat.dvd_div_iff_mul_dvd hdiv).mp (by simpa [S] using htwo)
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc,
        syracuseExponent, syracuseNumerator, nu2Nat] using hmul
    exact pow_succ_padicValNat_not_dvd
      (p := 2) (n := syracuseNumerator n) hm_ne hpow_succ
  exact Nat.not_even_iff_odd.mp (by
    intro heven
    exact hnot (even_iff_two_dvd.mp heven))

/--
If an accelerated Syracuse step divides by at least `4`, then it is a strict
descent for every `n > 1`.
-/
theorem syracuse_lt_self_of_two_le_exponent
    {n : ℕ} (hn : 1 < n) (hexp : 2 ≤ syracuseExponent n) :
    S n < n := by
  have hden_pos : 0 < 2 ^ syracuseExponent n :=
    pow_pos (by norm_num : 0 < (2 : ℕ)) _
  rw [S, syracuseNumerator]
  rw [Nat.div_lt_iff_lt_mul hden_pos]
  have hpow4 : 4 ≤ 2 ^ syracuseExponent n := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ syracuseExponent n :=
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexp
  calc
    3 * n + 1 < 4 * n := by omega
    _ ≤ (2 ^ syracuseExponent n) * n :=
        Nat.mul_le_mul_right n hpow4
    _ = n * 2 ^ syracuseExponent n := by rw [Nat.mul_comm]

/-- Any positive number of accelerated Syracuse iterates is positive. -/
theorem syracuse_iterate_succ_pos (k n : ℕ) :
    0 < S^[k + 1] n := by
  simpa [Function.iterate_succ_apply'] using
    (syracuse_pos (S^[k] n))

/-- Any positive number of accelerated Syracuse iterates is odd. -/
theorem syracuse_iterate_succ_odd (k n : ℕ) :
    Odd (S^[k + 1] n) := by
  simpa [Function.iterate_succ_apply'] using
    (syracuse_odd (S^[k] n))

/--
One accelerated Syracuse step when the removed 2-adic exponent is supplied
externally.
-/
def syracuseStepWithExponent (a n : ℕ) : ℕ :=
  (3 * n + 1) / 2 ^ a

theorem padicValNat_two_pow_mul_odd
    {a m : ℕ} (hodd : Odd m) :
    padicValNat 2 (2 ^ a * m) = a := by
  rcases hodd with ⟨r, hr⟩
  have hm_ne : m ≠ 0 := by omega
  have hnotdvd : ¬ 2 ∣ m := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr ⟨r, hr⟩)
      (even_iff_two_dvd.mpr hdiv)
  have hzero : padicValNat 2 m = 0 :=
    padicValNat.eq_zero_of_not_dvd hnotdvd
  rw [padicValNat_base_pow_mul (p := 2) (n := m)
      (by norm_num : 1 < 2) hm_ne a, hzero]
  omega

theorem syracuseStep_of_num_eq_two_pow_mul_odd
    {n a m : ℕ}
    (hnum : syracuseNumerator n = 2 ^ a * m)
    (hodd : Odd m) :
    syracuseExponent n = a ∧ S n = m := by
  have hexp : syracuseExponent n = a := by
    rw [syracuseExponent, nu2Nat, hnum]
    exact padicValNat_two_pow_mul_odd hodd
  refine ⟨hexp, ?_⟩
  have hpow_pos : 0 < 2 ^ a :=
    pow_pos (by norm_num : 0 < (2 : ℕ)) a
  rw [S, hnum, hexp]
  exact Nat.mul_div_cancel_left m hpow_pos

/-- Evaluate a finite word of prescribed Syracuse exponents on `n`. -/
def evalSyracuseWord : List ℕ → ℕ → ℕ
  | [], n => n
  | a :: rest, n => evalSyracuseWord rest (syracuseStepWithExponent a n)

/--
Numerator constant for a finite prescribed Syracuse exponent word.

For an exact matching word `w`, the evaluated endpoint satisfies

`2^w.sum * evalSyracuseWord w n = 3^w.length * n + syracuseWordConst w`.

The recursion is written in the same order as `evalSyracuseWord`: first apply
the head exponent, then the remaining word.
-/
def syracuseWordConst : List ℕ → ℕ
  | [] => 0
  | _a :: rest => 3 ^ rest.length + 2 ^ _a * syracuseWordConst rest

/-- Formal rational affine endpoint attached to a prescribed exponent word. -/
def syracuseWordAffineEndpointQ (w : List ℕ) (x : ℚ) : ℚ :=
  (((3 ^ w.length : ℕ) : ℚ) * x + (syracuseWordConst w : ℚ))
    / ((2 ^ w.sum : ℕ) : ℚ)

/--
Formal rational fixed point of a periodic exponent word.

This is a phantom-cycle diagnostic: it is meaningful as a rational/2-adic
boundary point even when it is not a positive integer.
-/
def syracuseWordFormalFixedPoint (w : List ℕ) : ℚ :=
  (syracuseWordConst w : ℚ)
    / (((2 ^ w.sum : ℕ) : ℚ) - ((3 ^ w.length : ℕ) : ℚ))

theorem syracuseWordConst_pos_cons (a : ℕ) (rest : List ℕ) :
    0 < syracuseWordConst (a :: rest) := by
  unfold syracuseWordConst
  exact Nat.add_pos_left (pow_pos (by norm_num : 0 < (3 : ℕ)) _) _

theorem syracuseWordConst_pos_of_ne_nil
    {w : List ℕ} (hw : w ≠ []) :
    0 < syracuseWordConst w := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons a rest => exact syracuseWordConst_pos_cons a rest

theorem syracuseWordConst_append_singleton
    (w : List ℕ) (a : ℕ) :
    syracuseWordConst (w ++ [a])
      = 3 * syracuseWordConst w + 2 ^ w.sum := by
  induction w with
  | nil =>
      simp [syracuseWordConst]
  | cons b rest ih =>
      simp [syracuseWordConst, ih, pow_succ, pow_add]
      ring

theorem syracuseWordFormalFixedPoint_fixed
    {w : List ℕ}
    (hden :
      (((2 ^ w.sum : ℕ) : ℚ) - ((3 ^ w.length : ℕ) : ℚ)) ≠ 0) :
    syracuseWordAffineEndpointQ w (syracuseWordFormalFixedPoint w)
      = syracuseWordFormalFixedPoint w := by
  have hpow : ((2 ^ w.sum : ℕ) : ℚ) ≠ 0 := by norm_num
  unfold syracuseWordAffineEndpointQ syracuseWordFormalFixedPoint
  field_simp [hden, hpow]
  ring

/--
Deviation from a formal periodic endpoint is multiplied by the rational
factor `3^length / 2^sum`.

This is the analytic core behind the phantom-boundary obstruction: repeated
expansive low-exponent words move away from their negative rational fixed
point in the real affine coordinate, while the exact word match is controlled
by 2-adic congruence to that same point.
-/
theorem syracuseWordAffineEndpointQ_sub_formalFixedPoint
    {w : List ℕ} (x : ℚ)
    (hden :
      (((2 ^ w.sum : ℕ) : ℚ) - ((3 ^ w.length : ℕ) : ℚ)) ≠ 0) :
    syracuseWordAffineEndpointQ w x - syracuseWordFormalFixedPoint w
      =
      (((3 ^ w.length : ℕ) : ℚ) / ((2 ^ w.sum : ℕ) : ℚ))
        * (x - syracuseWordFormalFixedPoint w) := by
  have hpow : ((2 ^ w.sum : ℕ) : ℚ) ≠ 0 := by norm_num
  unfold syracuseWordAffineEndpointQ syracuseWordFormalFixedPoint
  field_simp [hden, hpow]
  ring

theorem syracuseWordExpansionFactor_gt_one_of_expanding
    {w : List ℕ}
    (hexp :
      ((2 ^ w.sum : ℕ) : ℚ) < ((3 ^ w.length : ℕ) : ℚ)) :
    (1 : ℚ) <
      (((3 ^ w.length : ℕ) : ℚ) / ((2 ^ w.sum : ℕ) : ℚ)) := by
  have hpow_pos : (0 : ℚ) < ((2 ^ w.sum : ℕ) : ℚ) :=
    Nat.cast_pos.mpr (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
  exact (one_lt_div hpow_pos).mpr hexp

/--
Every nonempty periodic word with `2^sum < 3^length` has a negative formal
rational fixed point.  This is the exact reason expansive periodic
low-exponent boundaries are phantom rather than positive-integer cycles.
-/
theorem syracuseWordFormalFixedPoint_neg_of_expanding
    {w : List ℕ} (hw : w ≠ [])
    (hexp :
      ((2 ^ w.sum : ℕ) : ℚ) < ((3 ^ w.length : ℕ) : ℚ)) :
    syracuseWordFormalFixedPoint w < 0 := by
  have hCnat : 0 < syracuseWordConst w :=
    syracuseWordConst_pos_of_ne_nil hw
  have hC : (0 : ℚ) < (syracuseWordConst w : ℚ) :=
    Nat.cast_pos.mpr hCnat
  have hden :
      (((2 ^ w.sum : ℕ) : ℚ) - ((3 ^ w.length : ℕ) : ℚ)) < 0 :=
    sub_neg.mpr hexp
  unfold syracuseWordFormalFixedPoint
  exact div_neg_of_pos_of_neg hC hden

theorem syracuseWordFormalFixedPoint_one :
    syracuseWordFormalFixedPoint [1] = -1 := by
  norm_num [syracuseWordFormalFixedPoint, syracuseWordConst]

theorem syracuseWordFormalFixedPoint_one_two :
    syracuseWordFormalFixedPoint [1, 2] = -5 := by
  norm_num [syracuseWordFormalFixedPoint, syracuseWordConst]

theorem syracuseWordFormalFixedPoint_two_one :
    syracuseWordFormalFixedPoint [2, 1] = -7 := by
  norm_num [syracuseWordFormalFixedPoint, syracuseWordConst]

/-- Evaluating a concatenated Syracuse word is sequential evaluation. -/
theorem evalSyracuseWord_append
    (w v : List ℕ) (n : ℕ) :
    evalSyracuseWord (w ++ v) n =
      evalSyracuseWord v (evalSyracuseWord w n) := by
  induction w generalizing n with
  | nil =>
      simp [evalSyracuseWord]
  | cons a rest ih =>
      simp [evalSyracuseWord, ih]

/--
The orbit of `n` matches a finite word of Syracuse exponents.

This recursive form is proof-facing: at each step it checks the actual
`syracuseExponent` of the current accelerated iterate.
-/
def SyracuseWordMatchesFrom : List ℕ → ℕ → Prop
  | [], _n => True
  | a :: rest, n => syracuseExponent n = a ∧ SyracuseWordMatchesFrom rest (S n)

/--
If `a` is the actual Syracuse exponent at `n`, then the externally supplied
step has no floor error after multiplying by `2^a`.
-/
theorem pow_mul_syracuseStepWithExponent_eq_of_exponent
    {a n : ℕ} (ha : syracuseExponent n = a) :
    2 ^ a * syracuseStepWithExponent a n = 3 * n + 1 := by
  have hdiv : 2 ^ a ∣ 3 * n + 1 := by
    rw [← ha]
    simpa [syracuseExponent, syracuseNumerator, nu2Nat] using
      (pow_padicValNat_dvd (p := 2) (n := 3 * n + 1))
  simpa [syracuseStepWithExponent, Nat.mul_comm] using
    (Nat.div_mul_cancel hdiv)

/--
A match for a concatenated word splits into a match for the prefix and a match
for the suffix started at the evaluated prefix endpoint.
-/
theorem SyracuseWordMatchesFrom_append :
    ∀ (w v : List ℕ) (n : ℕ),
      SyracuseWordMatchesFrom (w ++ v) n →
      SyracuseWordMatchesFrom w n
        ∧ SyracuseWordMatchesFrom v (evalSyracuseWord w n)
  | [], v, n, h => by
      exact ⟨trivial, h⟩
  | a :: rest, v, n, h => by
      rcases h with ⟨ha, htail⟩
      rcases SyracuseWordMatchesFrom_append rest v (S n) htail with
        ⟨hrest, hv⟩
      have hstep : syracuseStepWithExponent a n = S n := by
        simp [syracuseStepWithExponent, S, syracuseNumerator, ha]
      constructor
      · exact ⟨ha, hrest⟩
      · simpa [evalSyracuseWord, hstep] using hv

theorem SyracuseWordMatchesFrom_append_of_matches :
    ∀ (w v : List ℕ) (n : ℕ),
      SyracuseWordMatchesFrom w n →
      SyracuseWordMatchesFrom v (evalSyracuseWord w n) →
      SyracuseWordMatchesFrom (w ++ v) n
  | [], _v, _n, _hw, hv => hv
  | a :: rest, v, n, hw, hv => by
      rcases hw with ⟨ha, hrest⟩
      have hstep : syracuseStepWithExponent a n = S n := by
        simp [syracuseStepWithExponent, S, syracuseNumerator, ha]
      refine ⟨ha, ?_⟩
      exact
        SyracuseWordMatchesFrom_append_of_matches rest v (S n) hrest
          (by simpa [evalSyracuseWord, hstep] using hv)

/--
If the actual accelerated orbit matches a prescribed exponent word, then the
word evaluator equals the corresponding iterate of `S`.
-/
theorem evalSyracuseWord_eq_iterate_of_matches :
    ∀ (w : List ℕ) (n : ℕ),
      SyracuseWordMatchesFrom w n →
      evalSyracuseWord w n = S^[w.length] n
  | [], _n, _h => by
      simp [evalSyracuseWord]
  | a :: rest, n, h => by
      rcases h with ⟨ha, hrest⟩
      have hstep : syracuseStepWithExponent a n = S n := by
        simp [syracuseStepWithExponent, S, syracuseNumerator, ha]
      have ih := evalSyracuseWord_eq_iterate_of_matches rest (S n) hrest
      calc
        evalSyracuseWord (a :: rest) n
            = evalSyracuseWord rest (S n) := by
                simp [evalSyracuseWord, hstep]
        _ = S^[rest.length] (S n) := ih
        _ = S^[(a :: rest).length] n := by
                simp [Function.iterate_succ_apply]

theorem evalSyracuseWord_odd_of_matches
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hlen : 0 < w.length) :
    Odd (evalSyracuseWord w n) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen) with ⟨k, hk⟩
  have heq := evalSyracuseWord_eq_iterate_of_matches w n hmatch
  rw [heq, hk]
  simpa [Nat.succ_eq_add_one] using syracuse_iterate_succ_odd k n

/--
Exact affine numerator formula for a matched finite Syracuse word.

This is the arithmetic bridge from word-level certificates to compact
contracting inequalities.  It is conditional on `SyracuseWordMatchesFrom`;
without the match hypothesis, `evalSyracuseWord` contains ordinary natural
division and may have floor error.
-/
theorem evalSyracuseWord_mul_pow_sum_eq_affine_of_matches :
    ∀ (w : List ℕ) (n : ℕ),
      SyracuseWordMatchesFrom w n →
      2 ^ w.sum * evalSyracuseWord w n =
        3 ^ w.length * n + syracuseWordConst w
  | [], n, _h => by
      simp [evalSyracuseWord, syracuseWordConst]
  | a :: rest, n, h => by
      rcases h with ⟨ha, hrest⟩
      have hstep : syracuseStepWithExponent a n = S n := by
        simp [syracuseStepWithExponent, S, syracuseNumerator, ha]
      have ih :=
        evalSyracuseWord_mul_pow_sum_eq_affine_of_matches rest (S n) hrest
      have hmul := pow_mul_syracuseStepWithExponent_eq_of_exponent ha
      rw [hstep] at hmul
      calc
        2 ^ (a :: rest).sum * evalSyracuseWord (a :: rest) n
            = 2 ^ a * (2 ^ rest.sum * evalSyracuseWord rest (S n)) := by
                simp [evalSyracuseWord, hstep, pow_add, Nat.mul_assoc]
        _ = 2 ^ a * (3 ^ rest.length * S n + syracuseWordConst rest) := by
                rw [ih]
        _ = 3 ^ (a :: rest).length * n + syracuseWordConst (a :: rest) := by
                calc
                  2 ^ a * (3 ^ rest.length * S n + syracuseWordConst rest)
                      = 3 ^ rest.length * (2 ^ a * S n)
                          + 2 ^ a * syracuseWordConst rest := by
                            ring
                  _ = 3 ^ rest.length * (3 * n + 1)
                          + 2 ^ a * syracuseWordConst rest := by
                            rw [hmul]
                  _ = 3 ^ (a :: rest).length * n
                          + syracuseWordConst (a :: rest) := by
                            simp [syracuseWordConst, pow_succ]
                            ring

theorem padicValNat_syracuseWordAffine_of_matches
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hlen : 0 < w.length) :
    padicValNat 2 (3 ^ w.length * n + syracuseWordConst w) = w.sum := by
  have heq :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch
  rw [← heq]
  exact padicValNat_two_pow_mul_odd
    (evalSyracuseWord_odd_of_matches hmatch hlen)

theorem padicValNat_a0EndpointSuffixAffine_of_matches
    {suff : List ℕ} {t : ℕ}
    (hmatch : SyracuseWordMatchesFrom suff (593 + 1458 * t))
    (hlen : 0 < suff.length) :
    padicValNat 2
      (3 ^ suff.length * (593 + 1458 * t) + syracuseWordConst suff)
      = suff.sum :=
  padicValNat_syracuseWordAffine_of_matches hmatch hlen

theorem syracuseWordAffine_dvd_of_matches
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n) :
    2 ^ w.sum ∣ 3 ^ w.length * n + syracuseWordConst w := by
  refine ⟨evalSyracuseWord w n, ?_⟩
  exact (evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch).symm

theorem a0EndpointSuffixAffine_dvd_of_matches
    {suff : List ℕ} {t : ℕ}
    (hmatch : SyracuseWordMatchesFrom suff (593 + 1458 * t)) :
    2 ^ suff.sum ∣
      3 ^ suff.length * (593 + 1458 * t) + syracuseWordConst suff :=
  syracuseWordAffine_dvd_of_matches hmatch

theorem evalSyracuseWord_lt_of_affine_contracting_of_matches
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hcontract :
      3 ^ w.length * n + syracuseWordConst w < 2 ^ w.sum * n) :
    evalSyracuseWord w n < n := by
  have heq :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w n hmatch
  have hmul_lt :
      2 ^ w.sum * evalSyracuseWord w n < 2 ^ w.sum * n := by
    rwa [heq]
  exact Nat.lt_of_mul_lt_mul_left hmul_lt

theorem collatzStep_iterate_syracuse {n : ℕ} (hodd : Odd n) :
    collatzStep^[syracuseExponent n + 1] n = S n := by
  have hdiv : 2 ^ syracuseExponent n ∣ 3 * n + 1 := by
    simpa [syracuseExponent, syracuseNumerator, nu2Nat] using
      (pow_padicValNat_dvd (p := 2) (n := 3 * n + 1))
  rw [Function.iterate_succ, Function.comp_apply, collatzStep_of_odd hodd]
  simpa [S, syracuseNumerator] using
    collatzStep_iterate_div_pow_two_of_pow_dvd
      (3 * n + 1) (syracuseExponent n) hdiv

/--
Every finite accelerated Syracuse orbit segment from a positive odd input
can be expanded into a finite classical Collatz orbit segment.
-/
theorem classical_hits_one_of_accelerated_hits_one
    {n k : ℕ} (hn : 0 < n) (hodd : Odd n) (h : S^[k] n = 1) :
    ∃ m : ℕ, collatzStep^[m] n = 1 := by
  induction k generalizing n with
  | zero =>
      exact ⟨0, by simpa using h⟩
  | succ k ih =>
      have htail : S^[k] (S n) = 1 := by
        simpa [Function.iterate_succ, Function.comp_apply] using h
      have hSpos : 0 < S n := syracuse_pos n
      have hSodd : Odd (S n) := syracuse_odd n
      obtain ⟨m, hm⟩ := ih hSpos hSodd htail
      exact ⟨m + (syracuseExponent n + 1), by
        rw [Function.iterate_add, Function.comp_apply,
          collatzStep_iterate_syracuse hodd, hm]⟩

/-- A concrete strict-descent witness for one accelerated odd orbit. -/
structure StrictDescentWitness (n : ℕ) where
  k : ℕ
  positive : 0 < S^[k] n
  odd : Odd (S^[k] n)
  descends : S^[k] n < n

/-- Propositional form of existence of an accelerated strict descent. -/
def HasStrictDescent (n : ℕ) : Prop :=
  ∃ k : ℕ, 0 < S^[k] n ∧ Odd (S^[k] n) ∧ S^[k] n < n

/-- Step-indexed direct drop for the accelerated Syracuse map. -/
def DirectDropAt (k n : ℕ) : Prop :=
  0 < S^[k] n ∧ Odd (S^[k] n) ∧ S^[k] n < n

/-- A step-indexed direct drop gives the existential strict-descent form. -/
theorem hasStrictDescent_of_directDropAt {k n : ℕ}
    (h : DirectDropAt k n) : HasStrictDescent n :=
  ⟨k, h.1, h.2.1, h.2.2⟩

/-- Any concrete strict-descent witness gives a step-indexed direct drop. -/
theorem directDropAt_of_witness {n : ℕ}
    (w : StrictDescentWitness n) : DirectDropAt w.k n :=
  ⟨w.positive, w.odd, w.descends⟩

/--
Boolean checker for a concrete step-indexed direct drop.

This is used only for small finite audits.  The proof-facing theorem below
converts a successful boolean check back to `DirectDropAt`.
-/
def directDropAtBool (k n : ℕ) : Bool :=
  decide (0 < S^[k] n)
    && decide ((S^[k] n) % 2 = 1)
    && decide (S^[k] n < n)

def hasDirectDropWithinBool : ℕ → ℕ → Bool
  | 0, n => directDropAtBool 0 n
  | K + 1, n => directDropAtBool (K + 1) n || hasDirectDropWithinBool K n

theorem directDropAt_of_directDropAtBool_eq_true
    {k n : ℕ} (h : directDropAtBool k n = true) : DirectDropAt k n := by
  unfold directDropAtBool at h
  unfold DirectDropAt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, Nat.odd_iff.mpr h.1.2, h.2⟩

theorem exists_directDropAt_of_hasDirectDropWithinBool_eq_true :
    ∀ {K n : ℕ}, hasDirectDropWithinBool K n = true →
      ∃ k : ℕ, k ≤ K ∧ DirectDropAt k n
  | 0, n, h => by
      have hdrop : directDropAtBool 0 n = true := by
        simpa [hasDirectDropWithinBool] using h
      exact ⟨0, by omega, directDropAt_of_directDropAtBool_eq_true hdrop⟩
  | K + 1, n, h => by
      have hcases :
          directDropAtBool (K + 1) n = true
            ∨ hasDirectDropWithinBool K n = true := by
        simpa [hasDirectDropWithinBool, Bool.or_eq_true] using h
      rcases hcases with hdrop | hprev
      · exact ⟨K + 1, by omega, directDropAt_of_directDropAtBool_eq_true hdrop⟩
      · rcases exists_directDropAt_of_hasDirectDropWithinBool_eq_true hprev with
          ⟨k, hk, hdk⟩
        exact ⟨k, by omega, hdk⟩

theorem hasStrictDescent_of_hasDirectDropWithinBool_eq_true
    {K n : ℕ} (h : hasDirectDropWithinBool K n = true) :
    HasStrictDescent n := by
  rcases exists_directDropAt_of_hasDirectDropWithinBool_eq_true h with
    ⟨k, _hk, hdrop⟩
  exact hasStrictDescent_of_directDropAt hdrop

set_option linter.style.nativeDecide false

/--
Finite small-case check supporting the A0 suffix-threshold route.

Every positive odd `n < 455`, except `1`, has an accelerated direct drop within
100 Syracuse steps.  This does not address large `n`; it only closes the finite
exception range left by the current observed suffix threshold.
-/
theorem smallOddHasDirectDropWithin100Bool :
    ∀ n : Fin 455,
      0 < n.val → n.val % 2 = 1 → n.val ≠ 1 →
        hasDirectDropWithinBool 100 n.val = true := by
  native_decide

set_option linter.style.nativeDecide true

theorem hasStrictDescent_of_odd_lt_455
    {n : ℕ} (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hlt : n < 455) :
    HasStrictDescent n := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  exact hasStrictDescent_of_hasDirectDropWithinBool_eq_true
    (smallOddHasDirectDropWithin100Bool ⟨n, hlt⟩ hn hmod hn1)

set_option linter.style.nativeDecide false in
/--
Same finite small-case check with cutoff `464`.

The T16 semantic suffix audit already has maximum threshold `463`, so the
previous hard-coded `455` cutoff is not structurally stable.  This theorem is
still only a finite exception check.
-/
theorem smallOddHasDirectDropWithin100Bool464 :
    ∀ n : Fin 464,
      0 < n.val → n.val % 2 = 1 → n.val ≠ 1 →
        hasDirectDropWithinBool 100 n.val = true := by
  native_decide

theorem hasStrictDescent_of_odd_lt_464
    {n : ℕ} (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hlt : n < 464) :
    HasStrictDescent n := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  exact hasStrictDescent_of_hasDirectDropWithinBool_eq_true
    (smallOddHasDirectDropWithin100Bool464 ⟨n, hlt⟩ hn hmod hn1)

set_option linter.style.nativeDecide false in
/--
Finite small-case check with cutoff `648`.

The T18 semantic suffix audit has maximum threshold `647`.  This remains a
finite support theorem for that observed cutoff, not a structural constant.
-/
theorem smallOddHasDirectDropWithin100Bool648 :
    ∀ n : Fin 648,
      0 < n.val → n.val % 2 = 1 → n.val ≠ 1 →
        hasDirectDropWithinBool 100 n.val = true := by
  native_decide

theorem hasStrictDescent_of_odd_lt_648
    {n : ℕ} (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hlt : n < 648) :
    HasStrictDescent n := by
  have hmod : n % 2 = 1 := Nat.odd_iff.mp hodd
  exact hasStrictDescent_of_hasDirectDropWithinBool_eq_true
    (smallOddHasDirectDropWithin100Bool648 ⟨n, hlt⟩ hn hmod hn1)

/--
A high-valuation accelerated Syracuse step gives the one-step direct-drop
predicate used by the finite-model soundness interface.
-/
theorem directDropAt_one_of_two_le_syracuseExponent
    {n : ℕ} (hn : 1 < n) (hexp : 2 ≤ syracuseExponent n) :
    DirectDropAt 1 n := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using syracuse_pos n
  · simpa using syracuse_odd n
  · simpa using syracuse_lt_self_of_two_le_exponent hn hexp

/--
A matched nonempty Syracuse word whose evaluated endpoint is below the start
gives a concrete step-indexed direct drop.
-/
theorem directDropAt_of_word_matches_eval_lt
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hlen : 0 < w.length)
    (hlt : evalSyracuseWord w n < n) :
    DirectDropAt w.length n := by
  have heq := evalSyracuseWord_eq_iterate_of_matches w n hmatch
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen) with ⟨k, hk⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hk]
    exact syracuse_iterate_succ_pos k n
  · rw [hk]
    exact syracuse_iterate_succ_odd k n
  · rw [← heq]
    exact hlt

theorem directDropAt_of_word_matches_affine_contracting
    {w : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hlen : 0 < w.length)
    (hcontract :
      3 ^ w.length * n + syracuseWordConst w < 2 ^ w.sum * n) :
    DirectDropAt w.length n :=
  directDropAt_of_word_matches_eval_lt hmatch hlen
    (evalSyracuseWord_lt_of_affine_contracting_of_matches
      hmatch hcontract)

/--
If a matched word is decomposed as `pref ++ suff` and the evaluated suffix
endpoint is below the original source, then the whole concatenated word gives
a direct drop.  This is the proof-facing shape needed when a finite audit
discovers a common non-drop prefix followed by many suffix drop words.
-/
theorem directDropAt_of_suffix_after_prefix_matches_eval_lt
    {pref suff : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom (pref ++ suff) n)
    (hsuffix : 0 < suff.length)
    (hlt :
      evalSyracuseWord suff (evalSyracuseWord pref n) < n) :
    DirectDropAt (pref ++ suff).length n := by
  refine directDropAt_of_word_matches_eval_lt hmatch ?_ ?_
  · simp [List.length_append]
    omega
  · rwa [evalSyracuseWord_append]

theorem evalSyracuseWord_suffix_lt_of_affine_contracting_after_prefix
    {pref suff : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom (pref ++ suff) n)
    (hcontract :
      3 ^ suff.length * evalSyracuseWord pref n + syracuseWordConst suff
        < 2 ^ suff.sum * n) :
    evalSyracuseWord suff (evalSyracuseWord pref n) < n := by
  have hsuffmatch :
      SyracuseWordMatchesFrom suff (evalSyracuseWord pref n) :=
    (SyracuseWordMatchesFrom_append pref suff n hmatch).2
  have heq :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches
      suff (evalSyracuseWord pref n) hsuffmatch
  have hmul_lt :
      2 ^ suff.sum * evalSyracuseWord suff (evalSyracuseWord pref n)
        < 2 ^ suff.sum * n := by
    rwa [heq]
  exact Nat.lt_of_mul_lt_mul_left hmul_lt

theorem directDropAt_of_suffix_after_prefix_affine_contracting
    {pref suff : List ℕ} {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom (pref ++ suff) n)
    (hsuffix : 0 < suff.length)
    (hcontract :
      3 ^ suff.length * evalSyracuseWord pref n + syracuseWordConst suff
        < 2 ^ suff.sum * n) :
    DirectDropAt (pref ++ suff).length n :=
  directDropAt_of_suffix_after_prefix_matches_eval_lt
    hmatch hsuffix
    (evalSyracuseWord_suffix_lt_of_affine_contracting_after_prefix
      hmatch hcontract)

/-!
### A0 semantic-drop common prefix

The current complete-prefix semantic replay audit found that every finite
semantic drop word through `T14` starts with `[1,1,2,1,1,1]`.  The following
named prefix and affine formula are local infrastructure for the next
compression step.  They do not assert that every global orbit has this prefix.
-/

def a0SemanticDropCommonPrefix : List ℕ :=
  [1, 1, 2, 1, 1, 1]

/--
The natural A0 source cylinder used by script 126 is
`n = 103 + 256*t`.  On this whole cylinder, the first six accelerated
Syracuse exponents are exactly the observed common prefix
`[1,1,2,1,1,1]`.

This is a parametric congruence fact, not a finite-prefix audit.
-/
theorem a0SemanticDropCommonPrefix_matches_source_cylinder
    (t : ℕ) :
    SyracuseWordMatchesFrom a0SemanticDropCommonPrefix (103 + 256 * t) := by
  have h0 :
      syracuseExponent (103 + 256 * t) = 1
        ∧ S (103 + 256 * t) = 155 + 384 * t := by
    refine syracuseStep_of_num_eq_two_pow_mul_odd ?_ ?_
    · unfold syracuseNumerator
      ring
    · exact ⟨77 + 192 * t, by ring⟩
  have h1 :
      syracuseExponent (155 + 384 * t) = 1
        ∧ S (155 + 384 * t) = 233 + 576 * t := by
    refine syracuseStep_of_num_eq_two_pow_mul_odd ?_ ?_
    · unfold syracuseNumerator
      ring
    · exact ⟨116 + 288 * t, by ring⟩
  have h2 :
      syracuseExponent (233 + 576 * t) = 2
        ∧ S (233 + 576 * t) = 175 + 432 * t := by
    refine syracuseStep_of_num_eq_two_pow_mul_odd ?_ ?_
    · unfold syracuseNumerator
      ring
    · exact ⟨87 + 216 * t, by ring⟩
  have h3 :
      syracuseExponent (175 + 432 * t) = 1
        ∧ S (175 + 432 * t) = 263 + 648 * t := by
    refine syracuseStep_of_num_eq_two_pow_mul_odd ?_ ?_
    · unfold syracuseNumerator
      ring
    · exact ⟨131 + 324 * t, by ring⟩
  have h4 :
      syracuseExponent (263 + 648 * t) = 1
        ∧ S (263 + 648 * t) = 395 + 972 * t := by
    refine syracuseStep_of_num_eq_two_pow_mul_odd ?_ ?_
    · unfold syracuseNumerator
      ring
    · exact ⟨197 + 486 * t, by ring⟩
  have h5 :
      syracuseExponent (395 + 972 * t) = 1
        ∧ S (395 + 972 * t) = 593 + 1458 * t := by
    refine syracuseStep_of_num_eq_two_pow_mul_odd ?_ ?_
    · unfold syracuseNumerator
      ring
    · exact ⟨296 + 729 * t, by ring⟩
  unfold a0SemanticDropCommonPrefix SyracuseWordMatchesFrom
  refine ⟨h0.1, ?_⟩
  rw [h0.2]
  refine ⟨h1.1, ?_⟩
  rw [h1.2]
  refine ⟨h2.1, ?_⟩
  rw [h2.2]
  refine ⟨h3.1, ?_⟩
  rw [h3.2]
  refine ⟨h4.1, ?_⟩
  rw [h4.2]
  refine ⟨h5.1, ?_⟩
  rw [h5.2]
  trivial

theorem eval_a0SemanticDropCommonPrefix_source_cylinder
    (t : ℕ) :
    evalSyracuseWord a0SemanticDropCommonPrefix (103 + 256 * t)
      = 593 + 1458 * t := by
  have hs0 :
      syracuseStepWithExponent 1 (103 + 256 * t) = 155 + 384 * t := by
    unfold syracuseStepWithExponent
    have hnum : 3 * (103 + 256 * t) + 1 = 2 * (155 + 384 * t) := by
      ring
    rw [hnum]
    norm_num
  have hs1 :
      syracuseStepWithExponent 1 (155 + 384 * t) = 233 + 576 * t := by
    unfold syracuseStepWithExponent
    have hnum : 3 * (155 + 384 * t) + 1 = 2 * (233 + 576 * t) := by
      ring
    rw [hnum]
    norm_num
  have hs2 :
      syracuseStepWithExponent 2 (233 + 576 * t) = 175 + 432 * t := by
    unfold syracuseStepWithExponent
    have hnum : 3 * (233 + 576 * t) + 1 = 4 * (175 + 432 * t) := by
      ring
    rw [hnum]
    norm_num
  have hs3 :
      syracuseStepWithExponent 1 (175 + 432 * t) = 263 + 648 * t := by
    unfold syracuseStepWithExponent
    have hnum : 3 * (175 + 432 * t) + 1 = 2 * (263 + 648 * t) := by
      ring
    rw [hnum]
    norm_num
  have hs4 :
      syracuseStepWithExponent 1 (263 + 648 * t) = 395 + 972 * t := by
    unfold syracuseStepWithExponent
    have hnum : 3 * (263 + 648 * t) + 1 = 2 * (395 + 972 * t) := by
      ring
    rw [hnum]
    norm_num
  have hs5 :
      syracuseStepWithExponent 1 (395 + 972 * t) = 593 + 1458 * t := by
    unfold syracuseStepWithExponent
    have hnum : 3 * (395 + 972 * t) + 1 = 2 * (593 + 1458 * t) := by
      ring
    rw [hnum]
    norm_num
  simp [a0SemanticDropCommonPrefix, evalSyracuseWord,
    hs0, hs1, hs2, hs3, hs4, hs5]

/--
The infinite all-`1` suffix obstruction is the 2-adic phantom endpoint `-1`.

Indeed, in the post-prefix coordinate `593 + 1458*t`, the formal parameter
`t = -11/27` gives endpoint `-1`; the corresponding source coordinate is not
a natural integer.  This records the exact boundary point behind the finite
low-exponent obstruction probes.
-/
theorem a0Endpoint_phantomParameter_eq_negOne :
    (593 : ℚ) + 1458 * (-(11 : ℚ) / 27) = -1 := by
  norm_num

theorem a0Source_phantomParameter_eq_negThirtyFiveOverTwentySeven :
    (103 : ℚ) + 256 * (-(11 : ℚ) / 27) = -(35 : ℚ) / 27 := by
  norm_num

/--
Raw endpoint-exit target for the A0 source cylinder.

For `n = 103 + 256*t`, the common prefix has already moved the orbit to
`593 + 1458*t`.  This predicate says that some actual suffix from that
endpoint drops below the original source.  It is intentionally independent of
any finite suffix table.
-/
def A0EndpointSuffixExit (t : ℕ) : Prop :=
  ∃ suff : List ℕ,
    SyracuseWordMatchesFrom suff (593 + 1458 * t)
      ∧ 0 < suff.length
      ∧ evalSyracuseWord suff (593 + 1458 * t) < 103 + 256 * t

/-- Conditional global exit target for the A0 source cylinder. -/
def A0EndpointSuffixExitAll : Prop :=
  ∀ t : ℕ, A0EndpointSuffixExit t

/-- Slope barrier for an A0 endpoint suffix. -/
def A0EndpointSuffixSlopeBarrier (suff : List ℕ) : Prop :=
  1458 * 3 ^ suff.length ≤ 256 * 2 ^ suff.sum

/--
Endpoint threshold inequality for an A0 suffix at parameter `t`.

Together with `A0EndpointSuffixSlopeBarrier`, this is exactly the natural
number inequality used by `a0EndpointSuffixExit_of_suffix_threshold_contracting`.
-/
def A0EndpointSuffixThreshold (t : ℕ) (suff : List ℕ) : Prop :=
  593 * 3 ^ suff.length + syracuseWordConst suff
    <
  (256 * 2 ^ suff.sum - 1458 * 3 ^ suff.length) * t
    + 103 * 2 ^ suff.sum

theorem a0EndpointSuffixThreshold_mono_t
    {suff : List ℕ} {t t' : ℕ}
    (ht : t ≤ t')
    (hthreshold : A0EndpointSuffixThreshold t suff) :
    A0EndpointSuffixThreshold t' suff := by
  unfold A0EndpointSuffixThreshold at hthreshold ⊢
  exact lt_of_lt_of_le hthreshold
    (Nat.add_le_add_right
      (Nat.mul_le_mul_left
        (256 * 2 ^ suff.sum - 1458 * 3 ^ suff.length) ht)
      (103 * 2 ^ suff.sum))

theorem a0EndpointSuffixThreshold_of_one_le
    {suff : List ℕ} {t : ℕ}
    (ht : 1 ≤ t)
    (hthreshold : A0EndpointSuffixThreshold 1 suff) :
    A0EndpointSuffixThreshold t suff :=
  a0EndpointSuffixThreshold_mono_t ht hthreshold

/--
Proof-facing threshold witness: it is enough to verify the endpoint threshold
at some smaller parameter `t0`, then use monotonicity in `t`.
-/
def A0EndpointSuffixThresholdWitness (t : ℕ) (suff : List ℕ) : Prop :=
  ∃ t0 : ℕ, t0 ≤ t ∧ A0EndpointSuffixThreshold t0 suff

theorem a0EndpointSuffixThreshold_of_thresholdWitness
    {t : ℕ} {suff : List ℕ}
    (hwitness : A0EndpointSuffixThresholdWitness t suff) :
    A0EndpointSuffixThreshold t suff := by
  rcases hwitness with ⟨t0, ht0, hthreshold⟩
  exact a0EndpointSuffixThreshold_mono_t ht0 hthreshold

/--
Linear congruence in the A0 endpoint parameter forced by a matched suffix.

It is written as a divisibility statement rather than choosing an inverse
modulo a power of two.  The coefficient of `t` is explicitly
`2 * 729 * 3^length`, so solving it modulo `2^sum` is the future residue/lower
bound task.
-/
def A0EndpointSuffixCongruence (t : ℕ) (suff : List ℕ) : Prop :=
  2 ^ suff.sum ∣
    (593 * 3 ^ suff.length + syracuseWordConst suff)
      + 2 * (729 * 3 ^ suff.length) * t

theorem a0EndpointSuffixCongruence_reducedCoeff_odd
    (suff : List ℕ) :
    Odd (729 * 3 ^ suff.length) := by
  have hpow : Odd (3 ^ suff.length) := by
    induction suff.length with
    | zero =>
        norm_num
    | succ k ih =>
        rw [pow_succ]
        exact Odd.mul ih (by norm_num : Odd 3)
  exact Odd.mul (by norm_num : Odd 729) hpow

theorem pow_two_dvd_of_succ_pow_two_dvd_two_mul
    {a x : ℕ}
    (hdiv : 2 ^ (a + 1) ∣ 2 * x) :
    2 ^ a ∣ x := by
  rcases hdiv with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have htwo :
      2 * x = 2 * (2 ^ a * q) := by
    calc
      2 * x = 2 ^ (a + 1) * q := hq
      _ = 2 * (2 ^ a * q) := by
        rw [pow_succ']
        ring
  exact Nat.mul_left_cancel (by norm_num : 0 < (2 : ℕ)) htwo

theorem a0EndpointSuffixCongruence_half_of_even_constant
    {t a b : ℕ} {suff : List ℕ}
    (hsum : suff.sum = a + 1)
    (hconst :
      593 * 3 ^ suff.length + syracuseWordConst suff = 2 * b)
    (hcong : A0EndpointSuffixCongruence t suff) :
    2 ^ a ∣ b + (729 * 3 ^ suff.length) * t := by
  unfold A0EndpointSuffixCongruence at hcong
  rw [hsum, hconst] at hcong
  have htwo :
      2 ^ (a + 1) ∣
        2 * (b + (729 * 3 ^ suff.length) * t) := by
    convert hcong using 1
    ring
  exact pow_two_dvd_of_succ_pow_two_dvd_two_mul htwo

theorem a0EndpointSuffixCongruence_of_matches
    {suff : List ℕ} {t : ℕ}
    (hmatch : SyracuseWordMatchesFrom suff (593 + 1458 * t)) :
    A0EndpointSuffixCongruence t suff := by
  have hdvd := a0EndpointSuffixAffine_dvd_of_matches hmatch
  unfold A0EndpointSuffixCongruence
  have hEq :
      3 ^ suff.length * (593 + 1458 * t) + syracuseWordConst suff =
        (593 * 3 ^ suff.length + syracuseWordConst suff)
          + 2 * (729 * 3 ^ suff.length) * t := by
    ring
  rwa [← hEq]

/--
`suff` is the first nonempty matched suffix prefix crossing the A0 endpoint
slope barrier.

The last field says that every nonempty proper prefix still lies below the
barrier.  This is the formal version of the empirical "first barrier
crossing" rule.
-/
structure A0FirstBarrierSuffix (t : ℕ) (suff : List ℕ) : Prop where
  match_suffix : SyracuseWordMatchesFrom suff (593 + 1458 * t)
  nonempty : 0 < suff.length
  barrier : A0EndpointSuffixSlopeBarrier suff
  minimal :
    ∀ pref rest : List ℕ,
      suff = pref ++ rest →
      0 < pref.length →
      0 < rest.length →
      ¬ A0EndpointSuffixSlopeBarrier pref

/-- Every A0 endpoint parameter has a first barrier suffix. -/
def A0FirstBarrierExistsAll : Prop :=
  ∀ t : ℕ, ∃ suff : List ℕ, A0FirstBarrierSuffix t suff

/--
At every first barrier crossing, the endpoint threshold inequality holds.

This is deliberately a named hypothesis, not a theorem: it is the next
mathematical target suggested by the finite probes.
-/
def A0FirstBarrierThresholdAutomatic : Prop :=
  ∀ ⦃t : ℕ⦄ ⦃suff : List ℕ⦄,
    A0FirstBarrierSuffix t suff →
      A0EndpointSuffixThreshold t suff

/--
Variant of the first-barrier target that separates the threshold check from
the lower bound on the matched parameter.
-/
def A0FirstBarrierThresholdWitnessAutomatic : Prop :=
  ∀ ⦃t : ℕ⦄ ⦃suff : List ℕ⦄,
    A0FirstBarrierSuffix t suff →
      A0EndpointSuffixThresholdWitness t suff

theorem A0FirstBarrierThresholdAutomatic_of_thresholdWitness
    (hwitness : A0FirstBarrierThresholdWitnessAutomatic) :
    A0FirstBarrierThresholdAutomatic := by
  intro t suff hfirst
  exact a0EndpointSuffixThreshold_of_thresholdWitness (hwitness hfirst)

theorem a0FirstBarrierSuffix_congruence
    {t : ℕ} {suff : List ℕ}
    (hfirst : A0FirstBarrierSuffix t suff) :
    A0EndpointSuffixCongruence t suff :=
  a0EndpointSuffixCongruence_of_matches hfirst.match_suffix

/--
The next proof-facing form of the threshold obligation: use first-barrier data
plus the linear congruence forced by matching to produce a threshold witness.
-/
def A0FirstBarrierCongruenceThresholdWitnessAutomatic : Prop :=
  ∀ ⦃t : ℕ⦄ ⦃suff : List ℕ⦄,
    A0FirstBarrierSuffix t suff →
      A0EndpointSuffixCongruence t suff →
        A0EndpointSuffixThresholdWitness t suff

theorem A0FirstBarrierThresholdWitnessAutomatic_of_congruence
    (hsolve : A0FirstBarrierCongruenceThresholdWitnessAutomatic) :
    A0FirstBarrierThresholdWitnessAutomatic := by
  intro t suff hfirst
  exact hsolve hfirst (a0FirstBarrierSuffix_congruence hfirst)

theorem a0EndpointSuffixThreshold_singleton_of_barrier
    {t e : ℕ}
    (hbarrier : A0EndpointSuffixSlopeBarrier [e]) :
    A0EndpointSuffixThreshold t [e] := by
  have hbase : 1780 < 103 * 2 ^ e := by
    unfold A0EndpointSuffixSlopeBarrier at hbarrier
    simp at hbarrier
    omega
  unfold A0EndpointSuffixThreshold
  simp only [List.length_cons, List.length_nil, zero_add, pow_one,
    Nat.reduceMul, List.sum_cons, List.sum_nil, add_zero, gt_iff_lt]
  exact lt_of_lt_of_le hbase (Nat.le_add_left _ _)

theorem a0FirstBarrierThreshold_singleton
    {t e : ℕ}
    (hfirst : A0FirstBarrierSuffix t [e]) :
    A0EndpointSuffixThreshold t [e] :=
  a0EndpointSuffixThreshold_singleton_of_barrier hfirst.barrier

/--
A concrete warning against a purely slope-barrier proof of
`A0FirstBarrierThresholdAutomatic`.

This word crosses the A0 endpoint slope barrier, but the endpoint threshold
inequality fails at `t = 0`.  Thus longer first-barrier suffixes cannot be
handled by slope arithmetic alone; a real proof must also use the
`SyracuseWordMatchesFrom` congruence information, which can force `t` into a
large residue class.
-/
def a0NaiveSlopeBarrierCounterexampleWord : List ℕ :=
  [4, 1, 2, 1, 2,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   12]

theorem a0NaiveSlopeBarrierCounterexample_crosses :
    A0EndpointSuffixSlopeBarrier a0NaiveSlopeBarrierCounterexampleWord := by
  norm_num [A0EndpointSuffixSlopeBarrier,
    a0NaiveSlopeBarrierCounterexampleWord]

theorem a0NaiveSlopeBarrierCounterexample_thresholdZeroFails :
    ¬ A0EndpointSuffixThreshold 0 a0NaiveSlopeBarrierCounterexampleWord := by
  norm_num [A0EndpointSuffixThreshold,
    a0NaiveSlopeBarrierCounterexampleWord, syracuseWordConst]

theorem a0NaiveSlopeBarrierCounterexample_thresholdOne :
    A0EndpointSuffixThreshold 1 a0NaiveSlopeBarrierCounterexampleWord := by
  norm_num [A0EndpointSuffixThreshold,
    a0NaiveSlopeBarrierCounterexampleWord, syracuseWordConst]

theorem a0NaiveSlopeBarrierCounterexample_threshold_of_match
    {t : ℕ}
    (hmatch :
      SyracuseWordMatchesFrom a0NaiveSlopeBarrierCounterexampleWord
        (593 + 1458 * t)) :
    A0EndpointSuffixThreshold t a0NaiveSlopeBarrierCounterexampleWord := by
  have hhead : syracuseExponent (593 + 1458 * t) = 4 := by
    simpa [a0NaiveSlopeBarrierCounterexampleWord] using hmatch.1
  have htpos : 1 ≤ t := by
    by_contra hnot
    have ht0 : t = 0 := by omega
    subst t
    have hzero_ne : syracuseExponent (593 + 1458 * 0) ≠ 4 := by
      have hval : padicValNat 2 1780 = 2 := by
        simpa using
          (padicValNat_two_pow_mul_odd
            (a := 2) (m := 445) (by norm_num : Odd 445))
      intro h
      rw [syracuseExponent, nu2Nat, syracuseNumerator] at h
      norm_num at h
      rw [hval] at h
      omega
    exact hzero_ne hhead
  exact
    a0EndpointSuffixThreshold_of_one_le htpos
      a0NaiveSlopeBarrierCounterexample_thresholdOne

theorem a0EndpointSuffixExit_of_suffix_scaled_contracting
    {suff : List ℕ} {t : ℕ}
    (hmatch : SyracuseWordMatchesFrom suff (593 + 1458 * t))
    (hsuffix : 0 < suff.length)
    (hscaled :
      3 ^ suff.length * (593 + 1458 * t) + syracuseWordConst suff
        < 2 ^ suff.sum * (103 + 256 * t)) :
    A0EndpointSuffixExit t := by
  refine ⟨suff, hmatch, hsuffix, ?_⟩
  have heq :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches
      suff (593 + 1458 * t) hmatch
  have hmul_lt :
      2 ^ suff.sum * evalSyracuseWord suff (593 + 1458 * t)
        < 2 ^ suff.sum * (103 + 256 * t) := by
    rwa [heq]
  exact Nat.lt_of_mul_lt_mul_left hmul_lt

theorem a0EndpointSuffix_scaled_contracting_of_threshold
    {suff : List ℕ} {t : ℕ}
    (hgap :
      1458 * 3 ^ suff.length ≤ 256 * 2 ^ suff.sum)
    (hthreshold :
      593 * 3 ^ suff.length + syracuseWordConst suff
        <
      (256 * 2 ^ suff.sum - 1458 * 3 ^ suff.length) * t
        + 103 * 2 ^ suff.sum) :
    3 ^ suff.length * (593 + 1458 * t) + syracuseWordConst suff
      < 2 ^ suff.sum * (103 + 256 * t) := by
  set L : ℕ := 1458 * 3 ^ suff.length
  set R : ℕ := 256 * 2 ^ suff.sum
  set I : ℕ := 593 * 3 ^ suff.length + syracuseWordConst suff
  set J : ℕ := 103 * 2 ^ suff.sum
  have hsum : L + (R - L) = R := Nat.add_sub_cancel' (by
    simpa [L, R] using hgap)
  have hleft :
      3 ^ suff.length * (593 + 1458 * t) + syracuseWordConst suff
        = L * t + I := by
    simp [L, I]
    ring
  have hright :
      2 ^ suff.sum * (103 + 256 * t) = R * t + J := by
    simp [R, J]
    ring
  rw [hleft, hright]
  calc
    L * t + I < L * t + ((R - L) * t + J) := by
      exact Nat.add_lt_add_left (by simpa [L, R, I, J] using hthreshold) _
    _ = (L + (R - L)) * t + J := by
      ring
    _ = R * t + J := by
      rw [hsum]

theorem a0EndpointSuffixExit_of_suffix_threshold_contracting
    {suff : List ℕ} {t : ℕ}
    (hmatch : SyracuseWordMatchesFrom suff (593 + 1458 * t))
    (hsuffix : 0 < suff.length)
    (hgap :
      1458 * 3 ^ suff.length ≤ 256 * 2 ^ suff.sum)
    (hthreshold :
      593 * 3 ^ suff.length + syracuseWordConst suff
        <
      (256 * 2 ^ suff.sum - 1458 * 3 ^ suff.length) * t
        + 103 * 2 ^ suff.sum) :
    A0EndpointSuffixExit t :=
  a0EndpointSuffixExit_of_suffix_scaled_contracting
    hmatch hsuffix
    (a0EndpointSuffix_scaled_contracting_of_threshold
      hgap hthreshold)

theorem a0EndpointSuffixExit_of_firstBarrier_threshold
    {suff : List ℕ} {t : ℕ}
    (hfirst : A0FirstBarrierSuffix t suff)
    (hthreshold : A0EndpointSuffixThreshold t suff) :
    A0EndpointSuffixExit t :=
  a0EndpointSuffixExit_of_suffix_threshold_contracting
    hfirst.match_suffix hfirst.nonempty hfirst.barrier hthreshold

theorem A0EndpointSuffixExitAll_of_firstBarrier
    (hexists : A0FirstBarrierExistsAll)
    (hauto : A0FirstBarrierThresholdAutomatic) :
    A0EndpointSuffixExitAll := by
  intro t
  rcases hexists t with ⟨suff, hfirst⟩
  exact a0EndpointSuffixExit_of_firstBarrier_threshold
    hfirst (hauto hfirst)

theorem hasStrictDescent_of_a0EndpointSuffixExit
    {t : ℕ} (hexit : A0EndpointSuffixExit t) :
    HasStrictDescent (103 + 256 * t) := by
  rcases hexit with ⟨suff, hsuffMatch, hsuffLen, hsuffDrop⟩
  have hpref :=
    a0SemanticDropCommonPrefix_matches_source_cylinder t
  have hprefixEval :=
    eval_a0SemanticDropCommonPrefix_source_cylinder t
  have hsuffMatch' :
      SyracuseWordMatchesFrom suff
        (evalSyracuseWord a0SemanticDropCommonPrefix (103 + 256 * t)) := by
    simpa [hprefixEval] using hsuffMatch
  have hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suff)
        (103 + 256 * t) :=
    SyracuseWordMatchesFrom_append_of_matches
      a0SemanticDropCommonPrefix suff (103 + 256 * t)
      hpref hsuffMatch'
  have hdrop :
      evalSyracuseWord suff
          (evalSyracuseWord a0SemanticDropCommonPrefix (103 + 256 * t))
        < 103 + 256 * t := by
    simpa [hprefixEval] using hsuffDrop
  exact
    hasStrictDescent_of_directDropAt
      (directDropAt_of_suffix_after_prefix_matches_eval_lt
        hmatch hsuffLen hdrop)

theorem hasStrictDescent_a0Cylinder_of_endpointSuffixExitAll
    (hexitAll : A0EndpointSuffixExitAll) (t : ℕ) :
    HasStrictDescent (103 + 256 * t) :=
  hasStrictDescent_of_a0EndpointSuffixExit (hexitAll t)

/--
After the common prefix, the next Syracuse exponent is controlled by the
2-adic valuation of the affine form `890 + 2187*t`.
-/
theorem syracuseExponent_a0CommonPrefix_endpoint
    (t : ℕ) :
    syracuseExponent (593 + 1458 * t)
      = padicValNat 2 (890 + 2187 * t) + 1 := by
  have hnum :
      syracuseNumerator (593 + 1458 * t)
        = 2 * (890 + 2187 * t) := by
    unfold syracuseNumerator
    ring
  have hne : 890 + 2187 * t ≠ 0 := by omega
  rw [syracuseExponent, nu2Nat, hnum]
  rw [padicValNat_base_mul (p := 2) (n := 890 + 2187 * t)
    (by norm_num : 1 < 2) hne]

theorem syracuseExponent_a0CommonPrefix_endpoint_of_odd_t
    {t : ℕ} (hodd : Odd t) :
    syracuseExponent (593 + 1458 * t) = 1 := by
  rcases hodd with ⟨r, hr⟩
  have hodd_affine : Odd (890 + 2187 * t) := by
    rw [hr]
    exact ⟨1538 + 2187 * r, by ring⟩
  have hnotdvd : ¬ 2 ∣ 890 + 2187 * t := by
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hodd_affine)
      (even_iff_two_dvd.mpr hdiv)
  have hzero : padicValNat 2 (890 + 2187 * t) = 0 :=
    padicValNat.eq_zero_of_not_dvd hnotdvd
  rw [syracuseExponent_a0CommonPrefix_endpoint, hzero]

theorem syracuseExponent_a0CommonPrefix_endpoint_even_t
    (u : ℕ) :
    syracuseExponent (593 + 1458 * (2 * u))
      = padicValNat 2 (445 + 2187 * u) + 2 := by
  have hnum :
      syracuseNumerator (593 + 1458 * (2 * u))
        = 2 ^ 2 * (445 + 2187 * u) := by
    unfold syracuseNumerator
    norm_num
    ring
  have hne : 445 + 2187 * u ≠ 0 := by omega
  rw [syracuseExponent, nu2Nat, hnum]
  rw [padicValNat_base_pow_mul (p := 2) (n := 445 + 2187 * u)
    (by norm_num : 1 < 2) hne 2]

theorem a0SemanticDropCommonPrefix_affine_of_matches
    {n : ℕ}
    (hmatch : SyracuseWordMatchesFrom a0SemanticDropCommonPrefix n) :
    128 * evalSyracuseWord a0SemanticDropCommonPrefix n = 729 * n + 817 := by
  have h :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches
      a0SemanticDropCommonPrefix n hmatch
  norm_num [a0SemanticDropCommonPrefix, syracuseWordConst] at h
  simpa using h

theorem directDropAt_of_a0CommonPrefix_suffix_scaled_contracting
    {suff : List ℕ} {n : ℕ}
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suff) n)
    (hsuffix : 0 < suff.length)
    (hscaled :
      3 ^ suff.length * (729 * n + 817) + 128 * syracuseWordConst suff
        < 128 * (2 ^ suff.sum * n)) :
    DirectDropAt (a0SemanticDropCommonPrefix ++ suff).length n := by
  have hprefmatch :
      SyracuseWordMatchesFrom a0SemanticDropCommonPrefix n :=
    (SyracuseWordMatchesFrom_append
      a0SemanticDropCommonPrefix suff n hmatch).1
  have hpref := a0SemanticDropCommonPrefix_affine_of_matches hprefmatch
  have hmul :
      128 *
          (3 ^ suff.length * evalSyracuseWord a0SemanticDropCommonPrefix n
            + syracuseWordConst suff)
        < 128 * (2 ^ suff.sum * n) := by
    calc
      128 *
          (3 ^ suff.length * evalSyracuseWord a0SemanticDropCommonPrefix n
            + syracuseWordConst suff)
          = 3 ^ suff.length
              * (128 * evalSyracuseWord a0SemanticDropCommonPrefix n)
            + 128 * syracuseWordConst suff := by
              ring
      _ = 3 ^ suff.length * (729 * n + 817)
            + 128 * syracuseWordConst suff := by
              rw [hpref]
      _ < 128 * (2 ^ suff.sum * n) := hscaled
  have hcontract :
      3 ^ suff.length * evalSyracuseWord a0SemanticDropCommonPrefix n
          + syracuseWordConst suff
        < 2 ^ suff.sum * n :=
    Nat.lt_of_mul_lt_mul_left hmul
  exact
    directDropAt_of_suffix_after_prefix_affine_contracting
      hmatch hsuffix hcontract

theorem a0CommonPrefix_suffix_scaled_contracting_of_threshold
    {suff : List ℕ} {n : ℕ}
    (hgap :
      729 * 3 ^ suff.length ≤ 128 * 2 ^ suff.sum)
    (hthreshold :
      817 * 3 ^ suff.length + 128 * syracuseWordConst suff
        < (128 * 2 ^ suff.sum - 729 * 3 ^ suff.length) * n) :
    3 ^ suff.length * (729 * n + 817) + 128 * syracuseWordConst suff
      < 128 * (2 ^ suff.sum * n) := by
  set L : ℕ := 729 * 3 ^ suff.length
  set R : ℕ := 128 * 2 ^ suff.sum
  set I : ℕ := 817 * 3 ^ suff.length + 128 * syracuseWordConst suff
  have hsum : L + (R - L) = R := Nat.add_sub_cancel' (by
    simpa [L, R] using hgap)
  have hleft :
      3 ^ suff.length * (729 * n + 817) + 128 * syracuseWordConst suff
        = L * n + I := by
    simp [L, I]
    ring
  have hright : 128 * (2 ^ suff.sum * n) = R * n := by
    simp [R]
    ring
  rw [hleft, hright]
  calc
    L * n + I < L * n + (R - L) * n := by
      exact Nat.add_lt_add_left (by simpa [L, R, I] using hthreshold) _
    _ = (L + (R - L)) * n := by
      ring
    _ = R * n := by
      rw [hsum]

theorem directDropAt_of_a0CommonPrefix_suffix_threshold_contracting
    {suff : List ℕ} {n : ℕ}
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suff) n)
    (hsuffix : 0 < suff.length)
    (hgap :
      729 * 3 ^ suff.length ≤ 128 * 2 ^ suff.sum)
    (hthreshold :
      817 * 3 ^ suff.length + 128 * syracuseWordConst suff
        < (128 * 2 ^ suff.sum - 729 * 3 ^ suff.length) * n) :
    DirectDropAt (a0SemanticDropCommonPrefix ++ suff).length n :=
  directDropAt_of_a0CommonPrefix_suffix_scaled_contracting
    hmatch hsuffix
    (a0CommonPrefix_suffix_scaled_contracting_of_threshold
      hgap hthreshold)

/--
Parametric cutoff version of the A0 common-prefix suffix criterion.

The finite small-case argument is supplied as a hypothesis.  This avoids
mistaking the observed T14 cutoff `455` for a structural constant.
-/
theorem hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_cutoff
    {cutoff : ℕ} {suff : List ℕ} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hsmall :
      ∀ m : ℕ, 0 < m → Odd m → m ≠ 1 → m < cutoff →
        HasStrictDescent m)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suff) n)
    (hsuffix : 0 < suff.length)
    (hgap :
      729 * 3 ^ suff.length ≤ 128 * 2 ^ suff.sum)
    (hthresholdCutoff :
      817 * 3 ^ suff.length + 128 * syracuseWordConst suff
        < (128 * 2 ^ suff.sum - 729 * 3 ^ suff.length) * cutoff) :
    HasStrictDescent n := by
  by_cases hlt : n < cutoff
  · exact hsmall n hn hodd hn1 hlt
  · have hcutoff : cutoff ≤ n := Nat.le_of_not_gt hlt
    have hthreshold :
        817 * 3 ^ suff.length + 128 * syracuseWordConst suff
          < (128 * 2 ^ suff.sum - 729 * 3 ^ suff.length) * n := by
      exact lt_of_lt_of_le hthresholdCutoff
        (Nat.mul_le_mul_left
          (128 * 2 ^ suff.sum - 729 * 3 ^ suff.length) hcutoff)
    exact hasStrictDescent_of_directDropAt
      (directDropAt_of_a0CommonPrefix_suffix_threshold_contracting
        hmatch hsuffix hgap hthreshold)

theorem hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_455
    {suff : List ℕ} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suff) n)
    (hsuffix : 0 < suff.length)
    (hgap :
      729 * 3 ^ suff.length ≤ 128 * 2 ^ suff.sum)
    (hthreshold455 :
      817 * 3 ^ suff.length + 128 * syracuseWordConst suff
        < (128 * 2 ^ suff.sum - 729 * 3 ^ suff.length) * 455) :
    HasStrictDescent n :=
  hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_cutoff
    hn hodd hn1
    (fun _m hm hoddm hm1 hltm =>
      hasStrictDescent_of_odd_lt_455 hm hoddm hm1 hltm)
    hmatch hsuffix hgap hthreshold455

theorem hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_464
    {suff : List ℕ} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suff) n)
    (hsuffix : 0 < suff.length)
    (hgap :
      729 * 3 ^ suff.length ≤ 128 * 2 ^ suff.sum)
    (hthreshold464 :
      817 * 3 ^ suff.length + 128 * syracuseWordConst suff
        < (128 * 2 ^ suff.sum - 729 * 3 ^ suff.length) * 464) :
    HasStrictDescent n :=
  hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_cutoff
    hn hodd hn1
    (fun _m hm hoddm hm1 hltm =>
      hasStrictDescent_of_odd_lt_464 hm hoddm hm1 hltm)
    hmatch hsuffix hgap hthreshold464

theorem hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_648
    {suff : List ℕ} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suff) n)
    (hsuffix : 0 < suff.length)
    (hgap :
      729 * 3 ^ suff.length ≤ 128 * 2 ^ suff.sum)
    (hthreshold648 :
      817 * 3 ^ suff.length + 128 * syracuseWordConst suff
        < (128 * 2 ^ suff.sum - 729 * 3 ^ suff.length) * 648) :
    HasStrictDescent n :=
  hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_cutoff
    hn hodd hn1
    (fun _m hm hoddm hm1 hltm =>
      hasStrictDescent_of_odd_lt_648 hm hoddm hm1 hltm)
    hmatch hsuffix hgap hthreshold648

/--
A compact proof-facing certificate row for the observed A0 semantic-drop
suffixes.

The script-side row records the suffix, the explicit slope gap
`128*2^sum(s) - 729*3^len(s)`, and the first threshold at which the strict
scaled contraction inequality holds.  The validity predicate below is what a
future generated suffix import should prove row-by-row.
-/
structure A0SemanticSuffixCertificate where
  suffix : List ℕ
  slopeGap : ℕ
  thresholdMinN : ℕ
  deriving Repr, DecidableEq

namespace A0SemanticSuffixCertificate

/-- Row-level validity at an arbitrary finite small-case cutoff. -/
def ValidAtCutoff (C : A0SemanticSuffixCertificate) (cutoff : ℕ) : Prop :=
  0 < C.suffix.length
    ∧ 729 * 3 ^ C.suffix.length ≤ 128 * 2 ^ C.suffix.sum
    ∧ C.slopeGap = 128 * 2 ^ C.suffix.sum - 729 * 3 ^ C.suffix.length
    ∧ 817 * 3 ^ C.suffix.length + 128 * syracuseWordConst C.suffix
        < C.slopeGap * C.thresholdMinN
    ∧ C.thresholdMinN ≤ cutoff

/--
The exact row-level condition needed to use the A0 common-prefix suffix
criterion above with the current finite small-case cutoff `455`.
-/
def ValidAt455 (C : A0SemanticSuffixCertificate) : Prop :=
  C.ValidAtCutoff 455

/-- Row-level validity at cutoff `464`, currently needed by the T16 audit. -/
def ValidAt464 (C : A0SemanticSuffixCertificate) : Prop :=
  C.ValidAtCutoff 464

theorem threshold455_of_validAt455
    {C : A0SemanticSuffixCertificate} (hC : C.ValidAt455) :
    817 * 3 ^ C.suffix.length + 128 * syracuseWordConst C.suffix
      < (128 * 2 ^ C.suffix.sum - 729 * 3 ^ C.suffix.length) * 455 := by
  rcases hC with ⟨_hlen, _hgap, hgapEq, hthreshold, hle455⟩
  rw [← hgapEq]
  exact lt_of_lt_of_le hthreshold
    (Nat.mul_le_mul_left C.slopeGap hle455)

theorem hasStrictDescent_of_validAt455
    {C : A0SemanticSuffixCertificate} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ C.suffix) n)
    (hC : C.ValidAt455) :
    HasStrictDescent n := by
  rcases hC with ⟨hlen, hgap, hgapEq, hthreshold, hle455⟩
  have hthreshold455 :
      817 * 3 ^ C.suffix.length + 128 * syracuseWordConst C.suffix
        < (128 * 2 ^ C.suffix.sum - 729 * 3 ^ C.suffix.length) * 455 := by
    rw [← hgapEq]
    exact lt_of_lt_of_le hthreshold
      (Nat.mul_le_mul_left C.slopeGap hle455)
  exact
    hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_455
      hn hodd hn1 hmatch hlen hgap hthreshold455

theorem hasStrictDescent_of_validAtCutoff
    {cutoff : ℕ} {C : A0SemanticSuffixCertificate} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hsmall :
      ∀ m : ℕ, 0 < m → Odd m → m ≠ 1 → m < cutoff →
        HasStrictDescent m)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ C.suffix) n)
    (hC : C.ValidAtCutoff cutoff) :
    HasStrictDescent n := by
  rcases hC with ⟨hlen, hgap, hgapEq, hthreshold, hleCutoff⟩
  have hthresholdCutoff :
      817 * 3 ^ C.suffix.length + 128 * syracuseWordConst C.suffix
        < (128 * 2 ^ C.suffix.sum - 729 * 3 ^ C.suffix.length)
            * cutoff := by
    rw [← hgapEq]
    exact lt_of_lt_of_le hthreshold
      (Nat.mul_le_mul_left C.slopeGap hleCutoff)
  exact
    hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_cutoff
      hn hodd hn1 hsmall hmatch hlen hgap hthresholdCutoff

theorem hasStrictDescent_of_validAt464
    {C : A0SemanticSuffixCertificate} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ C.suffix) n)
    (hC : C.ValidAt464) :
    HasStrictDescent n :=
  hasStrictDescent_of_validAtCutoff
    hn hodd hn1
    (fun _m hm hoddm hm1 hltm =>
      hasStrictDescent_of_odd_lt_464 hm hoddm hm1 hltm)
    hmatch hC

end A0SemanticSuffixCertificate

/--
A coarser certificate for a whole group of suffixes with the same
`(length, sum)` pair.

Such a row stores the largest observed `syracuseWordConst` and the largest
threshold in that group.  It is useful only if future generated data also
proves that each listed suffix belongs to the pair and has constant bounded
by `suffixConstMax`.
-/
structure A0SemanticSuffixPairCertificate where
  suffixLength : ℕ
  suffixSum : ℕ
  suffixConstMax : ℕ
  slopeGap : ℕ
  thresholdMinNMax : ℕ
  deriving Repr, DecidableEq

namespace A0SemanticSuffixPairCertificate

/-- Row-level validity for a pair-compressed certificate at any cutoff. -/
def ValidAtCutoff
    (P : A0SemanticSuffixPairCertificate) (cutoff : ℕ) : Prop :=
  0 < P.suffixLength
    ∧ 729 * 3 ^ P.suffixLength ≤ 128 * 2 ^ P.suffixSum
    ∧ P.slopeGap = 128 * 2 ^ P.suffixSum - 729 * 3 ^ P.suffixLength
    ∧ 817 * 3 ^ P.suffixLength + 128 * P.suffixConstMax
        < P.slopeGap * P.thresholdMinNMax
    ∧ P.thresholdMinNMax ≤ cutoff

/-- Row-level validity for the pair-compressed A0 semantic-drop certificate. -/
def ValidAt455 (P : A0SemanticSuffixPairCertificate) : Prop :=
  P.ValidAtCutoff 455

/-- Row-level validity at cutoff `464`, currently needed by the T16 audit. -/
def ValidAt464 (P : A0SemanticSuffixPairCertificate) : Prop :=
  P.ValidAtCutoff 464

instance (P : A0SemanticSuffixPairCertificate) (cutoff : ℕ) :
    Decidable (P.ValidAtCutoff cutoff) := by
  unfold ValidAtCutoff
  infer_instance

instance (P : A0SemanticSuffixPairCertificate) : Decidable P.ValidAt455 := by
  unfold ValidAt455
  infer_instance

/-- Computable checker for row-level validity at an arbitrary cutoff. -/
def validAtCutoffBool
    (cutoff : ℕ) (P : A0SemanticSuffixPairCertificate) : Bool :=
  decide (P.ValidAtCutoff cutoff)

theorem validAtCutoff_of_validAtCutoffBool_eq_true
    {cutoff : ℕ} {P : A0SemanticSuffixPairCertificate}
    (hP : validAtCutoffBool cutoff P = true) :
    P.ValidAtCutoff cutoff := by
  rw [validAtCutoffBool] at hP
  exact of_decide_eq_true hP

/-- Computable checker for a generated list of pair rows at a cutoff. -/
def allValidAtCutoffBool
    (cutoff : ℕ) (rows : List A0SemanticSuffixPairCertificate) : Bool :=
  rows.all (validAtCutoffBool cutoff)

theorem validAtCutoff_of_mem_of_allValidAtCutoffBool
    {cutoff : ℕ} {rows : List A0SemanticSuffixPairCertificate}
    (hrows : allValidAtCutoffBool cutoff rows = true)
    {P : A0SemanticSuffixPairCertificate}
    (hmem : P ∈ rows) :
    P.ValidAtCutoff cutoff := by
  have hall :
      ∀ Q ∈ rows, validAtCutoffBool cutoff Q = true := by
    simpa [allValidAtCutoffBool] using hrows
  exact validAtCutoff_of_validAtCutoffBool_eq_true (hall P hmem)

/-- Computable checker for the row-level `ValidAt455` predicate. -/
def validAt455Bool (P : A0SemanticSuffixPairCertificate) : Bool :=
  decide P.ValidAt455

theorem validAt455_of_validAt455Bool_eq_true
    {P : A0SemanticSuffixPairCertificate}
    (hP : P.validAt455Bool = true) :
    P.ValidAt455 := by
  rw [validAt455Bool] at hP
  exact of_decide_eq_true hP

/-- Computable checker for a generated list of pair-certificate rows. -/
def allValidAt455Bool (rows : List A0SemanticSuffixPairCertificate) : Bool :=
  rows.all validAt455Bool

theorem validAt455_of_mem_of_allValidAt455Bool
    {rows : List A0SemanticSuffixPairCertificate}
    (hrows : allValidAt455Bool rows = true)
    {P : A0SemanticSuffixPairCertificate}
    (hmem : P ∈ rows) :
    P.ValidAt455 := by
  have hall : ∀ Q ∈ rows, Q.validAt455Bool = true := by
    simpa [allValidAt455Bool] using hrows
  exact validAt455_of_validAt455Bool_eq_true (hall P hmem)

/-- Convert a pair row to the pointwise suffix row for a concrete suffix. -/
def toSuffixCertificate
    (P : A0SemanticSuffixPairCertificate) (suffix : List ℕ) :
    A0SemanticSuffixCertificate :=
  { suffix := suffix
    slopeGap := P.slopeGap
    thresholdMinN := P.thresholdMinNMax }

theorem suffix_validAt455_of_validAt455
    {P : A0SemanticSuffixPairCertificate} {suffix : List ℕ}
    (hP : P.ValidAt455)
    (hlen : suffix.length = P.suffixLength)
    (hsum : suffix.sum = P.suffixSum)
    (hconst : syracuseWordConst suffix ≤ P.suffixConstMax) :
    (P.toSuffixCertificate suffix).ValidAt455 := by
  rcases hP with ⟨hlenP, hgapP, hgapEqP, hthresholdP, hle455⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [toSuffixCertificate, hlen] using hlenP
  · simpa [toSuffixCertificate, hlen, hsum] using hgapP
  · simpa [toSuffixCertificate, hlen, hsum] using hgapEqP
  · have hleft :
        817 * 3 ^ suffix.length + 128 * syracuseWordConst suffix
          ≤ 817 * 3 ^ P.suffixLength + 128 * P.suffixConstMax := by
      exact Nat.add_le_add
        (by rw [hlen])
        (Nat.mul_le_mul_left 128 hconst)
    exact lt_of_le_of_lt hleft hthresholdP
  · exact hle455

theorem suffix_validAtCutoff_of_validAtCutoff
    {cutoff : ℕ} {P : A0SemanticSuffixPairCertificate} {suffix : List ℕ}
    (hP : P.ValidAtCutoff cutoff)
    (hlen : suffix.length = P.suffixLength)
    (hsum : suffix.sum = P.suffixSum)
    (hconst : syracuseWordConst suffix ≤ P.suffixConstMax) :
    (P.toSuffixCertificate suffix).ValidAtCutoff cutoff := by
  rcases hP with ⟨hlenP, hgapP, hgapEqP, hthresholdP, hleCutoff⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [toSuffixCertificate, hlen] using hlenP
  · simpa [toSuffixCertificate, hlen, hsum] using hgapP
  · simpa [toSuffixCertificate, hlen, hsum] using hgapEqP
  · have hleft :
        817 * 3 ^ suffix.length + 128 * syracuseWordConst suffix
          ≤ 817 * 3 ^ P.suffixLength + 128 * P.suffixConstMax := by
      exact Nat.add_le_add
        (by rw [hlen])
        (Nat.mul_le_mul_left 128 hconst)
    exact lt_of_le_of_lt hleft hthresholdP
  · exact hleCutoff

theorem hasStrictDescent_of_validAt455
    {P : A0SemanticSuffixPairCertificate} {suffix : List ℕ} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suffix) n)
    (hP : P.ValidAt455)
    (hlen : suffix.length = P.suffixLength)
    (hsum : suffix.sum = P.suffixSum)
    (hconst : syracuseWordConst suffix ≤ P.suffixConstMax) :
    HasStrictDescent n := by
  exact
    A0SemanticSuffixCertificate.hasStrictDescent_of_validAt455
      hn hodd hn1 hmatch
      (suffix_validAt455_of_validAt455 hP hlen hsum hconst)

theorem hasStrictDescent_of_validAtCutoff
    {cutoff : ℕ}
    {P : A0SemanticSuffixPairCertificate} {suffix : List ℕ} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hsmall :
      ∀ m : ℕ, 0 < m → Odd m → m ≠ 1 → m < cutoff →
        HasStrictDescent m)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suffix) n)
    (hP : P.ValidAtCutoff cutoff)
    (hlen : suffix.length = P.suffixLength)
    (hsum : suffix.sum = P.suffixSum)
    (hconst : syracuseWordConst suffix ≤ P.suffixConstMax) :
    HasStrictDescent n := by
  exact
    A0SemanticSuffixCertificate.hasStrictDescent_of_validAtCutoff
      hn hodd hn1 hsmall hmatch
      (suffix_validAtCutoff_of_validAtCutoff hP hlen hsum hconst)

theorem hasStrictDescent_of_validAt464
    {P : A0SemanticSuffixPairCertificate} {suffix : List ℕ} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suffix) n)
    (hP : P.ValidAt464)
    (hlen : suffix.length = P.suffixLength)
    (hsum : suffix.sum = P.suffixSum)
    (hconst : syracuseWordConst suffix ≤ P.suffixConstMax) :
    HasStrictDescent n :=
  hasStrictDescent_of_validAtCutoff
    hn hodd hn1
    (fun _m hm hoddm hm1 hltm =>
      hasStrictDescent_of_odd_lt_464 hm hoddm hm1 hltm)
    hmatch hP hlen hsum hconst

end A0SemanticSuffixPairCertificate

/--
Generic assignment of one concrete A0 semantic-drop suffix to a row of an
arbitrary finite pair-certificate table.

The table validity and cutoff-dependent small-exception theorem are supplied
to the use theorem below.  This keeps the proof-facing object independent of
the particular prefix depth used to generate the finite rows.
-/
structure A0SemanticSuffixPairCover
    (rows : List A0SemanticSuffixPairCertificate) where
  suffix : List ℕ
  pair : A0SemanticSuffixPairCertificate
  pairMem : pair ∈ rows
  lengthEq : suffix.length = pair.suffixLength
  sumEq : suffix.sum = pair.suffixSum
  constLe : syracuseWordConst suffix ≤ pair.suffixConstMax

theorem hasStrictDescent_of_a0SemanticSuffixPairCoverAtCutoff
    {rows : List A0SemanticSuffixPairCertificate} {cutoff : ℕ}
    {C : A0SemanticSuffixPairCover rows} {n : ℕ}
    (hrows :
      A0SemanticSuffixPairCertificate.allValidAtCutoffBool cutoff rows = true)
    (hsmall :
      ∀ m : ℕ, 0 < m → Odd m → m ≠ 1 → m < cutoff →
        HasStrictDescent m)
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ C.suffix) n) :
    HasStrictDescent n := by
  have hP :
      C.pair.ValidAtCutoff cutoff :=
    A0SemanticSuffixPairCertificate.validAtCutoff_of_mem_of_allValidAtCutoffBool
      hrows C.pairMem
  exact
    A0SemanticSuffixPairCertificate.hasStrictDescent_of_validAtCutoff
      hn hodd hn1 hsmall hmatch hP C.lengthEq C.sumEq C.constLe

/--
Generic source-level cover object for the A0 semantic-drop path.

Providing this object for a concrete source `n`, together with a valid finite
pair table at a cutoff and a small-exception theorem below that cutoff, is
enough to prove strict descent from `n`.
-/
structure A0SemanticDropSourcePairCover
    (rows : List A0SemanticSuffixPairCertificate) (n : ℕ) where
  positive : 0 < n
  odd : Odd n
  notOne : n ≠ 1
  suffixCover : A0SemanticSuffixPairCover rows
  wordMatch :
    SyracuseWordMatchesFrom
      (a0SemanticDropCommonPrefix ++ suffixCover.suffix) n

theorem hasStrictDescent_of_a0SemanticDropSourcePairCoverAtCutoff
    {rows : List A0SemanticSuffixPairCertificate} {cutoff n : ℕ}
    (hrows :
      A0SemanticSuffixPairCertificate.allValidAtCutoffBool cutoff rows = true)
    (hsmall :
      ∀ m : ℕ, 0 < m → Odd m → m ≠ 1 → m < cutoff →
        HasStrictDescent m)
    (C : A0SemanticDropSourcePairCover rows n) :
    HasStrictDescent n :=
  hasStrictDescent_of_a0SemanticSuffixPairCoverAtCutoff
    hrows hsmall C.positive C.odd C.notOne C.wordMatch

/--
The remaining A0 source-cover datum after the common prefix has been proved
on the source cylinder `103 + 256*t`.

It asks for a suffix word starting from the endpoint `593 + 1458*t`, together
with an assignment of that suffix to a finite pair-certificate table.
-/
structure A0EndpointSuffixPairCover
    (rows : List A0SemanticSuffixPairCertificate) (t : ℕ) where
  suffixCover : A0SemanticSuffixPairCover rows
  suffixMatch :
    SyracuseWordMatchesFrom suffixCover.suffix (593 + 1458 * t)

namespace A0EndpointSuffixPairCover

def toSourceCover
    {rows : List A0SemanticSuffixPairCertificate} {t : ℕ}
    (C : A0EndpointSuffixPairCover rows t) :
    A0SemanticDropSourcePairCover rows (103 + 256 * t) := by
  refine
    { positive := ?_
      odd := ?_
      notOne := ?_
      suffixCover := C.suffixCover
      wordMatch := ?_ }
  · omega
  · exact ⟨51 + 128 * t, by ring⟩
  · omega
  · have hpref :=
      a0SemanticDropCommonPrefix_matches_source_cylinder t
    have hsuffix' :
        SyracuseWordMatchesFrom C.suffixCover.suffix
          (evalSyracuseWord a0SemanticDropCommonPrefix
            (103 + 256 * t)) := by
      simpa [eval_a0SemanticDropCommonPrefix_source_cylinder t]
        using C.suffixMatch
    exact
      SyracuseWordMatchesFrom_append_of_matches
        a0SemanticDropCommonPrefix C.suffixCover.suffix
        (103 + 256 * t) hpref hsuffix'

theorem hasStrictDescent_atCutoff
    {rows : List A0SemanticSuffixPairCertificate} {cutoff t : ℕ}
    (hrows :
      A0SemanticSuffixPairCertificate.allValidAtCutoffBool cutoff rows = true)
    (hsmall :
      ∀ m : ℕ, 0 < m → Odd m → m ≠ 1 → m < cutoff →
        HasStrictDescent m)
    (C : A0EndpointSuffixPairCover rows t) :
    HasStrictDescent (103 + 256 * t) :=
  hasStrictDescent_of_a0SemanticDropSourcePairCoverAtCutoff
    hrows hsmall C.toSourceCover

end A0EndpointSuffixPairCover

/--
One finite pair-certificate table together with the cutoff theorem needed to
use it.

This is still a local A0 semantic-drop specification.  It does not assert
that every source has a cover into `rows`; it only packages the part of the
argument that is independent of the source.
-/
structure A0SemanticDropTableSpec where
  rows : List A0SemanticSuffixPairCertificate
  cutoff : ℕ
  rowsValid :
    A0SemanticSuffixPairCertificate.allValidAtCutoffBool cutoff rows = true
  smallStrictDescent :
    ∀ m : ℕ, 0 < m → Odd m → m ≠ 1 → m < cutoff →
      HasStrictDescent m

namespace A0SemanticDropTableSpec

/-- Source-cover data associated with a fixed semantic-drop table. -/
def SourceCover (T : A0SemanticDropTableSpec) (n : ℕ) : Type :=
  A0SemanticDropSourcePairCover T.rows n

/-- Endpoint-suffix cover data for the A0 source cylinder. -/
def EndpointSuffixCover (T : A0SemanticDropTableSpec) (t : ℕ) : Type :=
  A0EndpointSuffixPairCover T.rows t

theorem hasStrictDescent_of_sourceCover
    (T : A0SemanticDropTableSpec) {n : ℕ}
    (C : T.SourceCover n) :
    HasStrictDescent n :=
  hasStrictDescent_of_a0SemanticDropSourcePairCoverAtCutoff
    T.rowsValid T.smallStrictDescent C

theorem hasStrictDescent_of_endpointSuffixCover
    (T : A0SemanticDropTableSpec) {t : ℕ}
    (C : T.EndpointSuffixCover t) :
    HasStrictDescent (103 + 256 * t) :=
  A0EndpointSuffixPairCover.hasStrictDescent_atCutoff
    T.rowsValid T.smallStrictDescent C

end A0SemanticDropTableSpec

/-- Evaluate a finite chain of Syracuse exponent words on `n`. -/
def evalSyracuseWordChain : List (List ℕ) → ℕ → ℕ
  | [], n => n
  | w :: rest, n => evalSyracuseWordChain rest (evalSyracuseWord w n)

/--
Total accelerated length of a finite chain of Syracuse exponent words.

The recursive order is chosen to match Mathlib's orientation for
`Function.iterate_add`: `f^[m+n] = f^[m] ∘ f^[n]`.
-/
def syracuseWordChainLength : List (List ℕ) → ℕ
  | [] => 0
  | w :: rest => syracuseWordChainLength rest + w.length

/--
The actual accelerated orbit of `n` matches a finite chain of exponent words.

Each following word is matched from the endpoint of the previous evaluated
word.
-/
def SyracuseWordChainMatchesFrom : List (List ℕ) → ℕ → Prop
  | [], _n => True
  | w :: rest, n =>
      SyracuseWordMatchesFrom w n
        ∧ SyracuseWordChainMatchesFrom rest (evalSyracuseWord w n)

/--
If the actual accelerated orbit matches a finite chain of exponent words,
then evaluating the chain equals the corresponding iterate of `S`.
-/
theorem evalSyracuseWordChain_eq_iterate_of_matches :
    ∀ (ws : List (List ℕ)) (n : ℕ),
      SyracuseWordChainMatchesFrom ws n →
      evalSyracuseWordChain ws n = S^[syracuseWordChainLength ws] n
  | [], _n, _h => by
      simp [evalSyracuseWordChain, syracuseWordChainLength]
  | w :: rest, n, h => by
      rcases h with ⟨hw, hrest⟩
      have hword := evalSyracuseWord_eq_iterate_of_matches w n hw
      have ih := evalSyracuseWordChain_eq_iterate_of_matches
        rest (evalSyracuseWord w n) hrest
      calc
        evalSyracuseWordChain (w :: rest) n
            = evalSyracuseWordChain rest (evalSyracuseWord w n) := by
                simp [evalSyracuseWordChain]
        _ = S^[syracuseWordChainLength rest] (evalSyracuseWord w n) := ih
        _ = S^[syracuseWordChainLength rest] (S^[w.length] n) := by
                rw [hword]
        _ = S^[syracuseWordChainLength (w :: rest)] n := by
                simp [syracuseWordChainLength, Function.iterate_add,
                  Function.comp_apply]

/--
A matched nonempty finite chain of Syracuse words whose evaluated endpoint is
below the start gives a concrete direct drop from the start.
-/
theorem directDropAt_of_word_chain_matches_eval_lt
    {ws : List (List ℕ)} {n : ℕ}
    (hmatch : SyracuseWordChainMatchesFrom ws n)
    (hlen : 0 < syracuseWordChainLength ws)
    (hlt : evalSyracuseWordChain ws n < n) :
    DirectDropAt (syracuseWordChainLength ws) n := by
  have heq := evalSyracuseWordChain_eq_iterate_of_matches ws n hmatch
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hlen) with ⟨k, hk⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hk]
    exact syracuse_iterate_succ_pos k n
  · rw [hk]
    exact syracuse_iterate_succ_odd k n
  · rw [← heq]
    exact hlt

/-!
### Local affine return coordinates

The A0 return-branch diagnostics use local coordinates of the form
`source_t = q*u+r` and `next_t = a*u+b`.  The following tiny lemma records a
negative but useful fact: if `a >= q` and `b >= r`, then this branch cannot
itself be a strict descent in the same local `t` coordinate, nor after
embedding `t` back into a fixed residue class `residue + modulus*t`.
-/

/-- A one-parameter affine branch in a local `t` coordinate. -/
structure AffineTBranch where
  q : ℕ
  r : ℕ
  a : ℕ
  b : ℕ

namespace AffineTBranch

/-- Source coordinate `t = q*u+r`. -/
def sourceT (B : AffineTBranch) (u : ℕ) : ℕ :=
  B.q * u + B.r

/-- Return coordinate `t' = a*u+b`. -/
def nextT (B : AffineTBranch) (u : ℕ) : ℕ :=
  B.a * u + B.b

/-- Coefficientwise non-decrease in the local `t` coordinate. -/
def CoeffNondecreasing (B : AffineTBranch) : Prop :=
  B.q ≤ B.a ∧ B.r ≤ B.b

theorem sourceT_le_nextT_of_coeffNondecreasing
    {B : AffineTBranch} (hB : B.CoeffNondecreasing) (u : ℕ) :
    B.sourceT u ≤ B.nextT u := by
  exact Nat.add_le_add
    (Nat.mul_le_mul_right u hB.1)
    hB.2

theorem not_nextT_lt_sourceT_of_coeffNondecreasing
    {B : AffineTBranch} (hB : B.CoeffNondecreasing) (u : ℕ) :
    ¬ B.nextT u < B.sourceT u :=
  not_lt_of_ge (sourceT_le_nextT_of_coeffNondecreasing hB u)

/-- Embed a local `t` coordinate into a fixed residue class. -/
def localInteger (residue modulus t : ℕ) : ℕ :=
  residue + modulus * t

theorem a0SemanticDropCommonPrefix_matches_localInteger_source
    (t : ℕ) :
    SyracuseWordMatchesFrom a0SemanticDropCommonPrefix
      (localInteger 103 256 t) := by
  simpa [localInteger] using
    a0SemanticDropCommonPrefix_matches_source_cylinder t

theorem eval_a0SemanticDropCommonPrefix_localInteger_source
    (t : ℕ) :
    evalSyracuseWord a0SemanticDropCommonPrefix
        (localInteger 103 256 t)
      = 593 + 1458 * t := by
  simpa [localInteger] using
    eval_a0SemanticDropCommonPrefix_source_cylinder t

def a0SemanticDropSourcePairCover_of_localInteger_suffixCover
    {rows : List A0SemanticSuffixPairCertificate} {t : ℕ}
    (C : A0SemanticSuffixPairCover rows)
    (hsuffix :
      SyracuseWordMatchesFrom C.suffix (593 + 1458 * t)) :
    A0SemanticDropSourcePairCover rows (localInteger 103 256 t) := by
  refine
    { positive := ?_
      odd := ?_
      notOne := ?_
      suffixCover := C
      wordMatch := ?_ }
  · unfold localInteger
    omega
  · unfold localInteger
    exact ⟨51 + 128 * t, by ring⟩
  · unfold localInteger
    omega
  · have hpref :=
      a0SemanticDropCommonPrefix_matches_localInteger_source t
    have hsuffix' :
        SyracuseWordMatchesFrom C.suffix
          (evalSyracuseWord a0SemanticDropCommonPrefix
            (localInteger 103 256 t)) := by
      simpa [eval_a0SemanticDropCommonPrefix_localInteger_source t]
        using hsuffix
    exact
      SyracuseWordMatchesFrom_append_of_matches
        a0SemanticDropCommonPrefix C.suffix
        (localInteger 103 256 t) hpref hsuffix'

theorem localInteger_le_of_t_le
    {residue modulus t t' : ℕ} (ht : t ≤ t') :
    localInteger residue modulus t ≤ localInteger residue modulus t' := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_left modulus ht) residue

theorem sourceLocalInteger_le_nextLocalInteger_of_coeffNondecreasing
    {B : AffineTBranch} (hB : B.CoeffNondecreasing)
    (residue modulus u : ℕ) :
    localInteger residue modulus (B.sourceT u)
      ≤ localInteger residue modulus (B.nextT u) :=
  localInteger_le_of_t_le
    (sourceT_le_nextT_of_coeffNondecreasing hB u)

theorem not_nextLocalInteger_lt_sourceLocalInteger_of_coeffNondecreasing
    {B : AffineTBranch} (hB : B.CoeffNondecreasing)
    (residue modulus u : ℕ) :
    ¬ localInteger residue modulus (B.nextT u)
        < localInteger residue modulus (B.sourceT u) :=
  not_lt_of_ge
    (sourceLocalInteger_le_nextLocalInteger_of_coeffNondecreasing
      hB residue modulus u)

end AffineTBranch

/-- A one-parameter affine comparison between a source integer and an endpoint. -/
structure AffineNatDropBranch where
  sourceSlope : ℕ
  sourceIntercept : ℕ
  targetSlope : ℕ
  targetIntercept : ℕ

namespace AffineNatDropBranch

/-- Source integer `N(u) = sourceSlope*u + sourceIntercept`. -/
def sourceN (B : AffineNatDropBranch) (u : ℕ) : ℕ :=
  B.sourceSlope * u + B.sourceIntercept

/-- Endpoint integer `N'(u) = targetSlope*u + targetIntercept`. -/
def targetN (B : AffineNatDropBranch) (u : ℕ) : ℕ :=
  B.targetSlope * u + B.targetIntercept

/--
Coefficientwise affine non-descent.

This is the dual diagnostic to `CoeffDrop`: it records branches whose affine
endpoint is already at least the source endpoint for every local parameter.
-/
def CoeffNondecreasing (B : AffineNatDropBranch) : Prop :=
  B.sourceSlope ≤ B.targetSlope ∧ B.sourceIntercept ≤ B.targetIntercept

theorem sourceN_le_targetN_of_coeffNondecreasing
    {B : AffineNatDropBranch} (hB : B.CoeffNondecreasing) (u : ℕ) :
    B.sourceN u ≤ B.targetN u := by
  exact Nat.add_le_add
    (Nat.mul_le_mul_right u hB.1)
    hB.2

theorem not_targetN_lt_sourceN_of_coeffNondecreasing
    {B : AffineNatDropBranch} (hB : B.CoeffNondecreasing) (u : ℕ) :
    ¬ B.targetN u < B.sourceN u :=
  not_lt_of_ge (sourceN_le_targetN_of_coeffNondecreasing hB u)

/--
Coefficientwise affine drop certificate.

The target slope may tie the source slope, but the intercept must be strictly
smaller.  This is the exact arithmetic shape observed in the current
complete-prefix direct-drop audit.
-/
def CoeffDrop (B : AffineNatDropBranch) : Prop :=
  B.targetSlope ≤ B.sourceSlope ∧ B.targetIntercept < B.sourceIntercept

theorem targetN_lt_sourceN_of_coeffDrop
    {B : AffineNatDropBranch} (hB : B.CoeffDrop) (u : ℕ) :
    B.targetN u < B.sourceN u := by
  exact Nat.add_lt_add_of_le_of_lt
    (Nat.mul_le_mul_right u hB.1)
    hB.2

/--
Affine child produced by an exact one-exponent Syracuse suffix branch.

The local parameter is split as `u = 2*v + r`; the source slope doubles, while
the target slope triples.  Exact divisibility is intentionally not part of
this bare arithmetic object; it is supplied by the branch-specific matching
proofs.
-/
def eOneChild (B : AffineNatDropBranch) (r : ℕ) : AffineNatDropBranch :=
  { sourceSlope := 2 * B.sourceSlope
    sourceIntercept := B.sourceSlope * r + B.sourceIntercept
    targetSlope := 3 * B.targetSlope
    targetIntercept :=
      (3 * B.targetSlope * r + 3 * B.targetIntercept + 1) / 2 }

theorem eOneChild_slope_nondec_of_two_source_le_three_target
    {B : AffineNatDropBranch} {r : ℕ}
    (h : 2 * B.sourceSlope ≤ 3 * B.targetSlope) :
    (B.eOneChild r).sourceSlope ≤ (B.eOneChild r).targetSlope := by
  simpa [eOneChild] using h

theorem eOneChild_slope_growth_of_two_source_lt_three_target
    {B : AffineNatDropBranch} {r : ℕ}
    (h : 2 * B.sourceSlope < 3 * B.targetSlope) :
    (B.eOneChild r).sourceSlope < (B.eOneChild r).targetSlope := by
  simpa [eOneChild] using h

theorem eOneChild_not_coeffDrop_of_slope_growth
    {B : AffineNatDropBranch} {r : ℕ}
    (h : 2 * B.sourceSlope < 3 * B.targetSlope) :
    ¬ (B.eOneChild r).CoeffDrop := by
  intro hdrop
  exact not_le_of_gt
    (eOneChild_slope_growth_of_two_source_lt_three_target (B := B) (r := r) h)
    hdrop.1

end AffineNatDropBranch

/--
An affine integer drop certificate for a matched Syracuse word gives a
step-indexed direct drop.

This is the proof-facing shape for direct-drop rows extracted from finite or
parametric branch audits: the branch must identify the source integer, the
word endpoint, and the coefficientwise affine inequality.
-/
theorem directDropAt_of_word_matches_affineNatDrop
    {B : AffineNatDropBranch} {w : List ℕ} {n u : ℕ}
    (hmatch : SyracuseWordMatchesFrom w n)
    (hlen : 0 < w.length)
    (hsource : B.sourceN u = n)
    (htarget : B.targetN u = evalSyracuseWord w n)
    (hdrop : B.CoeffDrop) :
    DirectDropAt w.length n := by
  refine directDropAt_of_word_matches_eval_lt hmatch hlen ?_
  rw [← htarget, ← hsource]
  exact AffineNatDropBranch.targetN_lt_sourceN_of_coeffDrop hdrop u

/-- A concrete witness gives the propositional strict-descent statement. -/
theorem hasStrictDescent_of_witness {n : ℕ}
    (w : StrictDescentWitness n) : HasStrictDescent n :=
  ⟨w.k, w.positive, w.odd, w.descends⟩

/--
Convert the propositional strict-descent statement into a concrete
witness.  This uses classical choice and is meant only as a packaging
device; constructive proofs should provide `StrictDescentWitness` directly.
-/
noncomputable def strictDescentWitnessOfHasStrictDescent
    {n : ℕ} (h : HasStrictDescent n) : StrictDescentWitness n := by
  classical
  unfold HasStrictDescent at h
  exact
    ⟨Classical.choose h,
      (Classical.choose_spec h).1,
      (Classical.choose_spec h).2.1,
      (Classical.choose_spec h).2.2⟩

theorem hasStrictDescent_iff_nonempty_witness {n : ℕ} :
    HasStrictDescent n ↔ Nonempty (StrictDescentWitness n) := by
  constructor
  · intro h
    exact ⟨strictDescentWitnessOfHasStrictDescent h⟩
  · intro h
    rcases h with ⟨w⟩
    exact hasStrictDescent_of_witness w

/-- Package an explicitly found accelerated strict descent as a witness. -/
def strictDescentWitnessOfIterate
    {n k : ℕ}
    (hpos : 0 < S^[k] n)
    (hodd : Odd (S^[k] n))
    (hdrop : S^[k] n < n) :
    StrictDescentWitness n :=
  ⟨k, hpos, hodd, hdrop⟩

/-- One-step strict descent packaged as a witness. -/
def strictDescentWitnessOfOneStep
    {n : ℕ}
    (hpos : 0 < S n)
    (hodd : Odd (S n))
    (hdrop : S n < n) :
    StrictDescentWitness n :=
  strictDescentWitnessOfIterate
    (k := 1)
    (by simpa using hpos)
    (by simpa using hodd)
    (by simpa using hdrop)

/--
Abstract branch-cover route from the finite phantom-shadowing layer to
strict descent.

The source space `σ` may be infinite, while the branch label space `β` is
finite.  The structure packages exactly the extra theorem still missing
from the current finite diagnostics: every positive odd `n ≠ 1` must map
to a covered source, and every resolved covering branch must provide an
actual strict-descent witness for the accelerated Syracuse orbit of `n`.

This is intentionally conditional.  The existing finite prefix
certificates instantiate only finite summaries; they do not construct
this global branch-cover model.
-/
structure BranchDescentModel (σ β : Type*) [Fintype β] where
  sourceOf : ℕ → σ
  cover : WeakBridge.LabelSplit.BranchCover σ β
  counters : β → WeakBridge.LabelSplit.BranchCounters
  witness :
    ∀ ⦃n : ℕ⦄ ⦃b : β⦄,
      cover.Covers b (sourceOf n) →
      WeakBridge.LabelSplit.branchResolved (counters b) →
      0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n

/--
A resolved global branch-cover model is sufficient for the exact
`UniformStrictDescentHypothesis`.

This theorem is not a proof that such a model exists.  It isolates the
remaining bridge: construct the cover and prove that resolved branches
really give strict Syracuse descent for every positive odd source.
-/
theorem uniformStrictDescent_of_branchDescentModel
    {σ β : Type*} [Fintype β]
    (M : BranchDescentModel σ β)
    (hresolved : WeakBridge.LabelSplit.coverResolved M.cover M.counters) :
    UniformStrictDescentHypothesis := by
  intro n hn hodd hn1
  rcases M.cover.covers (M.sourceOf n) with ⟨b, hb⟩
  have hbResolved : WeakBridge.LabelSplit.branchResolved (M.counters b) :=
    hresolved hb
  let w := M.witness hb hbResolved hn hodd hn1
  exact ⟨w.k, w.positive, w.odd, w.descends⟩

/--
Global descent cover with explicitly declared loss classes.

This is a more audit-friendly version of `BranchDescentModel`.  For each
positive odd `n ≠ 1`, the cover must produce one of three outcomes:

* a direct strict-descent witness;
* a finite branch label whose counters are resolved and whose branch
  semantics give a strict-descent witness;
* a declared loss label whose semantics also give a strict-descent
  witness.

Thus an outside/budget/tail class can appear in this structure only after
it has been converted into an actual strict-descent witness.  Merely
listing a loss class is not enough.
-/
structure GlobalDescentCover (σ β loss : Type*) [Fintype β] [Fintype loss] where
  sourceOf : ℕ → σ
  BranchCovers : β → σ → Prop
  LossCovers : loss → σ → Prop
  branchCounters : β → WeakBridge.LabelSplit.BranchCounters
  branchWitness :
    ∀ ⦃n : ℕ⦄ ⦃b : β⦄,
      BranchCovers b (sourceOf n) →
      WeakBridge.LabelSplit.branchResolved (branchCounters b) →
      0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n
  lossWitness :
    ∀ ⦃n : ℕ⦄ ⦃ell : loss⦄,
      LossCovers ell (sourceOf n) →
      0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n
  cover :
    ∀ n : ℕ, 0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n ⊕
        ({ b : β // BranchCovers b (sourceOf n) } ⊕
          { ell : loss // LossCovers ell (sourceOf n) })

/-- All branch labels of a declared global cover have resolved counters. -/
def GlobalDescentCover.branchesResolved
    {σ β loss : Type*} [Fintype β] [Fintype loss]
    (C : GlobalDescentCover σ β loss) : Prop :=
  ∀ b : β, WeakBridge.LabelSplit.branchResolved (C.branchCounters b)

/--
A resolved global descent cover with declared loss witnesses implies the
uniform strict-descent hypothesis.

This theorem is conditional: it does not construct the cover and it does
not prove that the current finite A0 certificates supply one.
-/
theorem uniformStrictDescent_of_globalDescentCover
    {σ β loss : Type*} [Fintype β] [Fintype loss]
    (C : GlobalDescentCover σ β loss)
    (hresolved : C.branchesResolved) :
    UniformStrictDescentHypothesis := by
  intro n hn hodd hn1
  rcases C.cover n hn hodd hn1 with w | branchOrLoss
  · exact ⟨w.k, w.positive, w.odd, w.descends⟩
  · rcases branchOrLoss with branch | loss
    · rcases branch with ⟨b, hb⟩
      have w := C.branchWitness hb (hresolved b) hn hodd hn1
      exact ⟨w.k, w.positive, w.odd, w.descends⟩
    · rcases loss with ⟨ell, hell⟩
      have w := C.lossWitness hell hn hodd hn1
      exact ⟨w.k, w.positive, w.odd, w.descends⟩

/--
If every positive odd integer different from `1` eventually drops to a
smaller positive odd accelerated iterate, then accelerated Collatz
termination follows by strong induction.

This theorem is fully formalized and contains no computational or
spectral claim.  The open problem is the hypothesis
`UniformStrictDescentHypothesis`.
-/
theorem acceleratedCollatz_of_uniformStrictDescent
    (hdesc : UniformStrictDescentHypothesis) :
    AcceleratedCollatzConjecture := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn hodd
      by_cases h1 : n = 1
      · exact ⟨0, by simp [h1]⟩
      · obtain ⟨k, hpos, hodd', hlt⟩ := hdesc n hn hodd h1
        obtain ⟨l, hl⟩ := ih (S^[k] n) hlt hpos hodd'
        exact ⟨l + k, by
          rw [Function.iterate_add, Function.comp_apply]
          exact hl⟩

/--
Bridge proposition from accelerated termination on positive odd numbers
to classical Collatz termination on all positive natural numbers.

This is separated from the finite-layer problem because it is a standard
arithmetical bridge between the full Collatz map and the accelerated
odd-only Syracuse map, not a spectral or phantom-shadowing claim.
-/
def AcceleratedToClassicalBridge : Prop :=
  AcceleratedCollatzConjecture → ClassicalCollatzConjecture

/--
Elementary bridge from accelerated odd termination to classical Collatz
termination.

The proof expands the initial even tail into repeated halvings, then
expands each accelerated Syracuse step into one odd `3n+1` step followed
by the exact number of halving steps.
-/
theorem acceleratedToClassicalBridge : AcceleratedToClassicalBridge := by
  intro hacc n hn
  let m := natOddPart n
  have hmpos : 0 < m := by
    simpa [m] using natOddPart_pos hn
  have hmodd : Odd m := by
    simpa [m] using natOddPart_odd hn
  obtain ⟨ka, hka⟩ := hacc m hmpos hmodd
  obtain ⟨kc, hkc⟩ :=
    classical_hits_one_of_accelerated_hits_one hmpos hmodd hka
  have hprefix : collatzStep^[nu2Nat n] n = m := by
    simpa [m] using collatzStep_iterate_natOddPart n
  exact ⟨kc + nu2Nat n, by
    rw [Function.iterate_add, Function.comp_apply, hprefix, hkc]⟩

/--
Classical Collatz follows from two explicit hypotheses:

1. the standard bridge from accelerated odd termination to full Collatz
   termination;
2. the global strict-descent hypothesis for accelerated odd orbits.

The first hypothesis should be a later elementary Lean target.  The
second is the real mathematical gap for the finite phantom-shadowing
program.
-/
theorem classicalCollatz_of_uniformStrictDescent
    (hbridge : AcceleratedToClassicalBridge)
    (hdesc : UniformStrictDescentHypothesis) :
    ClassicalCollatzConjecture :=
  hbridge (acceleratedCollatz_of_uniformStrictDescent hdesc)

/--
Classical Collatz follows from the strict-descent hypothesis alone,
because the accelerated-to-classical bridge is now proved.
-/
theorem classicalCollatz_of_uniformStrictDescent_provedBridge
    (hdesc : UniformStrictDescentHypothesis) :
    ClassicalCollatzConjecture :=
  acceleratedToClassicalBridge (acceleratedCollatz_of_uniformStrictDescent hdesc)

/--
A resolved global branch-descent model would imply classical Collatz.

This is still conditional on constructing the global branch-cover model;
it just removes the previously separate elementary accelerated/classical
bookkeeping obligation.
-/
theorem classicalCollatz_of_branchDescentModel
    {σ β : Type*} [Fintype β]
    (M : BranchDescentModel σ β)
    (hresolved : WeakBridge.LabelSplit.coverResolved M.cover M.counters) :
    ClassicalCollatzConjecture :=
  classicalCollatz_of_uniformStrictDescent_provedBridge
    (uniformStrictDescent_of_branchDescentModel M hresolved)

/--
A resolved global descent cover with declared loss witnesses would imply
classical Collatz.

This is the current Lean-level target for the finite/phantom-shadowing
program: construct such a cover, or show exactly which declared loss
class cannot be converted into a strict-descent witness.
-/
theorem classicalCollatz_of_globalDescentCover
    {σ β loss : Type*} [Fintype β] [Fintype loss]
    (C : GlobalDescentCover σ β loss)
    (hresolved : C.branchesResolved) :
    ClassicalCollatzConjecture :=
  classicalCollatz_of_uniformStrictDescent_provedBridge
    (uniformStrictDescent_of_globalDescentCover C hresolved)

/--
Declared unresolved finite-model loss classes for the current global
proof audit.

`drop below start` is not listed here: it is a direct strict-descent
witness, not a loss.  Resolved branch transitions are also not losses;
they are handled by the branch side of `GlobalDescentCover`.
-/
inductive FiniteModelLossKind where
  | outsideSCC
  | budgetExit
  | valuationTail
  | stepTail
  deriving Repr, DecidableEq, Fintype

/--
Coarse classes used when auditing a proposed finite/phantom-shadowing
global cover.
-/
inductive FiniteModelCoverClass where
  | directDrop
  | resolvedBranch
  | outsideSCC
  | budgetExit
  | valuationTail
  | stepTail
  deriving Repr, DecidableEq, Fintype

def FiniteModelLossKind.toCoverClass :
    FiniteModelLossKind → FiniteModelCoverClass
  | .outsideSCC => .outsideSCC
  | .budgetExit => .budgetExit
  | .valuationTail => .valuationTail
  | .stepTail => .stepTail

/--
Current proof status of a cover class.

This is an audit label, not a theorem about the Collatz dynamics:

* `witness`: the class is already a strict-descent witness by definition;
* `branch`: the class is acceptable only after branch semantics and
  resolved counters produce a strict-descent witness;
* `openLoss`: the class is not acceptable in a proof until converted into
  a strict-descent witness or proved absent.
-/
inductive CoverClassStatus where
  | witness
  | branch
  | openLoss
  deriving Repr, DecidableEq, Fintype

def FiniteModelCoverClass.currentStatus :
    FiniteModelCoverClass → CoverClassStatus
  | .directDrop => .witness
  | .resolvedBranch => .branch
  | .outsideSCC => .openLoss
  | .budgetExit => .openLoss
  | .valuationTail => .openLoss
  | .stepTail => .openLoss

theorem finiteModelCoverClass_currentStatus :
    FiniteModelCoverClass.currentStatus .directDrop = .witness
      ∧ FiniteModelCoverClass.currentStatus .resolvedBranch = .branch
      ∧ FiniteModelCoverClass.currentStatus .outsideSCC = .openLoss
      ∧ FiniteModelCoverClass.currentStatus .budgetExit = .openLoss
      ∧ FiniteModelCoverClass.currentStatus .valuationTail = .openLoss
      ∧ FiniteModelCoverClass.currentStatus .stepTail = .openLoss := by
  simp [FiniteModelCoverClass.currentStatus]

/--
The current concrete global-cover target for the finite model: branch
labels are abstract, while loss labels are exactly the declared audit
classes `FiniteModelLossKind`.
-/
abbrev FiniteModelGlobalCover (σ β : Type*) [Fintype β] :=
  GlobalDescentCover σ β FiniteModelLossKind

theorem classicalCollatz_of_finiteModelGlobalCover
    {σ β : Type*} [Fintype β]
    (C : FiniteModelGlobalCover σ β)
    (hresolved : C.branchesResolved) :
    ClassicalCollatzConjecture :=
  classicalCollatz_of_globalDescentCover C hresolved

/--
A small Type-level wrapper around a proposition.

It is used in cover specifications whose cases must be pattern-matched to
construct data, such as `StrictDescentWitness`.
-/
abbrev ProofToken (P : Prop) : Type :=
  { _u : Unit // P }

def proofTokenOf {P : Prop} (h : P) : ProofToken P :=
  ⟨(), h⟩

/--
Soundness condition for a direct-drop predicate on a source space.

This is the proposition one should prove for an actual finite/A0 source
model: whenever the source attached to `n` is marked as a direct drop, the
accelerated orbit of `n` has a strict-descent event.
-/
def DirectDropSound {σ : Type*}
    (sourceOf : ℕ → σ) (DirectDropCovers : σ → Prop) : Prop :=
  ∀ ⦃n : ℕ⦄,
    DirectDropCovers (sourceOf n) →
    0 < n → Odd n → n ≠ 1 →
    HasStrictDescent n

/--
Step-indexed direct-drop soundness.

This is the most concrete shape expected from a finite certificate: for every
integer whose source is marked as a direct drop, exhibit an accelerated
Syracuse step at which the orbit is positive, odd, and below its start.
-/
def DirectDropAtSound {σ : Type*}
    (sourceOf : ℕ → σ) (DirectDropCovers : σ → Prop) : Prop :=
  ∀ ⦃n : ℕ⦄,
    DirectDropCovers (sourceOf n) →
    ∃ k : ℕ, DirectDropAt k n

/--
A step-indexed direct-drop proof is enough for direct-drop soundness.
-/
theorem directDropSound_of_directDropAtSound
    {σ : Type*} {sourceOf : ℕ → σ} {DirectDropCovers : σ → Prop}
    (hsound : DirectDropAtSound sourceOf DirectDropCovers) :
    DirectDropSound sourceOf DirectDropCovers := by
  intro n hdrop _hn _hodd _hn1
  rcases hsound hdrop with ⟨k, hk⟩
  exact hasStrictDescent_of_directDropAt hk

/--
Turn propositional direct-drop soundness into the concrete witness
function required by `FiniteModelCoverSpec`.
-/
noncomputable def directDropWitnessOfSound
    {σ : Type*} {sourceOf : ℕ → σ} {DirectDropCovers : σ → Prop}
    (hsound : DirectDropSound sourceOf DirectDropCovers) :
    ∀ ⦃n : ℕ⦄,
      DirectDropCovers (sourceOf n) →
      0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n := by
  intro n hdrop hn hodd hn1
  exact strictDescentWitnessOfHasStrictDescent
    (hsound hdrop hn hodd hn1)

/--
Soundness condition for a resolved finite branch predicate.

This is intentionally conditional on `branchResolved`: a branch predicate is
not a descent proof merely because the source lies in that branch.  It becomes
usable for the global cover only after the finite counters attached to the
branch are resolved and the branch semantics prove strict descent.
-/
def BranchSound {σ β : Type*} [Fintype β]
    (sourceOf : ℕ → σ)
    (BranchCovers : β → σ → Prop)
    (branchCounters : β → WeakBridge.LabelSplit.BranchCounters) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃b : β⦄,
    BranchCovers b (sourceOf n) →
    WeakBridge.LabelSplit.branchResolved (branchCounters b) →
    0 < n → Odd n → n ≠ 1 →
    HasStrictDescent n

/--
Step-indexed soundness for resolved branch predicates.

This is a convenient target when branch semantics can compute or certify a
specific descent time.
-/
def BranchDropAtSound {σ β : Type*} [Fintype β]
    (sourceOf : ℕ → σ)
    (BranchCovers : β → σ → Prop)
    (branchCounters : β → WeakBridge.LabelSplit.BranchCounters) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃b : β⦄,
    BranchCovers b (sourceOf n) →
    WeakBridge.LabelSplit.branchResolved (branchCounters b) →
    ∃ k : ℕ, DirectDropAt k n

/--
Word-level soundness target for resolved branch predicates.

For each source covered by a resolved branch, the branch supplies a finite
Syracuse exponent word.  The obligation is exactly:

* the actual accelerated orbit follows that word;
* the word is nonempty;
* the word evaluator ends below the starting integer.

This is the intended bridge from affine branch-word arithmetic to
`BranchDropAtSound`.
-/
def BranchWordDropSound {σ β : Type*} [Fintype β]
    (sourceOf : ℕ → σ)
    (BranchCovers : β → σ → Prop)
    (branchCounters : β → WeakBridge.LabelSplit.BranchCounters)
    (branchWord : β → List ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃b : β⦄,
    BranchCovers b (sourceOf n) →
    WeakBridge.LabelSplit.branchResolved (branchCounters b) →
    SyracuseWordMatchesFrom (branchWord b) n
      ∧ 0 < (branchWord b).length
      ∧ evalSyracuseWord (branchWord b) n < n

/--
Transition-chain soundness target for resolved branch predicates.

Unlike `BranchWordDropSound`, this allows a resolved branch to be justified by
a finite chain of returned words.  The endpoint must still be below the
original integer `n`; a rank or transition argument that descends only below
the last intermediate value is not sufficient for the global Collatz bridge.
-/
def BranchTransitionChainDropSound {σ β : Type*} [Fintype β]
    (sourceOf : ℕ → σ)
    (BranchCovers : β → σ → Prop)
    (branchCounters : β → WeakBridge.LabelSplit.BranchCounters)
    (branchWordChain : β → List (List ℕ)) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃b : β⦄,
    BranchCovers b (sourceOf n) →
    WeakBridge.LabelSplit.branchResolved (branchCounters b) →
    SyracuseWordChainMatchesFrom (branchWordChain b) n
      ∧ 0 < syracuseWordChainLength (branchWordChain b)
      ∧ evalSyracuseWordChain (branchWordChain b) n < n

/--
Branch word soundness gives a step-indexed branch-drop proof.
-/
theorem branchDropAtSound_of_branchWordDropSound
    {σ β : Type*} [Fintype β]
    {sourceOf : ℕ → σ}
    {BranchCovers : β → σ → Prop}
    {branchCounters : β → WeakBridge.LabelSplit.BranchCounters}
    {branchWord : β → List ℕ}
    (hsound :
      BranchWordDropSound sourceOf BranchCovers branchCounters branchWord) :
    BranchDropAtSound sourceOf BranchCovers branchCounters := by
  intro n b hbranch hresolved
  rcases hsound hbranch hresolved with ⟨hmatch, hlen, hlt⟩
  exact
    ⟨(branchWord b).length,
      directDropAt_of_word_matches_eval_lt hmatch hlen hlt⟩

/--
Transition-chain soundness gives a step-indexed branch-drop proof.
-/
theorem branchDropAtSound_of_branchTransitionChainDropSound
    {σ β : Type*} [Fintype β]
    {sourceOf : ℕ → σ}
    {BranchCovers : β → σ → Prop}
    {branchCounters : β → WeakBridge.LabelSplit.BranchCounters}
    {branchWordChain : β → List (List ℕ)}
    (hsound :
      BranchTransitionChainDropSound
        sourceOf BranchCovers branchCounters branchWordChain) :
    BranchDropAtSound sourceOf BranchCovers branchCounters := by
  intro n b hbranch hresolved
  rcases hsound hbranch hresolved with ⟨hmatch, hlen, hlt⟩
  exact
    ⟨syracuseWordChainLength (branchWordChain b),
      directDropAt_of_word_chain_matches_eval_lt hmatch hlen hlt⟩

/--
A step-indexed resolved-branch proof is enough for branch soundness.
-/
theorem branchSound_of_branchDropAtSound
    {σ β : Type*} [Fintype β]
    {sourceOf : ℕ → σ}
    {BranchCovers : β → σ → Prop}
    {branchCounters : β → WeakBridge.LabelSplit.BranchCounters}
    (hsound : BranchDropAtSound sourceOf BranchCovers branchCounters) :
    BranchSound sourceOf BranchCovers branchCounters := by
  intro n b hbranch hresolved _hn _hodd _hn1
  rcases hsound hbranch hresolved with ⟨k, hk⟩
  exact hasStrictDescent_of_directDropAt hk

/--
Branch word soundness gives the propositional resolved-branch soundness used
by `FiniteModelSoundSpec`.
-/
theorem branchSound_of_branchWordDropSound
    {σ β : Type*} [Fintype β]
    {sourceOf : ℕ → σ}
    {BranchCovers : β → σ → Prop}
    {branchCounters : β → WeakBridge.LabelSplit.BranchCounters}
    {branchWord : β → List ℕ}
    (hsound :
      BranchWordDropSound sourceOf BranchCovers branchCounters branchWord) :
    BranchSound sourceOf BranchCovers branchCounters :=
  branchSound_of_branchDropAtSound
    (branchDropAtSound_of_branchWordDropSound hsound)

/--
Transition-chain soundness gives the propositional resolved-branch soundness
used by `FiniteModelSoundSpec`.
-/
theorem branchSound_of_branchTransitionChainDropSound
    {σ β : Type*} [Fintype β]
    {sourceOf : ℕ → σ}
    {BranchCovers : β → σ → Prop}
    {branchCounters : β → WeakBridge.LabelSplit.BranchCounters}
    {branchWordChain : β → List (List ℕ)}
    (hsound :
      BranchTransitionChainDropSound
        sourceOf BranchCovers branchCounters branchWordChain) :
    BranchSound sourceOf BranchCovers branchCounters :=
  branchSound_of_branchDropAtSound
    (branchDropAtSound_of_branchTransitionChainDropSound hsound)

/--
Resolved-branch soundness via an A0 semantic-drop table.

This is the branch-level contract for the current A0 program: a resolved
branch is sound if it supplies source-cover data into a fixed
`A0SemanticDropTableSpec`.
-/
abbrev A0SemanticDropBranchCoverSound {σ β : Type*} [Fintype β]
    (sourceOf : ℕ → σ)
    (BranchCovers : β → σ → Prop)
    (branchCounters : β → WeakBridge.LabelSplit.BranchCounters)
    (T : A0SemanticDropTableSpec) :=
  ∀ ⦃n : ℕ⦄ ⦃b : β⦄,
    BranchCovers b (sourceOf n) →
    WeakBridge.LabelSplit.branchResolved (branchCounters b) →
    T.SourceCover n

theorem branchSound_of_a0SemanticDropBranchCoverSound
    {σ β : Type*} [Fintype β]
    {sourceOf : ℕ → σ}
    {BranchCovers : β → σ → Prop}
    {branchCounters : β → WeakBridge.LabelSplit.BranchCounters}
    {T : A0SemanticDropTableSpec}
    (hsound :
      A0SemanticDropBranchCoverSound
        sourceOf BranchCovers branchCounters T) :
    BranchSound sourceOf BranchCovers branchCounters := by
  intro n b hbranch hresolved _hn _hodd _hn1
  exact
    A0SemanticDropTableSpec.hasStrictDescent_of_sourceCover
      T (hsound hbranch hresolved)

/--
Turn propositional resolved-branch soundness into the concrete witness
function required by `FiniteModelCoverSpec`.
-/
noncomputable def branchWitnessOfSound
    {σ β : Type*} [Fintype β]
    {sourceOf : ℕ → σ}
    {BranchCovers : β → σ → Prop}
    {branchCounters : β → WeakBridge.LabelSplit.BranchCounters}
    (hsound : BranchSound sourceOf BranchCovers branchCounters) :
    ∀ ⦃n : ℕ⦄ ⦃b : β⦄,
      BranchCovers b (sourceOf n) →
      WeakBridge.LabelSplit.branchResolved (branchCounters b) →
      0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n := by
  intro n b hbranch hresolved hn hodd hn1
  exact strictDescentWitnessOfHasStrictDescent
    (hsound hbranch hresolved hn hodd hn1)

/--
Soundness condition for declared finite-model loss predicates.

Each loss class is unacceptable as a terminal escape unless it is separately
proved to force a genuine strict-descent witness for the original integer.
-/
def LossSound {σ : Type*}
    (sourceOf : ℕ → σ)
    (LossCovers : FiniteModelLossKind → σ → Prop) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃ell : FiniteModelLossKind⦄,
    LossCovers ell (sourceOf n) →
    0 < n → Odd n → n ≠ 1 →
    HasStrictDescent n

/--
Step-indexed soundness for declared loss predicates.

This applies when a declared loss is not actually a failure but can be
redirected to a concrete accelerated descent time.
-/
def LossDropAtSound {σ : Type*}
    (sourceOf : ℕ → σ)
    (LossCovers : FiniteModelLossKind → σ → Prop) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃ell : FiniteModelLossKind⦄,
    LossCovers ell (sourceOf n) →
    ∃ k : ℕ, DirectDropAt k n

/--
Absence condition for declared loss predicates.

If every declared loss predicate is impossible on the chosen source model,
then the loss soundness obligation is vacuous.
-/
def LossAbsent {σ : Type*}
    (sourceOf : ℕ → σ)
    (LossCovers : FiniteModelLossKind → σ → Prop) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃ell : FiniteModelLossKind⦄,
    LossCovers ell (sourceOf n) → False

/--
A step-indexed loss redirection proof is enough for loss soundness.
-/
theorem lossSound_of_lossDropAtSound
    {σ : Type*}
    {sourceOf : ℕ → σ}
    {LossCovers : FiniteModelLossKind → σ → Prop}
    (hsound : LossDropAtSound sourceOf LossCovers) :
    LossSound sourceOf LossCovers := by
  intro n ell hloss _hn _hodd _hn1
  rcases hsound hloss with ⟨k, hk⟩
  exact hasStrictDescent_of_directDropAt hk

/--
If declared loss predicates are absent, the loss soundness obligation is
vacuously satisfied.
-/
theorem lossSound_of_lossAbsent
    {σ : Type*}
    {sourceOf : ℕ → σ}
    {LossCovers : FiniteModelLossKind → σ → Prop}
    (habsent : LossAbsent sourceOf LossCovers) :
    LossSound sourceOf LossCovers := by
  intro n ell hloss _hn _hodd _hn1
  exact False.elim (habsent hloss)

/--
Turn propositional loss soundness into the concrete witness function required
by `FiniteModelCoverSpec`.
-/
noncomputable def lossWitnessOfSound
    {σ : Type*}
    {sourceOf : ℕ → σ}
    {LossCovers : FiniteModelLossKind → σ → Prop}
    (hsound : LossSound sourceOf LossCovers) :
    ∀ ⦃n : ℕ⦄ ⦃ell : FiniteModelLossKind⦄,
      LossCovers ell (sourceOf n) →
      0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n := by
  intro n ell hloss hn hodd hn1
  exact strictDescentWitnessOfHasStrictDescent
    (hsound hloss hn hodd hn1)

/--
Audit-friendly specification for the current finite-model global cover.

Compared with `FiniteModelGlobalCover`, this separates the direct-drop
predicate, branch predicates, and declared-loss predicates from the concrete
witness functions.  This is the form in which the next proof obligations
should be attacked:

* prove `DirectDropSound`;
* prove `BranchSound` for resolved branch counters;
* prove `LossSound`, or prove that the corresponding loss predicates cannot
  occur in the chosen source model.
-/
structure FiniteModelCoverSpec (σ β : Type*) [Fintype β] where
  sourceOf : ℕ → σ
  DirectDropCovers : σ → Prop
  BranchCovers : β → σ → Prop
  LossCovers : FiniteModelLossKind → σ → Prop
  branchCounters : β → WeakBridge.LabelSplit.BranchCounters
  directDropWitness :
    ∀ ⦃n : ℕ⦄,
      DirectDropCovers (sourceOf n) →
      0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n
  branchWitness :
    ∀ ⦃n : ℕ⦄ ⦃b : β⦄,
      BranchCovers b (sourceOf n) →
      WeakBridge.LabelSplit.branchResolved (branchCounters b) →
      0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n
  lossWitness :
    ∀ ⦃n : ℕ⦄ ⦃ell : FiniteModelLossKind⦄,
      LossCovers ell (sourceOf n) →
      0 < n → Odd n → n ≠ 1 →
      StrictDescentWitness n
  cover :
    ∀ n : ℕ, 0 < n → Odd n → n ≠ 1 →
      ProofToken (DirectDropCovers (sourceOf n)) ⊕
        ({ b : β // BranchCovers b (sourceOf n) } ⊕
          { ell : FiniteModelLossKind // LossCovers ell (sourceOf n) })

def FiniteModelCoverSpec.toGlobalDescentCover
    {σ β : Type*} [Fintype β]
    (S : FiniteModelCoverSpec σ β) :
    FiniteModelGlobalCover σ β :=
  { sourceOf := S.sourceOf,
    BranchCovers := S.BranchCovers,
    LossCovers := S.LossCovers,
    branchCounters := S.branchCounters,
    branchWitness := S.branchWitness,
    lossWitness := S.lossWitness,
    cover := by
      intro n hn hodd hn1
      rcases S.cover n hn hodd hn1 with direct | branchOrLoss
      · exact Sum.inl (S.directDropWitness direct.property hn hodd hn1)
      · exact Sum.inr branchOrLoss }

theorem classicalCollatz_of_finiteModelCoverSpec
    {σ β : Type*} [Fintype β]
    (S : FiniteModelCoverSpec σ β)
    (hresolved : S.toGlobalDescentCover.branchesResolved) :
    ClassicalCollatzConjecture :=
  classicalCollatz_of_finiteModelGlobalCover
    S.toGlobalDescentCover hresolved

/--
Propositional working interface for a finite source model.

This is slightly higher level than `FiniteModelCoverSpec`: direct drops,
resolved branches, and declared losses are justified by propositional
soundness statements.  The witness-producing version is then obtained by
classical packaging through the `...WitnessOfSound` constructors above.
-/
structure FiniteModelSoundSpec (σ β : Type*) [Fintype β] where
  sourceOf : ℕ → σ
  DirectDropCovers : σ → Prop
  BranchCovers : β → σ → Prop
  LossCovers : FiniteModelLossKind → σ → Prop
  branchCounters : β → WeakBridge.LabelSplit.BranchCounters
  directDropSound : DirectDropSound sourceOf DirectDropCovers
  branchSound : BranchSound sourceOf BranchCovers branchCounters
  lossSound : LossSound sourceOf LossCovers
  cover :
    ∀ n : ℕ, 0 < n → Odd n → n ≠ 1 →
      ProofToken (DirectDropCovers (sourceOf n)) ⊕
        ({ b : β // BranchCovers b (sourceOf n) } ⊕
          { ell : FiniteModelLossKind // LossCovers ell (sourceOf n) })

noncomputable def FiniteModelSoundSpec.toCoverSpec
    {σ β : Type*} [Fintype β]
    (S : FiniteModelSoundSpec σ β) :
    FiniteModelCoverSpec σ β :=
  { sourceOf := S.sourceOf,
    DirectDropCovers := S.DirectDropCovers,
    BranchCovers := S.BranchCovers,
    LossCovers := S.LossCovers,
    branchCounters := S.branchCounters,
    directDropWitness := directDropWitnessOfSound S.directDropSound,
    branchWitness := branchWitnessOfSound S.branchSound,
    lossWitness := lossWitnessOfSound S.lossSound,
    cover := S.cover }

theorem classicalCollatz_of_finiteModelSoundSpec
    {σ β : Type*} [Fintype β]
    (S : FiniteModelSoundSpec σ β)
    (hresolved : S.toCoverSpec.toGlobalDescentCover.branchesResolved) :
    ClassicalCollatzConjecture :=
  classicalCollatz_of_finiteModelCoverSpec
    S.toCoverSpec hresolved

end CollatzShadowing
