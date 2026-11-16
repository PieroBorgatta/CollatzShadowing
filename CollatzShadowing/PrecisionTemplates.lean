/-
Concrete precision-tax templates for the three shortest expansive Syracuse
words.  These are small reusable instances of `PrecisionTax`: their phantom
numerators are respectively `n + 1`, `n + 5`, and `n + 7`, and a matched
application consumes exactly the sum of the prescribed exponents.
-/

import CollatzShadowing.PrecisionTax

namespace CollatzShadowing

/-! ## The word `[1]` -/

@[simp] theorem syracuseWordConst_one :
    syracuseWordConst [1] = 1 := by
  norm_num [syracuseWordConst]

@[simp] theorem syracuseWordExpansionDefect_one :
    syracuseWordExpansionDefect [1] = 1 := by
  norm_num [syracuseWordExpansionDefect]

@[simp] theorem syracuseWordPhantomPrecisionNumerator_one (n : ℕ) :
    syracuseWordPhantomPrecisionNumerator [1] n = n + 1 := by
  simp [syracuseWordPhantomPrecisionNumerator]

@[simp] theorem syracuseWordMatchesFrom_one_iff (n : ℕ) :
    SyracuseWordMatchesFrom [1] n ↔ syracuseExponent n = 1 := by
  simp [SyracuseWordMatchesFrom]

theorem syracuseWordPhantomPrecision_one_after_eval_add_one
    {n : ℕ} (hmatch : SyracuseWordMatchesFrom [1] n) :
    syracuseWordPhantomPrecision [1] (evalSyracuseWord [1] n) + 1
      = syracuseWordPhantomPrecision [1] n := by
  exact syracuseWordPhantomPrecision_after_eval_add_sum
    (w := [1]) (n := n) (by norm_num) hmatch

theorem syracuseWord_one_matched_block_budget
    {n k : ℕ}
    (hmatch :
      ∀ i < k,
        SyracuseWordMatchesFrom [1]
          ((evalSyracuseWord [1])^[i] n)) :
    k ≤ nu2Nat (n + 1) := by
  simpa [syracuseWordPhantomPrecision] using
    (syracuseWord_matched_block_precision_budget
      (w := [1]) (n := n) (k := k) (by norm_num) hmatch)

theorem no_infinite_matched_syracuseWord_one (n : ℕ) :
    ¬ ∀ i : ℕ,
      SyracuseWordMatchesFrom [1]
        ((evalSyracuseWord [1])^[i] n) := by
  exact no_infinite_matched_expansive_word
    (w := [1]) (n := n) (by norm_num) (by norm_num)

/-! ## The word `[1, 2]` -/

@[simp] theorem syracuseWordConst_one_two :
    syracuseWordConst [1, 2] = 5 := by
  norm_num [syracuseWordConst]

@[simp] theorem syracuseWordExpansionDefect_one_two :
    syracuseWordExpansionDefect [1, 2] = 1 := by
  norm_num [syracuseWordExpansionDefect]

@[simp] theorem syracuseWordPhantomPrecisionNumerator_one_two (n : ℕ) :
    syracuseWordPhantomPrecisionNumerator [1, 2] n = n + 5 := by
  simp [syracuseWordPhantomPrecisionNumerator]

@[simp] theorem syracuseWordMatchesFrom_one_two_iff (n : ℕ) :
    SyracuseWordMatchesFrom [1, 2] n ↔
      syracuseExponent n = 1 ∧ syracuseExponent (S n) = 2 := by
  simp [SyracuseWordMatchesFrom]

theorem syracuseWordPhantomPrecision_one_two_after_eval_add_three
    {n : ℕ} (hmatch : SyracuseWordMatchesFrom [1, 2] n) :
    syracuseWordPhantomPrecision [1, 2] (evalSyracuseWord [1, 2] n) + 3
      = syracuseWordPhantomPrecision [1, 2] n := by
  exact syracuseWordPhantomPrecision_after_eval_add_sum
    (w := [1, 2]) (n := n) (by norm_num) hmatch

theorem syracuseWord_one_two_matched_block_budget
    {n k : ℕ}
    (hmatch :
      ∀ i < k,
        SyracuseWordMatchesFrom [1, 2]
          ((evalSyracuseWord [1, 2])^[i] n)) :
    3 * k ≤ nu2Nat (n + 5) := by
  simpa [syracuseWordPhantomPrecision, Nat.mul_comm] using
    (syracuseWord_matched_block_precision_budget
      (w := [1, 2]) (n := n) (k := k) (by norm_num) hmatch)

theorem no_infinite_matched_syracuseWord_one_two (n : ℕ) :
    ¬ ∀ i : ℕ,
      SyracuseWordMatchesFrom [1, 2]
        ((evalSyracuseWord [1, 2])^[i] n) := by
  exact no_infinite_matched_expansive_word
    (w := [1, 2]) (n := n) (by norm_num) (by norm_num)

/-! ## The word `[2, 1]` -/

@[simp] theorem syracuseWordConst_two_one :
    syracuseWordConst [2, 1] = 7 := by
  norm_num [syracuseWordConst]

@[simp] theorem syracuseWordExpansionDefect_two_one :
    syracuseWordExpansionDefect [2, 1] = 1 := by
  norm_num [syracuseWordExpansionDefect]

@[simp] theorem syracuseWordPhantomPrecisionNumerator_two_one (n : ℕ) :
    syracuseWordPhantomPrecisionNumerator [2, 1] n = n + 7 := by
  simp [syracuseWordPhantomPrecisionNumerator]

@[simp] theorem syracuseWordMatchesFrom_two_one_iff (n : ℕ) :
    SyracuseWordMatchesFrom [2, 1] n ↔
      syracuseExponent n = 2 ∧ syracuseExponent (S n) = 1 := by
  simp [SyracuseWordMatchesFrom]

theorem syracuseWordPhantomPrecision_two_one_after_eval_add_three
    {n : ℕ} (hmatch : SyracuseWordMatchesFrom [2, 1] n) :
    syracuseWordPhantomPrecision [2, 1] (evalSyracuseWord [2, 1] n) + 3
      = syracuseWordPhantomPrecision [2, 1] n := by
  exact syracuseWordPhantomPrecision_after_eval_add_sum
    (w := [2, 1]) (n := n) (by norm_num) hmatch

theorem syracuseWord_two_one_matched_block_budget
    {n k : ℕ}
    (hmatch :
      ∀ i < k,
        SyracuseWordMatchesFrom [2, 1]
          ((evalSyracuseWord [2, 1])^[i] n)) :
    3 * k ≤ nu2Nat (n + 7) := by
  simpa [syracuseWordPhantomPrecision, Nat.mul_comm] using
    (syracuseWord_matched_block_precision_budget
      (w := [2, 1]) (n := n) (k := k) (by norm_num) hmatch)

theorem no_infinite_matched_syracuseWord_two_one (n : ℕ) :
    ¬ ∀ i : ℕ,
      SyracuseWordMatchesFrom [2, 1]
        ((evalSyracuseWord [2, 1])^[i] n) := by
  exact no_infinite_matched_expansive_word
    (w := [2, 1]) (n := n) (by norm_num) (by norm_num)

end CollatzShadowing
