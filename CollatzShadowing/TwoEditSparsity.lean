/-
Finite arithmetic behind the sparse fixed-shift two-edit relation.

The paper proof in T02_SURGERY_ETA_IT.md uses Evertse's S-unit inequality
(Compositio Math. 53 (1984), Corollary 2, p.228). That analytic theorem and
the asymptotic conclusion are NOT axioms or formal claims in this module.
Here the full ternary residual and the elementary exponent budget are proved.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/

import CollatzShadowing.WordSurgery

namespace CollatzShadowing.TwoEditSparsity

/-- A complete residual identity for a positive interior shift balanced at
the terminal exponent. P is the old sum through the interior position. -/
theorem positive_residual_identity
    (k P B d : ℕ) (u v n y C T : ℤ)
    (hold : 3 ^ k * u + C = 2 ^ (P + B) * n)
    (hnew : 3 ^ k * v + (C + (2 ^ d - 1) * 2 ^ P * T) =
      2 ^ (P + B) * y) :
    3 ^ k * (v - u) =
      2 ^ P * (2 ^ B * (y - n) - (2 ^ d - 1) * T) := by
  rw [pow_add] at hold hnew
  linear_combination hnew - hold

/-- Unlike the terminal necessary condition, the entire depth k divides
this residual, which depends on only the terminal tail. -/
theorem positive_residual_dvd
    (k P B d : ℕ) (u v n y C T : ℤ)
    (hold : 3 ^ k * u + C = 2 ^ (P + B) * n)
    (hnew : 3 ^ k * v + (C + (2 ^ d - 1) * 2 ^ P * T) =
      2 ^ (P + B) * y) :
    (3 : ℤ) ^ k ∣ 2 ^ B * (y - n) - (2 ^ d - 1) * T := by
  have h := positive_residual_identity k P B d u v n y C T hold hnew
  have hc : IsCoprime ((3 : ℤ) ^ k) ((2 : ℤ) ^ P) :=
    (show IsCoprime (3 : ℤ) 2 by norm_num [Int.isCoprime_iff_gcd_eq_one]).pow
  exact hc.dvd_of_dvd_mul_left ⟨v - u, h.symm⟩

/-- In the negative-shift parameterization P is the NEW sum through the
interior position, and B is the OLD sum after that position. -/
theorem negative_residual_identity
    (k P B d : ℕ) (u v n y C T : ℤ)
    (hold : 3 ^ k * u + C = 2 ^ (P + d + B) * n)
    (hnew : 3 ^ k * v + (C - (2 ^ d - 1) * 2 ^ P * T) =
      2 ^ (P + d + B) * y) :
    3 ^ k * (v - u) =
      2 ^ P * (2 ^ (B + d) * (y - n) + (2 ^ d - 1) * T) := by
  simp only [pow_add] at hold hnew ⊢
  linear_combination hnew - hold

theorem negative_residual_dvd
    (k P B d : ℕ) (u v n y C T : ℤ)
    (hold : 3 ^ k * u + C = 2 ^ (P + d + B) * n)
    (hnew : 3 ^ k * v + (C - (2 ^ d - 1) * 2 ^ P * T) =
      2 ^ (P + d + B) * y) :
    (3 : ℤ) ^ k ∣ 2 ^ (B + d) * (y - n) + (2 ^ d - 1) * T := by
  have h := negative_residual_identity k P B d u v n y C T hold hnew
  have hc : IsCoprime ((3 : ℤ) ^ k) ((2 : ℤ) ^ P) :=
    (show IsCoprime (3 : ℤ) 2 by norm_num [Int.isCoprime_iff_gcd_eq_one]).pow
  exact hc.dvd_of_dvd_mul_left ⟨v - u, h.symm⟩

/-- Every exact positive word has this elementary total-exponent budget.
It uses neither finite-orbit sparsity nor a nonreturn hypothesis. -/
theorem exact_word_exponent_budget (w : List ℕ) (u : ℕ) (hu : 0 < u)
    (hm : SyracuseWordMatchesFrom w u) :
    2 ^ w.sum * evalSyracuseWord w u ≤ 4 ^ w.length * u := by
  induction w generalizing u with
  | nil => simp [evalSyracuseWord]
  | cons a rest ih =>
      rcases hm with ⟨ha, hrest⟩
      have hstep : syracuseStepWithExponent a u = S u := by
        simp [syracuseStepWithExponent, S, syracuseNumerator, ha]
      have heq := pow_mul_syracuseStepWithExponent_eq_of_exponent ha
      rw [hstep] at heq
      have hi := ih (S u) (syracuse_pos u) hrest
      calc
        2 ^ (a :: rest).sum * evalSyracuseWord (a :: rest) u =
            2 ^ a * (2 ^ rest.sum * evalSyracuseWord rest (S u)) := by
              simp [evalSyracuseWord, hstep, pow_add, Nat.mul_assoc]
        _ ≤ 2 ^ a * (4 ^ rest.length * S u) := Nat.mul_le_mul_left _ hi
        _ = 4 ^ rest.length * (3 * u + 1) := by rw [← heq]; ring
        _ ≤ 4 ^ rest.length * (4 * u) := Nat.mul_le_mul_left _ (by omega)
        _ = 4 ^ (a :: rest).length * u := by simp [pow_succ]; ring

end CollatzShadowing.TwoEditSparsity
