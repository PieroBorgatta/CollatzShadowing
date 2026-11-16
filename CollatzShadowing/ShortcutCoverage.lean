/-
AI-assisted development: Codex with Piero Borgatta, 2026-09-24.
An explicit stopping rank for the forward-sufficient residue 20 modulo 27.
The target residue is classical (Monks et al., 2013); the rank below is an
independently checked arithmetic certificate, not a Collatz termination rank.
-/
import CollatzShadowing.CollatzBridge
import Mathlib.Tactic

namespace CollatzShadowing.ShortcutCoverage

/-- The shortcut Collatz map, with one halving included in the odd step. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The two stopping conditions covered by the rank. -/
def target (n : ℕ) : Prop := n = 1 ∨ n % 27 = 20

/-- Integer coefficients for the finite residue graph outside 13, 20, 26. -/
def coefficient (r : ℕ) : ℕ :=
  if r = 8 ∨ r = 17 then 4
  else if r = 2 ∨ r = 4 ∨ r = 5 ∨ r = 11 ∨ r = 14 ∨ r = 22 ∨ r = 23 then 7
  else 13

/-- The exceptional self-loop at 26 is measured by its remaining odd steps. -/
def rank (n : ℕ) : ℕ :=
  if n % 27 = 13 then 1
  else if n % 27 = 26 then nu2Nat (n + 1) + 2
  else coefficient (n % 27) * n + 3

theorem T_pos {n : ℕ} (hn : 0 < n) : 0 < T n := by
  unfold T
  split_ifs <;> omega

theorem T_le (n : ℕ) : T n ≤ 2 * n := by
  unfold T
  split_ifs <;> omega

theorem coefficient_ge (r : ℕ) : 4 ≤ coefficient r := by
  unfold coefficient
  split_ifs <;> omega

theorem nu2Nat_le (n : ℕ) : nu2Nat n ≤ n := by
  exact (padicValNat_le_nat_log n).trans (Nat.log_le_self 2 n)

theorem odd_step_valuation {n : ℕ} (hn : n % 2 ≠ 0) :
    nu2Nat (T n + 1) + 1 = nu2Nat (n + 1) := by
  have heq : 2 * (T n + 1) = 3 * (n + 1) := by
    simp only [T, if_neg hn]
    omega
  have hleft : nu2Nat (2 * (T n + 1)) = 1 + nu2Nat (T n + 1) := by
    simp only [nu2Nat, padicValNat.mul (by norm_num : (2 : ℕ) ≠ 0)
      (by omega : T n + 1 ≠ 0)]
    norm_num
  have hright : nu2Nat (3 * (n + 1)) = nu2Nat (n + 1) := by
    simp only [nu2Nat, padicValNat.mul (by norm_num : (3 : ℕ) ≠ 0)
      (by omega : n + 1 ≠ 0)]
    norm_num
  rw [heq, hright] at hleft
  omega

/-- A finite arithmetic certificate for all edges in the remaining graph. -/
theorem core_decrease {n : ℕ} (hn : 1 < n)
    (_h13 : n % 27 ≠ 13) (_h20 : n % 27 ≠ 20) (_h26 : n % 27 ≠ 26)
    (ht13 : T n % 27 ≠ 13) (ht20 : T n % 27 ≠ 20)
    (ht26 : T n % 27 ≠ 26) :
    coefficient (T n % 27) * T n < coefficient (n % 27) * n := by
  unfold T at *
  split_ifs at * <;>
    unfold coefficient <;> split_ifs <;> omega

/-- Every positive state outside the stopping set has a decreasing rank,
unless its next state already belongs to the stopping set. -/
theorem rank_decrease {n : ℕ} (hn : 0 < n) (hstop : ¬ target n)
    (hnext : ¬ target (T n)) : rank (T n) < rank n := by
  have hn1 : 1 < n := by simp only [target, not_or] at hstop; omega
  have hn20 : n % 27 ≠ 20 := fun h => hstop (Or.inr h)
  have ht20 : T n % 27 ≠ 20 := fun h => hnext (Or.inr h)
  by_cases h13 : n % 27 = 13
  · have : T n % 27 = 20 := by unfold T; split_ifs <;> omega
    exact False.elim (ht20 this)
  by_cases h26 : n % 27 = 26
  · by_cases heven : n % 2 = 0
    · have ht13 : T n % 27 = 13 := by simp only [T, if_pos heven]; omega
      simp only [rank, if_neg h13, if_pos h26, if_pos ht13]
      omega
    · have ht26 : T n % 27 = 26 := by simp only [T, if_neg heven]; omega
      have ht13 : T n % 27 ≠ 13 := by omega
      have hv := odd_step_valuation heven
      simp only [rank, if_neg h13, if_pos h26, if_neg ht13, if_pos ht26]
      omega
  by_cases ht13 : T n % 27 = 13
  · simp only [rank, if_pos ht13, if_neg h13, if_neg h26]
    omega
  by_cases ht26 : T n % 27 = 26
  · have hv := nu2Nat_le (T n + 1)
    have hb := T_le n
    have hc := coefficient_ge (n % 27)
    simp only [rank, if_neg ht13, if_pos ht26, if_neg h13, if_neg h26]
    nlinarith
  · have hd := core_decrease hn1 h13 hn20 h26 ht13 ht20 ht26
    simp only [rank, if_neg ht13, if_neg ht26, if_neg h13, if_neg h26]
    omega

/-- Unconditional forward coverage: every positive shortcut orbit hits 1
or the residue 20 modulo 27. This does not assert termination after that hit. -/
theorem exists_iterate_target_bound (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, k ≤ rank n + 1 ∧ target (T^[k] n) := by
  suffices ∀ r n : ℕ, rank n = r → 0 < n →
      ∃ k : ℕ, k ≤ r + 1 ∧ target (T^[k] n) by
    exact this (rank n) n rfl hn
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro n hr hn
      by_cases hstop : target n
      · exact ⟨0, by omega, by simpa using hstop⟩
      by_cases hnext : target (T n)
      · exact ⟨1, by omega, by simpa using hnext⟩
      have hd : rank (T n) < r := by rw [← hr]; exact rank_decrease hn hstop hnext
      obtain ⟨k, hbound, hk⟩ := ih (rank (T n)) hd (T n) rfl (T_pos hn)
      exact ⟨k + 1, by omega, by simpa [Function.iterate_succ_apply] using hk⟩

theorem exists_iterate_target (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, target (T^[k] n) := by
  obtain ⟨k, _, hk⟩ := exists_iterate_target_bound n hn
  exact ⟨k, hk⟩

/-- A coarse linear upper bound on arrival at the sufficient residue or 1. -/
theorem exists_iterate_target_linear_bound (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, k ≤ 13 * n + 4 ∧ target (T^[k] n) := by
  obtain ⟨k, hk, ht⟩ := exists_iterate_target_bound n hn
  have hr : rank n ≤ 13 * n + 3 := by
    have hv := nu2Nat_le (n + 1)
    unfold rank coefficient
    split_ifs <;> omega
  exact ⟨k, by omega, ht⟩

end CollatzShadowing.ShortcutCoverage
