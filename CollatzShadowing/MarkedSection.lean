/-
AI-assisted development: Codex with Piero Borgatta, 2026-09-24.
Exact six-port arithmetic section for marked odd-to-odd Syracuse episodes.
The arithmetic equivalence is unconditional; recurrence is a separate issue.
-/
import CollatzShadowing.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace CollatzShadowing.MarkedSection

/-- The six arithmetic progressions marking an episode containing `20 mod 27`. -/
def «section» (n : ℕ) : Prop :=
  n % 18 = 13 ∨ n % 72 = 53 ∨ n % 1152 = 853 ∨
  n % 4608 = 3413 ∨ n % 73728 = 54613 ∨ n % 294912 = 218453

/-- A state in the half-open episode `(n,S(n)]` has residue `20 mod 27`.
For positive odd `n`, the displayed quotients are precisely the shortcut
Collatz states in this episode. -/
def episodeHits20 (n : ℕ) : Prop :=
  ∃ j : ℕ, 0 < j ∧ j ≤ syracuseExponent n ∧ (3 * n + 1) / 2 ^ j % 27 = 20

/-- Divisibility is equivalent to the exact valuation threshold. -/
theorem pow_two_dvd_iff (n j : ℕ) :
    2 ^ j ∣ 3 * n + 1 ↔ j ≤ syracuseExponent n := by
  exact padicValNat_dvd_iff_le (by omega : 3 * n + 1 ≠ 0)

/-- The mod-27 power sequence has period 18; this applies at every exponent. -/
theorem pow_two_mod_period (j : ℕ) :
    2 ^ (j + 18) % 27 = 2 ^ j % 27 := by
  rw [pow_add, Nat.mul_mod]
  norm_num

/-- Reduction to the positive representative of an exponent modulo 18. -/
theorem positive_exponent_reduction {j : ℕ} (hj : 0 < j) :
    ∃ k : ℕ, 0 < k ∧ k ≤ 18 ∧ k ≤ j ∧ 2 ^ j % 27 = 2 ^ k % 27 := by
  refine ⟨(j - 1) % 18 + 1, by omega, by omega, ?_, ?_⟩
  · have := Nat.mod_le (j - 1) 18
    omega
  · have hjdecomp : j = (j - 1) % 18 + 1 + 18 * ((j - 1) / 18) := by
      have := Nat.mod_add_div (j - 1) 18
      omega
    conv_lhs => rw [hjdecomp, pow_add, pow_mul, Nat.mul_mod]
    have hpow : (2 ^ 18) ^ ((j - 1) / 18) % 27 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [hpow, Nat.mul_one, Nat.mod_mod]

/-- Multiplying a marked quotient recovers its exact numerator congruence. -/
theorem numerator_congruence {n j : ℕ} (hdiv : 2 ^ j ∣ 3 * n + 1)
    (hmark : (3 * n + 1) / 2 ^ j % 27 = 20) :
    (3 * n + 1) % 27 = (20 * 2 ^ j) % 27 := by
  have h : (3 * n + 1) / 2 ^ j ≡ 20 [MOD 27] := hmark
  have hmul := h.mul_right (2 ^ j)
  change ((3 * n + 1) / 2 ^ j * 2 ^ j) % 27 = (20 * 2 ^ j) % 27 at hmul
  rwa [Nat.div_mul_cancel hdiv] at hmul

/-- Powers of two can be cancelled modulo 27, recovering the quotient residue. -/
theorem quotient_congruence {n k : ℕ} (hdiv : 2 ^ k ∣ 3 * n + 1)
    (hmark : (3 * n + 1) % 27 = (20 * 2 ^ k) % 27) :
    (3 * n + 1) / 2 ^ k % 27 = 20 := by
  have hm : (3 * n + 1) / 2 ^ k * 2 ^ k ≡ 20 * 2 ^ k [MOD 27] := by
    simpa only [Nat.div_mul_cancel hdiv] using hmark
  have hc : Nat.Coprime 27 (2 ^ k) := (by decide : Nat.Coprime 27 2).pow_right k
  exact Nat.ModEq.cancel_right_of_coprime hc hm

/-- The marked quotient gives an exact arithmetic progression, without a CRT search. -/
theorem quotient_mark_crt {d r n : ℕ} (_hd : 0 < d) (hr : r < 9 * d)
    (hscale : 3 * r + 1 = 20 * d) (hdiv : d ∣ 3 * n + 1)
    (hq : ((3 * n + 1) / d) % 27 = 20) : n % (9 * d) = r := by
  let q := ((3 * n + 1) / d) / 27
  have hquot : (3 * n + 1) / d = 20 + 27 * q := by
    have heq := Nat.mod_add_div ((3 * n + 1) / d) 27
    rw [hq] at heq
    simpa [q] using heq.symm
  have hmul := Nat.div_mul_cancel hdiv
  rw [hquot] at hmul
  have hn : n = r + (9 * d) * q := by nlinarith
  rw [hn]
  simpa using Nat.add_mul_mod_self_left r (9 * d) q |>.trans (Nat.mod_eq_of_lt hr)


/-- The finite residue calculation after the justified exponent reduction. -/
theorem reduced_mark_implies_section {n k : ℕ} (hthree : ¬ 3 ∣ n)
    (hk : 0 < k) (hk18 : k ≤ 18) (hdiv : 2 ^ k ∣ 3 * n + 1)
    (hmark : (3 * n + 1) % 27 = (20 * 2 ^ k) % 27) : «section» n := by
  have hthree' : n % 3 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hthree
  have hquot := quotient_congruence hdiv hmark
  unfold «section»
  interval_cases k <;> norm_num only at hdiv hmark hquot
  · exact Or.inl (quotient_mark_crt (d := 2) (by decide) (by decide) (by decide) hdiv hquot)
  · exfalso; omega
  · exact Or.inr (Or.inl
      (quotient_mark_crt (d := 8) (by decide) (by decide) (by decide) hdiv hquot))
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact Or.inr (Or.inr (Or.inl
      (quotient_mark_crt (d := 128) (by decide) (by decide) (by decide) hdiv hquot)))
  · exfalso; omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (quotient_mark_crt (d := 512) (by decide) (by decide) (by decide) hdiv hquot))))
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (quotient_mark_crt (d := 8192) (by decide) (by decide) (by decide) hdiv hquot)))))
  · exfalso; omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (quotient_mark_crt (d := 32768) (by decide) (by decide) (by decide) hdiv hquot)))))
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

/-- Every marked episode begins in the six-port section. -/
theorem section_of_episodeHits20 {n : ℕ} (hthree : ¬ 3 ∣ n)
    (hhit : episodeHits20 n) : «section» n := by
  obtain ⟨j, hj, hjexp, hmark⟩ := hhit
  have hdiv := (pow_two_dvd_iff n j).mpr hjexp
  obtain ⟨k, hk, hk18, hkj, hpow⟩ := positive_exponent_reduction hj
  apply reduced_mark_implies_section hthree hk hk18
  · exact dvd_trans (pow_dvd_pow 2 hkj) hdiv
  · have hnum := numerator_congruence hdiv hmark
    calc
      (3 * n + 1) % 27 = (20 * 2 ^ j) % 27 := hnum
      _ = (20 * 2 ^ k) % 27 :=
        (show 2 ^ j ≡ 2 ^ k [MOD 27] from hpow).mul_left 20

/-- Every section element has a marked state within the valuation threshold. -/
theorem episodeHits20_of_section {n : ℕ} (hn : «section» n) : episodeHits20 n := by
  rcases hn with h | h | h | h | h | h
  · refine ⟨1, by omega, (pow_two_dvd_iff n 1).mp ?_, ?_⟩
    · norm_num [Nat.dvd_iff_mod_eq_zero]; omega
    · norm_num; omega
  · refine ⟨3, by omega, (pow_two_dvd_iff n 3).mp ?_, ?_⟩
    · norm_num [Nat.dvd_iff_mod_eq_zero]; omega
    · norm_num; omega
  · refine ⟨7, by omega, (pow_two_dvd_iff n 7).mp ?_, ?_⟩
    · norm_num [Nat.dvd_iff_mod_eq_zero]; omega
    · norm_num; omega
  · refine ⟨9, by omega, (pow_two_dvd_iff n 9).mp ?_, ?_⟩
    · norm_num [Nat.dvd_iff_mod_eq_zero]; omega
    · norm_num; omega
  · refine ⟨13, by omega, (pow_two_dvd_iff n 13).mp ?_, ?_⟩
    · norm_num [Nat.dvd_iff_mod_eq_zero]; omega
    · norm_num; omega
  · refine ⟨15, by omega, (pow_two_dvd_iff n 15).mp ?_, ?_⟩
    · norm_num [Nat.dvd_iff_mod_eq_zero]; omega
    · norm_num; omega

/-- Exact arithmetic equivalence. No bound on the true Syracuse exponent is assumed. -/
theorem section_iff_episodeHits20 {n : ℕ} (hthree : ¬ 3 ∣ n) :
    «section» n ↔ episodeHits20 n :=
  ⟨episodeHits20_of_section, section_of_episodeHits20 hthree⟩

end CollatzShadowing.MarkedSection
