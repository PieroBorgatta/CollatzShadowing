/-
AI-assisted development: Codex with Piero Borgatta, 2026-09-24.
The marked arithmetic section is reached by every positive odd Syracuse
orbit unless that orbit first reaches 1. Coverage follows from the explicit
shortcut stopping certificate and exact decomposition into odd episodes.
This file does not prove descent or termination after reaching the section.
-/
import CollatzShadowing.MarkedSection
import CollatzShadowing.ShortcutCoverage

namespace CollatzShadowing.SectionCoverage

open ShortcutCoverage

private theorem exponent_pos_of_odd {n : ℕ} (hn : Odd n) :
    0 < syracuseExponent n := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hd : 2 ^ 1 ∣ 3 * n + 1 := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨3 * k + 2, ?_⟩
    omega
  have hle := (MarkedSection.pow_two_dvd_iff n 1).mp hd
  omega

private theorem T_iterate_halvings (m k : ℕ) (hd : 2 ^ k ∣ m) :
    T^[k] m = m / 2 ^ k := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      have hd2 : 2 ∣ m := (dvd_pow_self 2 (by omega : k + 1 ≠ 0)).trans hd
      have hm : m % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd2
      have htail : 2 ^ k ∣ m / 2 := by
        rw [Nat.dvd_div_iff_mul_dvd hd2]
        simpa [pow_succ, Nat.mul_comm] using hd
      rw [Function.iterate_succ_apply, T, if_pos hm, ih (m / 2) htail,
        Nat.div_div_eq_div_mul, pow_succ']

/-- Every internal shortcut state in an odd Syracuse episode is its exact
power-of-two quotient. -/
theorem shortcut_episode {n j : ℕ} (hn : Odd n) (hj : 0 < j)
    (hle : j ≤ syracuseExponent n) :
    T^[j] n = (3 * n + 1) / 2 ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hd := (MarkedSection.pow_two_dvd_iff n (k + 1)).mpr hle
  have hd2 : 2 ∣ 3 * n + 1 :=
    (dvd_pow_self 2 (by omega : k + 1 ≠ 0)).trans hd
  have htail : 2 ^ k ∣ (3 * n + 1) / 2 := by
    rw [Nat.dvd_div_iff_mul_dvd hd2]
    simpa [pow_succ, Nat.mul_comm] using hd
  have hnmod : n % 2 ≠ 0 := by
    have ho := Nat.odd_iff.mp hn
    omega
  rw [Function.iterate_succ_apply, T, if_neg hnmod,
    T_iterate_halvings _ _ htail, Nat.div_div_eq_div_mul, pow_succ']

/-- The complete shortcut episode ends at the accelerated Syracuse value. -/
theorem shortcut_episode_endpoint {n : ℕ} (hn : Odd n) :
    T^[syracuseExponent n] n = S n := by
  simpa [S, syracuseNumerator] using
    shortcut_episode hn (exponent_pos_of_odd hn) (le_refl (syracuseExponent n))

/-- A positive Syracuse output is never divisible by three. -/
theorem syracuse_not_three_dvd (n : ℕ) : ¬ 3 ∣ S n := by
  have hnum := pow_mul_syracuseStepWithExponent_eq_of_exponent
    (n := n) (a := syracuseExponent n) rfl
  have hstep : syracuseStepWithExponent (syracuseExponent n) n = S n := by
    simp [syracuseStepWithExponent, S, syracuseNumerator]
  rw [hstep] at hnum
  intro hd
  have hdnum : 3 ∣ 3 * n + 1 := by
    rw [← hnum]
    exact dvd_mul_of_dvd_right hd _
  have hm := Nat.dvd_iff_mod_eq_zero.mp hdnum
  omega

private theorem target_in_episode {n j : ℕ} (hn : Odd n)
    (hthree : ¬ 3 ∣ n) (hj : 0 < j) (hle : j ≤ syracuseExponent n)
    (ht : target (T^[j] n)) :
    (S n = 1) ∨ MarkedSection.«section» n := by
  rw [shortcut_episode hn hj hle] at ht
  rcases ht with h1 | h20
  · left
    have hd := (MarkedSection.pow_two_dvd_iff n j).mpr hle
    have haff : syracuseNumerator n = 2 ^ j * 1 := by
      have heq := Nat.mul_div_cancel' hd
      rw [h1] at heq
      simpa [syracuseNumerator] using heq.symm
    exact (syracuseStep_of_num_eq_two_pow_mul_odd haff (by decide : Odd 1)).2
  · right
    exact MarkedSection.section_of_episodeHits20 hthree ⟨j, hj, hle, h20⟩

/-- A positive-time shortcut hit pulls back to an accelerated hit of 1 or
a marked episode. The time bound is used only for a finite induction. -/
theorem accelerated_hit_of_shortcut_hit (t : ℕ) :
    ∀ n : ℕ, Odd n → (¬ 3 ∣ n) → 0 < t →
      target (T^[t] n) →
      ∃ k : ℕ, S^[k] n = 1 ∨ MarkedSection.«section» (S^[k] n) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro n hn hthree htpos htarget
      by_cases hle : t ≤ syracuseExponent n
      · rcases target_in_episode hn hthree htpos hle htarget with h1 | hmark
        · exact ⟨1, Or.inl (by simpa using h1)⟩
        · exact ⟨0, Or.inr (by simpa using hmark)⟩
      · have hapos := exponent_pos_of_odd hn
        have htrem : 0 < t - syracuseExponent n := by omega
        have hsmall : t - syracuseExponent n < t := by omega
        have hdecomp : t = (t - syracuseExponent n) + syracuseExponent n := by omega
        have htarget' : target (T^[t - syracuseExponent n] (S n)) := by
          rw [hdecomp, Function.iterate_add_apply, shortcut_episode_endpoint hn] at htarget
          exact htarget
        obtain ⟨k, hk⟩ := ih (t - syracuseExponent n) hsmall (S n)
          (syracuse_odd n) (syracuse_not_three_dvd n) htrem htarget'
        exact ⟨k + 1, by simpa [Function.iterate_succ_apply] using hk⟩

/-- Every positive odd Syracuse orbit reaches 1 or the marked six-port
section. No return/descent property of the section is assumed. -/
theorem exists_accelerated_hit (n : ℕ) (_hn : 0 < n) (_hodd : Odd n) :
    ∃ k : ℕ, S^[k] n = 1 ∨ MarkedSection.«section» (S^[k] n) := by
  have hpos := T_pos (syracuse_pos n)
  obtain ⟨t, ht⟩ := exists_iterate_target (T (S n)) hpos
  have ht' : target (T^[t + 1] (S n)) := by
    simpa [Function.iterate_succ_apply] using ht
  obtain ⟨k, hk⟩ := accelerated_hit_of_shortcut_hit (t + 1) (S n)
    (syracuse_odd n) (syracuse_not_three_dvd n) (by omega) ht'
  exact ⟨k + 1, by simpa [Function.iterate_succ_apply] using hk⟩

end CollatzShadowing.SectionCoverage
