/-
AI-assisted development: Codex with Piero Borgatta, 2026-09-24.
Concrete marked returns and the exact remaining termination obligation.
The hypothesis below is NOT established by section coverage or by the
cancellation-tower formulas. No global decreasing section rank is claimed.
-/
import CollatzShadowing.SectionCoverage
import CollatzShadowing.CancellationTower

namespace CollatzShadowing.SectionReturn

open MarkedSection

theorem section_pos {n : ℕ} (hn : «section» n) : 0 < n := by
  unfold MarkedSection.«section» at hn
  omega

theorem section_odd {n : ℕ} (hn : «section» n) : Odd n := by
  apply Nat.odd_iff.mpr
  unfold MarkedSection.«section» at hn
  omega

/-- Every orbit that never reaches 1 visits the section at arbitrarily
late accelerated times. This applies to both divergent and periodic orbits. -/
theorem recurrent_section_of_never_hits_one (n : ℕ)
    (hnever : ∀ k : ℕ, S^[k] n ≠ 1) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ «section» (S^[k] n) := by
  obtain ⟨j, hj⟩ := SectionCoverage.exists_accelerated_hit (S^[N + 1] n)
    (syracuse_iterate_succ_pos N n) (syracuse_iterate_succ_odd N n)
  rcases hj with h1 | hmark
  · exact False.elim (hnever (j + (N + 1))
      (by simpa [Function.iterate_add_apply] using h1))
  · exact ⟨j + (N + 1), by omega,
      by simpa [Function.iterate_add_apply] using hmark⟩

/-- An infinite family of genuine one-step descending returns to port one. -/
theorem descending_return_family (t : ℕ) :
    «section» (661 + 1152 * t) ∧
    syracuseExponent (661 + 1152 * t) = 6 ∧
    S (661 + 1152 * t) = 31 + 54 * t ∧
    «section» (31 + 54 * t) ∧
    31 + 54 * t < 661 + 1152 * t := by
  have hnum : syracuseNumerator (661 + 1152 * t) = 2 ^ 6 * (31 + 54 * t) := by
    unfold syracuseNumerator
    ring
  have hodd : Odd (31 + 54 * t) := ⟨15 + 27 * t, by omega⟩
  obtain ⟨ha, hs⟩ := syracuseStep_of_num_eq_two_pow_mul_odd hnum hodd
  refine ⟨?_, ha, hs, ?_, by omega⟩
  · unfold MarkedSection.«section»
    exact Or.inl (by omega)
  · unfold MarkedSection.«section»
    exact Or.inl (by omega)

/-- The first marked return can increase the integer: 31 returns to 121
after the intermediate values 47, 71, 107, 161. -/
theorem first_return_can_increase :
    «section» 31 ∧ S^[5] 31 = 121 ∧ «section» 121 ∧
    31 < 121 ∧ ∀ j : ℕ, 0 < j → j < 5 → ¬ «section» (S^[j] 31) := by
  have h31 : S 31 = 47 := (syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 31) (a := 1) (m := 47) (by norm_num [syracuseNumerator]) (by decide)).2
  have h47 : S 47 = 71 := (syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 47) (a := 1) (m := 71) (by norm_num [syracuseNumerator]) (by decide)).2
  have h71 : S 71 = 107 := (syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 71) (a := 1) (m := 107) (by norm_num [syracuseNumerator]) (by decide)).2
  have h107 : S 107 = 161 := (syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 107) (a := 1) (m := 161) (by norm_num [syracuseNumerator]) (by decide)).2
  have h161 : S 161 = 121 := (syracuseStep_of_num_eq_two_pow_mul_odd
    (n := 161) (a := 2) (m := 121) (by norm_num [syracuseNumerator]) (by decide)).2
  refine ⟨by norm_num [MarkedSection.«section»], ?_,
    by norm_num [MarkedSection.«section»], by norm_num, ?_⟩
  · norm_num [Function.iterate_succ_apply', h31, h47, h71, h107, h161]
  · intro j hj hj5
    interval_cases j <;>
      norm_num [Function.iterate_succ_apply', h31, h47, h71, h107,
        MarkedSection.«section»]

/-- No fixed accelerated time horizon guarantees descent even on the marked
section. This is an explicit infinite family, not a bounded computation. -/
theorem marked_sources_noDrop_for_any_horizon (B : ℕ) :
    «section» (cancellationTowerSource (18 * (B + 2) + 10)) ∧
    ∀ j ≤ B, cancellationTowerSource (18 * (B + 2) + 10) ≤
      S^[j] (cancellationTowerSource (18 * (B + 2) + 10)) := by
  constructor
  · exact Or.inl (cancellationTowerSource_mod_eighteen (B + 2))
  · have h := cancellationTower_noDrop_of_even_ge_thirty
      (k := 18 * (B + 2) + 10) (by omega) ⟨9 * (B + 2) + 5, by omega⟩
    intro j hj
    apply h j
    dsimp [cancellationTowerMacroLength]
    have hd := Nat.mod_add_div (18 * (B + 2) + 10 - 1) 3
    have hm := Nat.mod_lt (18 * (B + 2) + 10 - 1) (by norm_num : 0 < 3)
    split_ifs <;> omega

/-- A candidate rank must decrease at some actual later marked visit,
or the orbit must reach 1. Coverage alone does not supply this property. -/
def RankDescent (R : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, «section» n →
    acceleratedOrbitHitsOne n ∨
      ∃ k : ℕ, 0 < k ∧ «section» (S^[k] n) ∧ R (S^[k] n) < R n

theorem section_hits_one_of_rankDescent {R : ℕ → ℕ} (hR : RankDescent R)
    (n : ℕ) (hn : «section» n) : acceleratedOrbitHitsOne n := by
  suffices ∀ r n : ℕ, R n = r → «section» n → acceleratedOrbitHitsOne n by
    exact this (R n) n rfl hn
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro n hr hn
      rcases hR n hn with h1 | ⟨k, _hkpos, hmark, hlt⟩
      · exact h1
      · obtain ⟨j, hj⟩ := ih (R (S^[k] n)) (by omega) (S^[k] n) rfl hmark
        exact ⟨j + k, by simpa [Function.iterate_add_apply] using hj⟩

/-- The six-port return-rank problem suffices for accelerated Collatz.
The rank-descent argument remains an explicit open hypothesis. -/
theorem acceleratedCollatz_of_rankDescent {R : ℕ → ℕ} (hR : RankDescent R) :
    AcceleratedCollatzConjecture := by
  intro n hn hodd
  obtain ⟨k, hk⟩ := SectionCoverage.exists_accelerated_hit n hn hodd
  rcases hk with h1 | hmark
  · exact ⟨k, h1⟩
  · obtain ⟨j, hj⟩ := section_hits_one_of_rankDescent hR (S^[k] n) hmark
    exact ⟨j + k, by simpa [Function.iterate_add_apply] using hj⟩

theorem classicalCollatz_of_rankDescent {R : ℕ → ℕ} (hR : RankDescent R) :
    ClassicalCollatzConjecture :=
  acceleratedToClassicalBridge (acceleratedCollatz_of_rankDescent hR)

/-- The open rank interface reorganizes the global obligation; existentially
it is equivalent to accelerated Collatz, not a weaker theorem already proved. -/
theorem exists_rankDescent_iff_acceleratedCollatz :
    (∃ R : ℕ → ℕ, RankDescent R) ↔ AcceleratedCollatzConjecture := by
  constructor
  · rintro ⟨R, hR⟩
    exact acceleratedCollatz_of_rankDescent hR
  · intro h
    refine ⟨fun _ => 0, ?_⟩
    intro n hn
    exact Or.inl (h n (section_pos hn) (section_odd hn))

end CollatzShadowing.SectionReturn
