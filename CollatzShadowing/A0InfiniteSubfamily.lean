/-
Two exact infinite leaves of the A0 source cylinder.

The common A0 prefix sends

  103 + 256 * t  ↦  593 + 1458 * t.

No finite search is used below.  The residue `t = 2 (mod 16)` forces at
least five powers of two in the very next Syracuse numerator, which is
already enough for a strict drop below the original source.
-/

import CollatzShadowing.CollatzBridge

namespace CollatzShadowing

/--
On the infinite A0 residue class `t = 2 + 16*u`, the first exponent after
the common six-step prefix is at least five.
-/
theorem five_le_syracuseExponent_a0_t_two_mod_sixteen (u : ℕ) :
    5 ≤ syracuseExponent (593 + 1458 * (2 + 16 * u)) := by
  have hnum :
      syracuseNumerator (593 + 1458 * (2 + 16 * u))
        = 2 ^ 5 * (329 + 2187 * u) := by
    unfold syracuseNumerator
    norm_num
    ring
  have hne : 329 + 2187 * u ≠ 0 := by omega
  rw [syracuseExponent, nu2Nat, hnum]
  rw [padicValNat_base_pow_mul
    (p := 2) (n := 329 + 2187 * u)
    (by norm_num : 1 < 2) hne 5]
  omega

/--
Every source

  `n = 103 + 256*(2 + 16*u) = 615 + 4096*u`

has a direct accelerated drop after the six-step A0 common prefix and one
additional step.
-/
theorem directDropAt_seven_a0_t_two_mod_sixteen (u : ℕ) :
    DirectDropAt 7 (103 + 256 * (2 + 16 * u)) := by
  let t : ℕ := 2 + 16 * u
  let n : ℕ := 103 + 256 * t
  let x : ℕ := 593 + 1458 * t
  let e : ℕ := syracuseExponent x
  have hpref :
      SyracuseWordMatchesFrom a0SemanticDropCommonPrefix n := by
    simpa [t, n] using
      a0SemanticDropCommonPrefix_matches_source_cylinder t
  have hprefEval :
      evalSyracuseWord a0SemanticDropCommonPrefix n = x := by
    simpa [t, n, x] using
      eval_a0SemanticDropCommonPrefix_source_cylinder t
  have hsuff : SyracuseWordMatchesFrom [e] x := by
    simp [SyracuseWordMatchesFrom, e]
  have hmatch :
      SyracuseWordMatchesFrom
        (a0SemanticDropCommonPrefix ++ [e]) n :=
    SyracuseWordMatchesFrom_append_of_matches
      a0SemanticDropCommonPrefix [e] n hpref
      (by simpa [hprefEval] using hsuff)
  have he : 5 ≤ e := by
    simpa [t, x, e] using
      five_le_syracuseExponent_a0_t_two_mod_sixteen u
  have hpow : 32 ≤ 2 ^ e := by
    calc
      32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ e :=
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) he
  have hnum :
      3 * x + 1 = 32 * (329 + 2187 * u) := by
    simp [t, x]
    ring
  have hsource :
      329 + 2187 * u < n := by
    simp [t, n]
    omega
  have hcontract : 3 * x + 1 < 2 ^ e * n := by
    calc
      3 * x + 1 = 32 * (329 + 2187 * u) := hnum
      _ < 32 * n :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < (32 : ℕ))).mpr hsource
      _ ≤ 2 ^ e * n := Nat.mul_le_mul_right n hpow
  have hdrop :
      DirectDropAt
        (a0SemanticDropCommonPrefix ++ [e]).length n := by
    apply directDropAt_of_suffix_after_prefix_affine_contracting
      (pref := a0SemanticDropCommonPrefix) (suff := [e])
      hmatch
    · simp
    · simpa [hprefEval, syracuseWordConst] using hcontract
  simpa [a0SemanticDropCommonPrefix, n] using hdrop

/-- Strict-descent form of the same infinite A0 residue leaf. -/
theorem hasStrictDescent_a0_t_two_mod_sixteen (u : ℕ) :
    HasStrictDescent (615 + 4096 * u) := by
  have hdrop := directDropAt_seven_a0_t_two_mod_sixteen u
  have hn :
      103 + 256 * (2 + 16 * u) = 615 + 4096 * u := by
    ring
  rw [hn] at hdrop
  exact hasStrictDescent_of_directDropAt hdrop

/--
On `t = 10 + 32*u`, the first post-prefix step has exponent exactly four
and endpoint `2845 + 8748*u`.
-/
theorem syracuseStep_a0_t_ten_mod_thirtytwo (u : ℕ) :
    syracuseExponent (593 + 1458 * (10 + 32 * u)) = 4
      ∧ S (593 + 1458 * (10 + 32 * u)) = 2845 + 8748 * u := by
  apply syracuseStep_of_num_eq_two_pow_mul_odd
  · unfold syracuseNumerator
    norm_num
    ring
  · exact ⟨1422 + 4374 * u, by ring⟩

/--
The next exponent after the exact exponent-four step on
`t = 10 + 32*u` is at least two.
-/
theorem two_le_syracuseExponent_after_a0_t_ten_mod_thirtytwo (u : ℕ) :
    2 ≤ syracuseExponent (2845 + 8748 * u) := by
  have hnum :
      syracuseNumerator (2845 + 8748 * u)
        = 2 ^ 2 * (2134 + 6561 * u) := by
    unfold syracuseNumerator
    norm_num
    ring
  have hne : 2134 + 6561 * u ≠ 0 := by omega
  rw [syracuseExponent, nu2Nat, hnum]
  rw [padicValNat_base_pow_mul
    (p := 2) (n := 2134 + 6561 * u)
    (by norm_num : 1 < 2) hne 2]
  omega

/--
Every source

  `n = 103 + 256*(10 + 32*u) = 2663 + 8192*u`

has a direct accelerated drop after the common prefix and the two-step
suffix `[4, e]`, where the second exponent satisfies `e ≥ 2`.
-/
theorem directDropAt_eight_a0_t_ten_mod_thirtytwo (u : ℕ) :
    DirectDropAt 8 (103 + 256 * (10 + 32 * u)) := by
  let t : ℕ := 10 + 32 * u
  let n : ℕ := 103 + 256 * t
  let x : ℕ := 593 + 1458 * t
  let y : ℕ := 2845 + 8748 * u
  let e : ℕ := syracuseExponent y
  have hpref :
      SyracuseWordMatchesFrom a0SemanticDropCommonPrefix n := by
    simpa [t, n] using
      a0SemanticDropCommonPrefix_matches_source_cylinder t
  have hprefEval :
      evalSyracuseWord a0SemanticDropCommonPrefix n = x := by
    simpa [t, n, x] using
      eval_a0SemanticDropCommonPrefix_source_cylinder t
  have hfirst :
      syracuseExponent x = 4 ∧ S x = y := by
    simpa [t, x, y] using syracuseStep_a0_t_ten_mod_thirtytwo u
  have htail : SyracuseWordMatchesFrom [e] y := by
    simp [SyracuseWordMatchesFrom, e]
  have hsuff : SyracuseWordMatchesFrom [4, e] x := by
    unfold SyracuseWordMatchesFrom
    refine ⟨hfirst.1, ?_⟩
    rw [hfirst.2]
    exact htail
  have hmatch :
      SyracuseWordMatchesFrom
        (a0SemanticDropCommonPrefix ++ [4, e]) n :=
    SyracuseWordMatchesFrom_append_of_matches
      a0SemanticDropCommonPrefix [4, e] n hpref
      (by simpa [hprefEval] using hsuff)
  have he : 2 ≤ e := by
    simpa [y, e] using
      two_le_syracuseExponent_after_a0_t_ten_mod_thirtytwo u
  have hpow : 64 ≤ 2 ^ (4 + e) := by
    calc
      64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (4 + e) :=
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
  have hnum :
      9 * x + 19 = 64 * (2134 + 6561 * u) := by
    simp [t, x]
    ring
  have hsource :
      2134 + 6561 * u < n := by
    simp [t, n]
    omega
  have hcontract : 9 * x + 19 < 2 ^ (4 + e) * n := by
    calc
      9 * x + 19 = 64 * (2134 + 6561 * u) := hnum
      _ < 64 * n :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < (64 : ℕ))).mpr hsource
      _ ≤ 2 ^ (4 + e) * n := Nat.mul_le_mul_right n hpow
  have hdrop :
      DirectDropAt
        (a0SemanticDropCommonPrefix ++ [4, e]).length n := by
    apply directDropAt_of_suffix_after_prefix_affine_contracting
      (pref := a0SemanticDropCommonPrefix) (suff := [4, e])
      hmatch
    · simp
    · simpa [hprefEval, syracuseWordConst] using hcontract
  simpa [a0SemanticDropCommonPrefix, n] using hdrop

/-- Strict-descent form of the second infinite A0 residue leaf. -/
theorem hasStrictDescent_a0_t_ten_mod_thirtytwo (u : ℕ) :
    HasStrictDescent (2663 + 8192 * u) := by
  have hdrop := directDropAt_eight_a0_t_ten_mod_thirtytwo u
  have hn :
      103 + 256 * (10 + 32 * u) = 2663 + 8192 * u := by
    ring
  rw [hn] at hdrop
  exact hasStrictDescent_of_directDropAt hdrop

/-!
The three shortest expansive phantom templates do not themselves give an A0
drop.  Their scaled endpoints are respectively

  `3*x + 1`, `9*x + 5`, and `9*x + 7`,

where `x = 593 + 1458*t`; each is already larger than the correspondingly
scaled source `103 + 256*t`.  Thus a high-valuation exit, such as the two
families above, is genuinely necessary.
-/

theorem a0Endpoint_word_one_not_drop
    (t : ℕ)
    (hmatch :
      SyracuseWordMatchesFrom [1] (593 + 1458 * t)) :
    ¬ evalSyracuseWord [1] (593 + 1458 * t) < 103 + 256 * t := by
  have heq :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches
      [1] (593 + 1458 * t) hmatch
  norm_num [syracuseWordConst] at heq
  intro hdrop
  have hscaled :
      2 * evalSyracuseWord [1] (593 + 1458 * t)
        < 2 * (103 + 256 * t) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < (2 : ℕ))).mpr hdrop
  rw [heq] at hscaled
  omega

theorem a0Endpoint_word_one_two_not_drop
    (t : ℕ)
    (hmatch :
      SyracuseWordMatchesFrom [1, 2] (593 + 1458 * t)) :
    ¬ evalSyracuseWord [1, 2] (593 + 1458 * t) < 103 + 256 * t := by
  have heq :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches
      [1, 2] (593 + 1458 * t) hmatch
  norm_num [syracuseWordConst] at heq
  intro hdrop
  have hscaled :
      8 * evalSyracuseWord [1, 2] (593 + 1458 * t)
        < 8 * (103 + 256 * t) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < (8 : ℕ))).mpr hdrop
  rw [heq] at hscaled
  omega

theorem a0Endpoint_word_two_one_not_drop
    (t : ℕ)
    (hmatch :
      SyracuseWordMatchesFrom [2, 1] (593 + 1458 * t)) :
    ¬ evalSyracuseWord [2, 1] (593 + 1458 * t) < 103 + 256 * t := by
  have heq :=
    evalSyracuseWord_mul_pow_sum_eq_affine_of_matches
      [2, 1] (593 + 1458 * t) hmatch
  norm_num [syracuseWordConst] at heq
  intro hdrop
  have hscaled :
      8 * evalSyracuseWord [2, 1] (593 + 1458 * t)
        < 8 * (103 + 256 * t) :=
    (Nat.mul_lt_mul_left (by norm_num : 0 < (8 : ℕ))).mpr hdrop
  rw [heq] at hscaled
  omega

end CollatzShadowing
