/-
AI-assisted development: Codex with Piero Borgatta, 2026-09-24.
Every admissible finite suffix occurs after a cancellation-tower burst.
The parameter may vary with the suffix: no infinite natural orbit is asserted.
-/
import CollatzShadowing.TowerParameter
import CollatzShadowing.ExactCylinders
import CollatzShadowing.CancellationTower

namespace CollatzShadowing.TowerParameter

/-- Endpoint of an exponent-one burst; phase C has `s=v`, phase B `s=v+4`. -/
def burstEnd (v s q : ℕ) : ℕ := 2 * 3 ^ s * quotient v q - 1

private theorem quotient_pos {v q : ℕ} (hv : 1 ≤ v) (hq : 0 < q) :
    0 < quotient v q := by
  have h := quotient_strictMono hv hq
  simpa only [quotient, mul_zero, pow_zero, Nat.sub_self, Nat.zero_div] using h

private theorem burstEnd_add_one {v q : ℕ} (hv : 1 ≤ v) (hq : 0 < q) (s : ℕ) :
    burstEnd v s q + 1 = 2 * 3 ^ s * quotient v q := by
  have hQ := quotient_pos hv hq
  have hc : 0 < 3 ^ s := by positivity
  have hp : 0 < 2 * 3 ^ s * quotient v q := by positivity
  unfold burstEnd
  omega

/-- The normalization constant is even when the first exponent is at least two. -/
private theorem word_constant_div_four {a : ℕ} (ha : 2 ≤ a) (w : List ℕ) :
    4 ∣ syracuseWordConst (a :: w) + 3 ^ (a :: w).length := by
  have hdiv : 4 ∣ 2 ^ a := by
    simpa using (pow_dvd_pow 2 ha : 2 ^ 2 ∣ 2 ^ a)
  have he : syracuseWordConst (a :: w) + 3 ^ (a :: w).length =
      4 * 3 ^ w.length + 2 ^ a * syracuseWordConst w := by
    simp only [syracuseWordConst, List.length_cons, pow_succ]
    ring
  rw [he]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hdiv _)

/-- An exact finite word becomes one affine congruence in the original cofactor. -/
theorem suffix_iff_affine_residue {v q a : ℕ} (hv : 1 ≤ v) (hq : 0 < q)
    (ha : 2 ≤ a) (w : List ℕ) (hw : ∀ b ∈ w, 0 < b) (s : ℕ) :
    SyracuseWordMatchesFrom (a :: w) (burstEnd v s q) ↔
      3 ^ ((a :: w).length + s) * quotient v q +
          (syracuseWordConst (a :: w) + 3 ^ (a :: w).length) / 2 ≡
        2 ^ ((a :: w).sum - 1) + 3 ^ (a :: w).length [MOD 2 ^ (a :: w).sum] := by
  let A := (a :: w).sum
  let P := 3 ^ (a :: w).length
  let C := syracuseWordConst (a :: w)
  have hA : 2 ≤ A := by change 2 ≤ a + w.sum; omega
  have hdiv : 2 ∣ C + P := dvd_trans (by decide : 2 ∣ 4) (word_constant_div_four ha w)
  have hhalf : 2 * ((C + P) / 2) = C + P := Nat.mul_div_cancel' hdiv
  have hz := burstEnd_add_one hv hq s
  have he : syracuseWordAffineNumerator (a :: w) (burstEnd v s q) + 2 * P =
      2 * (3 ^ ((a :: w).length + s) * quotient v q + (C + P) / 2) := by
    change P * burstEnd v s q + C + 2 * P =
      2 * (3 ^ ((a :: w).length + s) * quotient v q + (C + P) / 2)
    rw [show 3 ^ ((a :: w).length + s) = P * 3 ^ s from pow_add _ _ _]
    nlinarith [congrArg (fun t => P * t) hz]
  have ht : 2 ^ A + 2 * P = 2 * (2 ^ (A - 1) + P) := by
    have hp : 2 ^ A = 2 * 2 ^ (A - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hp]; ring
  have hM : syracuseWordExactResidueModulus (a :: w) = 2 * 2 ^ A := by
    simp [syracuseWordExactResidueModulus, A, pow_succ, Nat.mul_comm]
  have hsmall : 2 ^ A < syracuseWordExactResidueModulus (a :: w) := by
    rw [hM]
    have : 0 < 2 ^ A := by positivity
    omega
  have hpos : ∀ b ∈ a :: w, 0 < b := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · omega
    · exact hw b hb
  rw [syracuseWordMatches_iff_exactResidue _ _ (by simp) hpos]
  change syracuseWordAffineNumerator (a :: w) (burstEnd v s q) %
    syracuseWordExactResidueModulus (a :: w) = 2 ^ A ↔ _
  have hiff : (syracuseWordAffineNumerator (a :: w) (burstEnd v s q) %
      syracuseWordExactResidueModulus (a :: w) = 2 ^ A) ↔
      (syracuseWordAffineNumerator (a :: w) (burstEnd v s q) ≡ 2 ^ A
        [MOD syracuseWordExactResidueModulus (a :: w)]) := by
    change (_ = _) ↔ (_ = _ % _)
    rw [Nat.mod_eq_of_lt hsmall]
  rw [hiff]
  rw [← Nat.ModEq.add_iff_right (Nat.ModEq.refl (2 * P)), he, ht, hM,
    Nat.ModEq.mul_left_cancel_iff' (by decide : 2 ≠ 0)]

/-- Every admissible finite suffix determines exactly one odd parameter class.
The modulus is `2^(sum word)`, relative to the original tower parameter q. -/
theorem finite_suffix_residue {v a : ℕ} (hv : 1 ≤ v) (ha : 2 ≤ a)
    (w : List ℕ) (hw : ∀ b ∈ w, 0 < b) (s : ℕ) :
    ∃ r : ℕ, r < 2 ^ (a :: w).sum ∧ Odd r ∧
      ∀ q : ℕ, 0 < q →
        (SyracuseWordMatchesFrom (a :: w) (burstEnd v s q) ↔
          q % 2 ^ (a :: w).sum = r) := by
  let A := (a :: w).sum
  let L := (a :: w).length + s
  let D := (syracuseWordConst (a :: w) + 3 ^ (a :: w).length) / 2
  let T := 2 ^ (A - 1) + 3 ^ (a :: w).length
  have hA : 2 ≤ A := by change 2 ≤ a + w.sum; omega
  obtain ⟨r, hr⟩ := (affine_residue_bijective hv A L D).2
    ⟨T % 2 ^ A, Nat.mod_lt _ (by positivity)⟩
  have hres : 3 ^ L * quotient v r + D ≡ T [MOD 2 ^ A] := congrArg Fin.val hr
  have hD : D % 2 = 0 := by
    obtain ⟨k, hk⟩ := word_constant_div_four ha w
    change ((syracuseWordConst (a :: w) + 3 ^ (a :: w).length) / 2) % 2 = 0
    rw [hk]
    omega
  have hT : T % 2 = 1 := by
    have hpow : 2 ^ (A - 1) % 2 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
    simp [T, Nat.add_mod, Nat.pow_mod, hpow]
  have hmod2 := hres.of_dvd (dvd_pow_self 2 (by omega : A ≠ 0))
  have hrodd : Odd (r : ℕ) := by
    apply Nat.odd_iff.mpr
    change (3 ^ L * quotient v r + D) % 2 = T % 2 at hmod2
    simpa [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hD, hT, quotient_mod_two hv] using hmod2
  refine ⟨r, r.isLt, hrodd, ?_⟩
  intro q hq
  rw [suffix_iff_affine_residue hv hq ha w hw s]
  change (3 ^ L * quotient v q + D ≡ T [MOD 2 ^ A]) ↔ q % 2 ^ A = (r : ℕ)
  have hc : (2 ^ A).Coprime (3 ^ L) :=
    ((by decide : Nat.Coprime 2 3).pow_left A).pow_right L
  constructor
  · intro h
    have hh := Nat.ModEq.cancel_left_of_coprime hc ((h.trans hres.symm).add_right_cancel' D)
    have hh' := (quotient_modEq_iff hv A q r).mp hh
    change q % 2 ^ A = (r : ℕ) % 2 ^ A at hh'
    exact hh'.trans (Nat.mod_eq_of_lt r.isLt)
  · intro h
    have hh : q ≡ (r : ℕ) [MOD 2 ^ A] := by
      change q % 2 ^ A = (r : ℕ) % 2 ^ A
      rwa [Nat.mod_eq_of_lt r.isLt]
    exact (((quotient_modEq_iff hv A q r).mpr hh).mul_left (3 ^ L)).add_right D |>.trans hres

/-- Every finite suffix is realized at arbitrarily large positive odd parameters. -/
theorem finite_suffix_arbitrarily_large {v a : ℕ} (hv : 1 ≤ v) (ha : 2 ≤ a)
    (w : List ℕ) (hw : ∀ b ∈ w, 0 < b) (s B : ℕ) :
    ∃ q : ℕ, B < q ∧ Odd q ∧ SyracuseWordMatchesFrom (a :: w) (burstEnd v s q) := by
  obtain ⟨r, hr, hodd, hmatch⟩ := finite_suffix_residue hv ha w hw s
  let M := 2 ^ (a :: w).sum
  have hM : 0 < M := by positivity
  have he : Even M := even_iff_two_dvd.mpr (dvd_pow_self 2 (by simp; omega))
  let q := r + M * (B + 1)
  have hq : B < q := by dsimp [q]; nlinarith
  refine ⟨q, hq, hodd.add_even (he.mul_right _), (hmatch q (by omega)).mpr ?_⟩
  change (r + M * (B + 1)) % M = r
  simpa using Nat.add_mul_mod_self_left r M (B + 1) |>.trans (Nat.mod_eq_of_lt hr)

/-- A whole burst of exponent-one steps, without an upper bound on its length. -/
theorem one_burst_iterate (l u : ℕ) (hu : 0 < u) :
    S^[l] (2 ^ (l + 1) * u - 1) = 2 * 3 ^ l * u - 1 := by
  induction l generalizing u with
  | zero => simp
  | succ l ih =>
      have hpow : 0 < 2 ^ l := by positivity
      have hp : 0 < 2 ^ l * u := Nat.mul_pos hpow hu
      have he1 : 2 ^ (l + 1) * (3 * u) = 6 * (2 ^ l * u) := by
        rw [pow_succ]; ring
      have he2 : 2 ^ (l + 1 + 1) * u = 4 * (2 ^ l * u) := by
        rw [pow_succ, pow_succ]; ring
      have hodd : Odd (2 ^ (l + 1) * (3 * u) - 1) := by
        rw [he1]
        exact ⟨3 * (2 ^ l * u) - 1, by omega⟩
      have he : syracuseNumerator (2 ^ (l + 1 + 1) * u - 1) =
          2 ^ 1 * (2 ^ (l + 1) * (3 * u) - 1) := by
        simp only [syracuseNumerator, he1, he2, pow_one]
        omega
      have hs := (syracuseStep_of_num_eq_two_pow_mul_odd he hodd).2
      rw [Function.iterate_succ_apply, hs, ih (3 * u) (by omega), pow_succ]
      congr 1
      ring

/-- The phase-C exit and its full following burst retain the original parameter. -/
theorem phaseC_exit_burst {v q : ℕ} (hv : 1 ≤ v) (hq : 0 < q) :
    S^[v] ((9 ^ (2 ^ v * q) - 5) / 4) = burstEnd v v q := by
  have hQ := quotient_pos hv hq
  have hf := quotient_factorization hv q
  have hp : 2 ^ (v + 3) = 4 * 2 ^ (v + 1) := by
    rw [show v + 3 = (v + 1) + 2 by omega, pow_add]; norm_num; ring
  rw [hp, mul_assoc] at hf
  have he : (9 ^ (2 ^ v * q) - 5) / 4 = 2 ^ (v + 1) * quotient v q - 1 := by
    have : 0 < 2 ^ (v + 1) * quotient v q := by positivity
    omega
  rw [he, one_burst_iterate v (quotient v q) hQ]
  rfl

/-- Phase B has two more exponent-one steps and an extra factor 81 at the endpoint. -/
theorem phaseB_exit_burst {v q : ℕ} (hv : 1 ≤ v) (hq : 0 < q) :
    S^[v + 2] (9 ^ (2 ^ v * q + 1) - 10) = burstEnd v (v + 4) q := by
  have hQ := quotient_pos hv hq
  have hf := quotient_factorization hv q
  have he : 9 ^ (2 ^ v * q + 1) - 10 = 2 ^ (v + 2 + 1) * (9 * quotient v q) - 1 := by
    rw [pow_succ]
    have hpow : v + 2 + 1 = v + 3 := by omega
    rw [hpow]
    have hpos : 0 < 2 ^ (v + 3) * quotient v q := by positivity
    rw [show 2 ^ (v + 3) * (9 * quotient v q) =
      9 * (2 ^ (v + 3) * quotient v q) by ring]
    omega
  rw [he, one_burst_iterate (v + 2) (9 * quotient v q) (by omega)]
  unfold burstEnd
  rw [show v + 4 = (v + 2) + 2 by omega, pow_add]
  norm_num
  congr 1
  ring

/-- Complete phase-C tower prefix, including the reset and the two-step exit. -/
theorem phaseC_tower_exit {v q : ℕ} (hv : 1 ≤ v) (hq : 0 < q) :
    S^[2 * (2 ^ v * q) + 1] (cancellationTowerSource (3 * (2 ^ v * q))) =
      (9 ^ (2 ^ v * q) - 5) / 4 := by
  let d := 2 ^ v * q
  have hvpow : 2 ≤ 2 ^ v := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hv
  have hd : 2 ≤ d := by dsimp [d]; nlinarith
  have heven : Even (3 * d) := by
    exact ((even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : v ≠ 0))).mul_right q).mul_left 3
  have hi := cancellationTower_initial (k := 3 * d) (by omega) heven
  have hp : 2 ^ (3 * d) = 8 ^ (d - 1) * 8 := by
    rw [pow_mul]; norm_num
    rw [← pow_succ]; congr 1; omega
  rw [hp] at hi
  have hm : S^[2 * (d - 1) + 1] (cancellationTowerSource (3 * d)) =
      8 * 9 ^ (d - 1) - 5 := by
    rw [Function.iterate_succ_apply, hi.2,
      cancellationTower_iterate (d - 1) 8 (by decide) (by decide)]
    rw [Nat.mul_comm]
  have hx := cancellationTower_exit_three (d - 1)
  have htime : 2 * d + 1 = (2 * (d - 1) + 1) + 1 + 1 := by omega
  change S^[2 * d + 1] (cancellationTowerSource (3 * d)) = (9 ^ d - 5) / 4
  rw [htime, Function.iterate_succ_apply', Function.iterate_succ_apply', hm,
    hx.2.1, hx.2.2.2, Nat.sub_add_cancel (by omega : 1 ≤ d)]

/-- The actual orbit from the original source reaches the cofactor endpoint. -/
theorem phaseC_tower_burst {v q : ℕ} (hv : 1 ≤ v) (hq : 0 < q) :
    S^[2 * (2 ^ v * q) + 1 + v] (cancellationTowerSource (3 * (2 ^ v * q))) =
      burstEnd v v q := by
  rw [Nat.add_comm (2 * (2 ^ v * q) + 1) v, Function.iterate_add_apply,
    phaseC_tower_exit hv hq, phaseC_exit_burst hv hq]

/-- Every finite admissible suffix occurs after a genuine phase-C tower,
for arbitrarily large positive odd parameters. This is a finite-word theorem. -/
theorem tower_finite_suffix_arbitrarily_large {v a : ℕ} (hv : 1 ≤ v) (ha : 2 ≤ a)
    (w : List ℕ) (hw : ∀ b ∈ w, 0 < b) (B : ℕ) :
    ∃ q : ℕ, B < q ∧ Odd q ∧
      SyracuseWordMatchesFrom (a :: w)
        (S^[2 * (2 ^ v * q) + 1 + v] (cancellationTowerSource (3 * (2 ^ v * q)))) := by
  obtain ⟨q, hq, ho, hm⟩ := finite_suffix_arbitrarily_large hv ha w hw v B
  refine ⟨q, hq, ho, ?_⟩
  rwa [phaseC_tower_burst hv (by omega)]

/-- A long run of further growth can follow exponent two after the actual tower.
The positive parameter changes with the requested finite length. -/
theorem tower_arbitrarily_long_one_suffix {v : ℕ} (hv : 1 ≤ v) (l B : ℕ) :
    ∃ q : ℕ, B < q ∧ Odd q ∧
      SyracuseWordMatchesFrom (2 :: List.replicate l 1)
        (S^[2 * (2 ^ v * q) + 1 + v] (cancellationTowerSource (3 * (2 ^ v * q)))) := by
  apply tower_finite_suffix_arbitrarily_large hv (by decide)
  intro b hb
  have : b = 1 := (List.mem_replicate.mp hb).2
  omega

/-- A height-sensitive criterion: the least positive parameter residue must
fit below the given parameter bound. This does not bound all infinite words. -/
theorem finite_suffix_bounded_iff {v a : ℕ} (hv : 1 ≤ v) (ha : 2 ≤ a)
    (w : List ℕ) (hw : ∀ b ∈ w, 0 < b) (s : ℕ) :
    ∃ r : ℕ, 0 < r ∧ r < 2 ^ (a :: w).sum ∧ Odd r ∧
      ∀ B : ℕ, (∃ q : ℕ, 0 < q ∧ q ≤ B ∧
        SyracuseWordMatchesFrom (a :: w) (burstEnd v s q)) ↔ r ≤ B := by
  obtain ⟨r, hr, ho, hm⟩ := finite_suffix_residue hv ha w hw s
  have hrpos : 0 < r := by obtain ⟨t, ht⟩ := ho; omega
  refine ⟨r, hrpos, hr, ho, ?_⟩
  intro B
  constructor
  · rintro ⟨q, hq, hqB, hword⟩
    have hres := (hm q hq).mp hword
    have hle := Nat.mod_le q (2 ^ (a :: w).sum)
    omega
  · intro hrB
    exact ⟨r, hrpos, hrB, (hm r hrpos).mpr (Nat.mod_eq_of_lt hr)⟩

end CollatzShadowing.TowerParameter
