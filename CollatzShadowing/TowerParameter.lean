/-
AI-assisted development: Codex with Piero Borgatta, 2026-09-24.
Exact dyadic transport of the cancellation-tower parameter.
This finite-level arithmetic makes no assertion about infinite positive orbits.
-/
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace CollatzShadowing.TowerParameter

/-- The odd cofactor at the phase-C exit when `v ≥ 1` and `q` is positive odd. -/
def quotient (v q : ℕ) : ℕ := (9 ^ (2 ^ v * q) - 1) / 2 ^ (v + 3)

/-- LTE specialized to the tower exponent, with all parameters unbounded. -/
theorem numerator_valuation {v d : ℕ} (hv : 1 ≤ v) (hd : 0 < d) :
    padicValNat 2 (9 ^ (2 ^ v * d) - 1) = v + 3 + padicValNat 2 d := by
  have hp : 0 < 2 ^ v := by positivity
  have he : Even (2 ^ v * d) :=
    (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega : v ≠ 0))).mul_right d
  have h := padicValNat.pow_two_sub_one (x := 9) (by norm_num)
    (by norm_num) (Nat.ne_of_gt (Nat.mul_pos hp hd)) he
  rw [padicValNat.mul (Nat.ne_of_gt hp) (Nat.ne_of_gt hd),
    padicValNat.prime_pow] at h
  have h10 : padicValNat 2 (9 + 1) = 1 := by
    change padicValNat 2 (2 ^ 1 * 5) = 1
    rw [padicValNat.mul (by decide) (by decide), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬2 ∣ 5)]
  have h8 : padicValNat 2 (9 - 1) = 3 := padicValNat.prime_pow 3
  rw [h10, h8] at h
  omega

/-- Division in the definition loses no remainder, including at `q = 0`. -/
theorem quotient_factorization {v : ℕ} (hv : 1 ≤ v) (q : ℕ) :
    2 ^ (v + 3) * quotient v q + 1 = 9 ^ (2 ^ v * q) := by
  by_cases hq : q = 0
  · subst q; simp [quotient]
  have hp : 1 < 9 ^ (2 ^ v * q) := by
    exact Nat.one_lt_pow (by positivity) (by norm_num)
  have hval := numerator_valuation hv (Nat.pos_of_ne_zero hq)
  have hd : 2 ^ (v + 3) ∣ 9 ^ (2 ^ v * q) - 1 :=
    (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
  have h := Nat.mul_div_cancel' hd
  dsimp [quotient]
  omega

/-- Strict order on natural parameters is retained by the cofactor map. -/
theorem quotient_strictMono {v : ℕ} (hv : 1 ≤ v) : StrictMono (quotient v) := by
  intro r q hrq
  have hpow : 9 ^ (2 ^ v * r) < 9 ^ (2 ^ v * q) := by
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.mul_lt_mul_of_pos_left hrq (by positivity))
  have hr := quotient_factorization hv r
  have hq := quotient_factorization hv q
  apply (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ (v + 3))).mp
  omega

/-- The cofactor is an exact dyadic isometry on distinct ordered parameters. -/
theorem quotient_difference_valuation {v r q : ℕ} (hv : 1 ≤ v) (hrq : r < q) :
    padicValNat 2 (quotient v q - quotient v r) = padicValNat 2 (q - r) := by
  have hdiff : 9 ^ (2 ^ v * q) - 9 ^ (2 ^ v * r) =
      9 ^ (2 ^ v * r) * (9 ^ (2 ^ v * (q - r)) - 1) := by
    have he : 2 ^ v * q = 2 ^ v * r + 2 ^ v * (q - r) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hrq.le]
    rw [he, pow_add]
    simpa only [Nat.mul_one] using
      (Nat.mul_sub (9 ^ (2 ^ v * r)) (9 ^ (2 ^ v * (q - r))) 1).symm
  have hf : 2 ^ (v + 3) * (quotient v q - quotient v r) =
      9 ^ (2 ^ v * q) - 9 ^ (2 ^ v * r) := by
    rw [Nat.mul_sub]
    have hq := quotient_factorization hv q
    have hr := quotient_factorization hv r
    omega
  have hn : 9 ^ (2 ^ v * (q - r)) - 1 ≠ 0 := by
    have : 1 < 9 ^ (2 ^ v * (q - r)) :=
      Nat.one_lt_pow (Nat.mul_ne_zero (by positivity) (by omega)) (by norm_num)
    omega
  have hleft : quotient v q - quotient v r ≠ 0 :=
    Nat.ne_of_gt (Nat.sub_pos_of_lt (quotient_strictMono hv hrq))
  have h := congrArg (padicValNat 2) (hf.trans hdiff)
  rw [padicValNat.mul (by positivity) hleft, padicValNat.prime_pow,
    padicValNat.mul (by positivity) hn,
    padicValNat.pow _ (by norm_num), numerator_valuation hv (by omega)] at h
  rw [show padicValNat 2 9 = 0 from padicValNat.eq_zero_of_not_dvd (by decide),
    mul_zero, zero_add] at h
  omega

/-- Exact preservation and reflection of every finite binary congruence. -/
theorem quotient_modEq_iff {v : ℕ} (hv : 1 ≤ v) (b q r : ℕ) :
    quotient v q ≡ quotient v r [MOD 2 ^ b] ↔ q ≡ r [MOD 2 ^ b] := by
  suffices h : ∀ q r : ℕ, q < r →
      (quotient v q ≡ quotient v r [MOD 2 ^ b] ↔ q ≡ r [MOD 2 ^ b]) by
    rcases lt_trichotomy q r with hqr | hqr | hqr
    · exact h q r hqr
    · subst r; constructor <;> intro _ <;> rfl
    · exact ⟨fun hh => ((h r q hqr).mp hh.symm).symm,
        fun hh => ((h r q hqr).mpr hh.symm).symm⟩
  intro q r hqr
  rw [Nat.modEq_iff_dvd' (quotient_strictMono hv hqr).le,
    Nat.modEq_iff_dvd' hqr.le,
    padicValNat_dvd_iff_le (Nat.ne_of_gt (Nat.sub_pos_of_lt (quotient_strictMono hv hqr))),
    padicValNat_dvd_iff_le (Nat.ne_of_gt (Nat.sub_pos_of_lt hqr)),
    quotient_difference_valuation hv hqr]

/-- Every binary residue has a unique parameter representative. -/
theorem quotient_residue_bijective {v : ℕ} (hv : 1 ≤ v) (b : ℕ) :
    Function.Bijective (fun q : Fin (2 ^ b) =>
      (⟨quotient v q % 2 ^ b, Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ b))) := by
  apply (Finite.injective_iff_bijective).mp
  intro q r h
  apply Fin.ext
  have he : quotient v q ≡ quotient v r [MOD 2 ^ b] := congrArg Fin.val h
  have hm := (quotient_modEq_iff hv b q r).mp he
  change (q : ℕ) % 2 ^ b = (r : ℕ) % 2 ^ b at hm
  simpa only [Nat.mod_eq_of_lt q.isLt, Nat.mod_eq_of_lt r.isLt] using hm

/-- Adding an affine odd multiplier retains the full residue permutation. -/
theorem affine_residue_bijective {v : ℕ} (hv : 1 ≤ v) (b s d : ℕ) :
    Function.Bijective (fun q : Fin (2 ^ b) =>
      (⟨(3 ^ s * quotient v q + d) % 2 ^ b,
        Nat.mod_lt _ (by positivity)⟩ : Fin (2 ^ b))) := by
  apply (Finite.injective_iff_bijective).mp
  intro q r h
  apply Fin.ext
  have he : 3 ^ s * quotient v q + d ≡
      3 ^ s * quotient v r + d [MOD 2 ^ b] := congrArg Fin.val h
  have hc : (2 ^ b).Coprime (3 ^ s) :=
    ((by decide : Nat.Coprime 2 3).pow_left b).pow_right s
  have hm := (quotient_modEq_iff hv b q r).mp
    (Nat.ModEq.cancel_left_of_coprime hc (he.add_right_cancel' d))
  change (q : ℕ) % 2 ^ b = (r : ℕ) % 2 ^ b at hm
  simpa only [Nat.mod_eq_of_lt q.isLt, Nat.mod_eq_of_lt r.isLt] using hm

/-- In particular odd parameters correspond exactly to odd cofactors. -/
theorem quotient_mod_two {v : ℕ} (hv : 1 ≤ v) (q : ℕ) :
    quotient v q % 2 = q % 2 := by
  have h := quotient_modEq_iff hv 1 q 0
  simp only [quotient, mul_zero, pow_zero, Nat.sub_self, Nat.zero_div,
    pow_one, Nat.ModEq, Nat.zero_mod] at h
  have hq := Nat.mod_lt q (by decide : 0 < 2)
  have hQ := Nat.mod_lt (quotient v q) (by decide : 0 < 2)
  change (quotient v q % 2 = 0 ↔ q % 2 = 0) at h
  omega

end CollatzShadowing.TowerParameter
