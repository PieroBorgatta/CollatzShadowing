/-
Positive affine endpoints force positive integral sources for words of
positive exponents. In particular the full ternary congruence already
implies the strict height inequality; it is not a further analytic input.

AI-assisted development: Codex with Piero Borgatta, 2026-11-13.
-/

import CollatzShadowing.LastExponentTransport
import CollatzShadowing.JointAtomDictionary
import Mathlib.RingTheory.Coprime.Lemmas

namespace CollatzShadowing.AffinePositivity

/-- There is no integral nonpositive source for a positive affine endpoint
when every prescribed exponent is positive. No oddness premise is needed
for this purely affine positivity statement. -/
theorem integer_source_pos (w : List ℕ) (x y : ℤ)
    (hpos : ∀ a ∈ w, 0 < a) (hy : 0 < y)
    (haff : (3 : ℤ) ^ w.length * x + (syracuseWordConst w : ℤ) =
      (2 : ℤ) ^ w.sum * y) : 0 < x := by
  induction w generalizing x with
  | nil =>
      have hxy : x = y := by simpa [syracuseWordConst] using haff
      simpa only [hxy] using hy
  | cons a rest ih =>
      have ha : 0 < a := hpos a (by simp)
      have hrest : ∀ b ∈ rest, 0 < b := by
        intro b hb
        exact hpos b (by simp [hb])
      have heq :
          (3 : ℤ) ^ rest.length * (3 * x + 1) +
            2 ^ a * (syracuseWordConst rest : ℤ) =
          2 ^ a * (2 ^ rest.sum * y) := by
        simp only [List.length_cons, List.sum_cons, syracuseWordConst,
          Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          pow_succ, pow_add] at haff
        nlinarith [haff]
      have hdiv : (2 : ℤ) ^ a ∣ 3 ^ rest.length * (3 * x + 1) := by
        refine ⟨2 ^ rest.sum * y - (syracuseWordConst rest : ℤ), ?_⟩
        nlinarith [heq]
      have hcop : IsCoprime ((2 : ℤ) ^ a) ((3 : ℤ) ^ rest.length) :=
        (by norm_num : IsCoprime (2 : ℤ) 3).pow
      obtain ⟨z, hz⟩ := hcop.dvd_of_dvd_mul_left hdiv
      have htail :
          (3 : ℤ) ^ rest.length * z + (syracuseWordConst rest : ℤ) =
          2 ^ rest.sum * y := by
        apply mul_left_cancel₀ (by positivity : (2 : ℤ) ^ a ≠ 0)
        calc
          2 ^ a * (3 ^ rest.length * z + (syracuseWordConst rest : ℤ)) =
              3 ^ rest.length * (2 ^ a * z) +
                2 ^ a * (syracuseWordConst rest : ℤ) := by ring
          _ = 2 ^ a * (2 ^ rest.sum * y) := by rw [← hz]; exact heq
      have hzpos : 0 < z := ih z hrest htail
      have htwo : (2 : ℤ) ≤ 2 ^ a := by
        obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
        have hpow : 0 < (2 : ℤ) ^ b := by positivity
        rw [pow_succ]
        omega
      have hprod := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ z by omega)
        (show (0 : ℤ) ≤ 2 ^ a by positivity)
      simp only [mul_one] at hprod
      omega

/-- The complete ternary congruence forces the affine height inequality.
The proof first constructs an integral source and then proves positivity. -/
theorem height_of_ternary_congruence (w : List ℕ) (y : ℕ)
    (hpos : ∀ a ∈ w, 0 < a) (hy : 0 < y)
    (hcong : 2 ^ w.sum * y ≡ syracuseWordConst w [MOD 3 ^ w.length]) :
    syracuseWordConst w < 2 ^ w.sum * y := by
  obtain ⟨x, hx⟩ := Nat.modEq_iff_dvd.mp hcong.symm
  have heq : (3 : ℤ) ^ w.length * x + (syracuseWordConst w : ℤ) =
      2 ^ w.sum * (y : ℤ) := by
    push_cast at hx
    linarith
  have hxpos := integer_source_pos w x y hpos (by exact_mod_cast hy) heq
  have hgain : (0 : ℤ) < 3 ^ w.length * x := mul_pos (by positivity) hxpos
  have hlt : (syracuseWordConst w : ℤ) < 2 ^ w.sum * (y : ℤ) := by linarith
  exact_mod_cast hlt

/-- For positive prescribed exponents and a positive target, the full
ternary congruence alone gives admissibility: height is automatic. -/
theorem admissible_iff_ternary_congruence (w : List ℕ) (y : ℕ)
    (hpos : ∀ a ∈ w, 0 < a) (hy : 0 < y) :
    JointAtomDictionary.Admissible w y ↔
      2 ^ w.sum * y ≡ syracuseWordConst w [MOD 3 ^ w.length] := by
  constructor
  · intro h
    exact ((JointAtomDictionary.admissible_iff_residue w y).mp h).2.symm
  · intro h
    exact (JointAtomDictionary.admissible_iff_residue w y).mpr
      ⟨height_of_ternary_congruence w y hpos hy h, h.symm⟩

/-- Exact positive odd predecessors are in bijection with full ternary
atoms. Oddness of the target is essential for the exact Syracuse claim. -/
theorem exact_source_iff_ternary_congruence (w : List ℕ) (y : ℕ)
    (hw : w ≠ []) (hpos : ∀ a ∈ w, 0 < a) (hy : 0 < y) (hyodd : Odd y) :
    (∃ x : ℕ, 0 < x ∧ Odd x ∧ SyracuseWordMatchesFrom w x ∧
      evalSyracuseWord w x = y) ↔
      2 ^ w.sum * y ≡ syracuseWordConst w [MOD 3 ^ w.length] := by
  rw [← JointAtomDictionary.admissible_iff_exact w y hw hpos hyodd]
  exact admissible_iff_ternary_congruence w y hpos hy

/-- A same-length finite atom catalogue counts distinct physical sources
exactly. No atom probability, completeness, or lower mass is asserted. -/
theorem card_ternary_atom_image (W : Finset (List ℕ)) (y k : ℕ)
    (hw : ∀ w ∈ W, w ≠ []) (hpos : ∀ w ∈ W, ∀ a ∈ w, 0 < a)
    (hlen : ∀ w ∈ W, w.length = k) (hy : 0 < y) (hyodd : Odd y) :
    ((W.filter (fun w => 2 ^ w.sum * y ≡ syracuseWordConst w
        [MOD 3 ^ w.length])).image
      (fun w => JointAtomDictionary.inverseSource w y)).card =
      (W.filter (fun w => 2 ^ w.sum * y ≡ syracuseWordConst w
        [MOD 3 ^ w.length])).card := by
  have hf : W.filter (fun w => JointAtomDictionary.Admissible w y) =
      W.filter (fun w => 2 ^ w.sum * y ≡ syracuseWordConst w
        [MOD 3 ^ w.length]) := by
    apply Finset.filter_congr
    intro w hw'
    exact admissible_iff_ternary_congruence w y (hpos w hw') hy
  rw [← hf]
  exact JointAtomDictionary.card_admissible_image W y k hw hpos hlen hyodd

end CollatzShadowing.AffinePositivity
