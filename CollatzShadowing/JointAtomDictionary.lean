/-
Exact finite dictionary between a forward Syracuse valuation word, its
ternary affine residue, and its positive predecessor at a fixed odd target.

Motivation: the fixed-length/fixed-total counting identity in rStation
Collatz paper 10, section 3 (fourier_wren, v3, 2026-10-22). The forward word
here is reversed relative to that source's offset convention. This is an
independent integration using the local exact-cylinder theorem. It does not
import a mixing estimate or an asymptotic predecessor-density statement.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-11-13.
-/

import CollatzShadowing.LastExponentTransport
import CollatzShadowing.WeightedWords

namespace CollatzShadowing.JointAtomDictionary

/-- The candidate positive source. Its height and divisibility conditions
are kept separate, because natural subtraction alone would conceal them. -/
def inverseSource (w : List ℕ) (y : ℕ) : ℕ :=
  (2 ^ w.sum * y - syracuseWordConst w) / 3 ^ w.length

/-- The exact ternary atom plus the strict height condition needed for a
positive source. No distribution of these atoms is assumed. -/
def Admissible (w : List ℕ) (y : ℕ) : Prop :=
  syracuseWordConst w < 2 ^ w.sum * y ∧
    3 ^ w.length ∣ 2 ^ w.sum * y - syracuseWordConst w

instance (w : List ℕ) (y : ℕ) : Decidable (Admissible w y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- With the height condition, divisibility is exactly a ternary congruence. -/
theorem admissible_iff_residue (w : List ℕ) (y : ℕ) :
    Admissible w y ↔ syracuseWordConst w < 2 ^ w.sum * y ∧
      syracuseWordConst w ≡ 2 ^ w.sum * y [MOD 3 ^ w.length] := by
  constructor
  · rintro ⟨hh, hd⟩
    exact ⟨hh, (Nat.modEq_iff_dvd' (Nat.le_of_lt hh)).mpr hd⟩
  · rintro ⟨hh, hd⟩
    exact ⟨hh, (Nat.modEq_iff_dvd' (Nat.le_of_lt hh)).mp hd⟩

theorem inverseSource_affine {w : List ℕ} {y : ℕ} (h : Admissible w y) :
    3 ^ w.length * inverseSource w y + syracuseWordConst w = 2 ^ w.sum * y := by
  have hd := Nat.div_mul_cancel h.2
  unfold inverseSource
  rw [Nat.mul_comm, hd]
  exact Nat.sub_add_cancel (Nat.le_of_lt h.1)

theorem inverseSource_pos {w : List ℕ} {y : ℕ} (h : Admissible w y) :
    0 < inverseSource w y := by
  have ha := inverseSource_affine h
  by_contra hz
  have heq : inverseSource w y = 0 := by omega
  rw [heq, mul_zero, zero_add] at ha
  exact (Nat.ne_of_lt h.1) ha

/-- Positive prescribed exponents force the actual source to be odd. -/
theorem source_odd_of_matches {w : List ℕ} {x : ℕ} (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 0 < a) (hm : SyracuseWordMatchesFrom w x) : Odd x := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons a rest =>
      have ha : 0 < a := hpos a (by simp)
      have hmul := pow_mul_syracuseStepWithExponent_eq_of_exponent hm.1
      have hdiv : 2 ^ a ∣ 3 * x + 1 := ⟨_, hmul.symm⟩
      have htwo : 2 ∣ 3 * x + 1 :=
        dvd_trans (dvd_pow_self 2 (Nat.ne_of_gt ha)) hdiv
      have hmod := Nat.mod_eq_zero_of_dvd htwo
      apply Nat.odd_iff.mpr
      omega

/-- An admissible odd target produces the exact positive odd source, with
all intermediate valuations certified by the affine-endpoint theorem. -/
theorem inverseSource_spec (w : List ℕ) (y : ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 0 < a) (hy : Odd y) (h : Admissible w y) :
    0 < inverseSource w y ∧ Odd (inverseSource w y) ∧
      SyracuseWordMatchesFrom w (inverseSource w y) ∧
      evalSyracuseWord w (inverseSource w y) = y := by
  obtain ⟨hm, he⟩ := LastExponentTransport.matches_and_endpoint_of_affine
    w (inverseSource w y) y hw hpos hy (inverseSource_affine h)
  exact ⟨inverseSource_pos h, source_odd_of_matches hw hpos hm, hm, he⟩

/-- Every actual positive exact predecessor gives both a height inequality
and an integral ternary atom, and equals the displayed inverse source. -/
theorem admissible_of_exact {w : List ℕ} {x y : ℕ} (hx : 0 < x)
    (hm : SyracuseWordMatchesFrom w x) (he : evalSyracuseWord w x = y) :
    Admissible w y ∧ inverseSource w y = x := by
  have ha := evalSyracuseWord_mul_pow_sum_eq_affine_of_matches w x hm
  rw [he] at ha
  have hp : 0 < 3 ^ w.length := by positivity
  have hh : syracuseWordConst w < 2 ^ w.sum * y := by nlinarith
  have hdiff : 2 ^ w.sum * y - syracuseWordConst w = 3 ^ w.length * x := by
    omega
  have had : Admissible w y := ⟨hh, by rw [hdiff]; exact dvd_mul_right _ _⟩
  refine ⟨had, ?_⟩
  have hb := inverseSource_affine had
  nlinarith

/-- The finite dictionary, with positivity and oddness stated explicitly.
An even target cannot be substituted into this equivalence. -/
theorem admissible_iff_exact (w : List ℕ) (y : ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 0 < a) (hy : Odd y) :
    Admissible w y ↔ ∃ x : ℕ, 0 < x ∧ Odd x ∧
      SyracuseWordMatchesFrom w x ∧ evalSyracuseWord w x = y := by
  constructor
  · intro h
    exact ⟨inverseSource w y, inverseSource_spec w y hw hpos hy h⟩
  · rintro ⟨x, hx, _hodd, hm, he⟩
    exact (admissible_of_exact hx hm he).1

/-- The cutoff is an exact affine height inequality, not a bound on the
valuation total alone. -/
theorem inverseSource_le_iff {w : List ℕ} {y X : ℕ} (h : Admissible w y) :
    inverseSource w y ≤ X ↔ 2 ^ w.sum * y ≤ 3 ^ w.length * X + syracuseWordConst w := by
  have ha := inverseSource_affine h
  have hp : 0 < 3 ^ w.length := by positivity
  constructor <;> intro hb <;> nlinarith

/-- At a fixed length, admissible words have distinct actual sources.
The total exponent may also be fixed, but is not needed for injectivity. -/
theorem inverseSource_injective_at_length {u v : List ℕ} {y : ℕ}
    (hu : u ≠ []) (hv : v ≠ [])
    (hupos : ∀ a ∈ u, 0 < a) (hvpos : ∀ a ∈ v, 0 < a) (hy : Odd y)
    (hau : Admissible u y) (hav : Admissible v y)
    (hlen : u.length = v.length)
    (hsource : inverseSource u y = inverseSource v y) : u = v := by
  have hm := (inverseSource_spec u y hu hupos hy hau).2.2.1
  have hn := (inverseSource_spec v y hv hvpos hy hav).2.2.1
  rw [← hsource] at hn
  exact WeightedVisits.matches_eq_of_length_eq hm hn hlen

/-- A finite profile is counted exactly by its distinct positive sources.
Only the same-length condition is needed; a fixed-total profile is a special
case. Completeness of any chosen catalogue is a separate application input. -/
theorem card_admissible_image (W : Finset (List ℕ)) (y k : ℕ)
    (hw : ∀ w ∈ W, w ≠ []) (hpos : ∀ w ∈ W, ∀ a ∈ w, 0 < a)
    (hlen : ∀ w ∈ W, w.length = k) (hy : Odd y) :
    ((W.filter (fun w => Admissible w y)).image (fun w => inverseSource w y)).card =
      (W.filter (fun w => Admissible w y)).card := by
  apply Finset.card_image_of_injOn
  intro u hu v hv hsource
  rcases Finset.mem_filter.mp hu with ⟨hu, hau⟩
  rcases Finset.mem_filter.mp hv with ⟨hv, hav⟩
  exact inverseSource_injective_at_length (hw u hu) (hw v hv)
    (hpos u hu) (hpos v hv) hy hau hav ((hlen u hu).trans (hlen v hv).symm) hsource

end CollatzShadowing.JointAtomDictionary
