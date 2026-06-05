/-
Phase 1 — Mathlib infrastructure inventory.

This is a scratch buffer for exploring the Mathlib API used by
`CollatzShadowing/INVENTORY.md`. It is intentionally not imported by
the main `CollatzShadowing` library.

The first version of this file used broad `import Mathlib` plus a few
examples that no longer reduce with `by decide` in Mathlib v4.29.1.
This version keeps the same coverage, but every declaration below
typechecks under the pinned toolchain.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-04.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic

noncomputable section

namespace CollatzShadowing.Inventory

/-!
## Section 1.1 — `padicValNat`, `padicValInt`, `padicValRat`,
`multiplicity`, and `padicNorm`
-/

#check @padicValNat
#check @padicValInt
#check @padicValRat
#check @padicNorm

#check padicValNat.self
#check padicValNat.eq_zero_of_not_dvd
#check padicValInt.of_nat
#check padicValRat.of_nat
#check padicValRat.of_int

#check padicValRat.mul
#check padicValRat.pow
#check padicValRat.min_le_padicValRat_add
#check padicValRat.add_eq_min

#check padicValNat.prime_pow
#check padicValNat_dvd_iff

-- General multiplicity API. Useful as a fallback for prime-power divisibility.
#check @multiplicity
#check @emultiplicity
#check pow_dvd_of_le_multiplicity
#check pow_multiplicity_dvd
#check multiplicity_eq_of_dvd_of_not_dvd

-- Lightweight aliases planned for `Basic.lean`.
def nu2Nat (n : ℕ) : ℕ := padicValNat 2 n
def nu2Int (z : ℤ) : ℕ := padicValInt 2 z
def nu2Rat (q : ℚ) : ℤ := padicValRat 2 q

/-!
## Section 1.2 — `Padic`, `PadicInt`, and valuation API
-/

#check @Padic
#check @PadicInt

-- Standard notations for the 2-adics.
example : ℚ_[2] = Padic 2 := rfl
example : ℤ_[2] = PadicInt 2 := rfl

#check @Padic.valuation
#check @PadicInt.valuation

-- Valuation compatibility with casts from ordinary number systems.
#check Padic.valuation_ratCast
#check Padic.valuation_intCast
#check Padic.valuation_natCast
#check PadicInt.valuation_coe

-- Algebraic and ultrametric valuation facts.
#check Padic.valuation_mul
#check Padic.valuation_inv
#check Padic.valuation_pow
#check Padic.valuation_zpow
#check Padic.le_valuation_add

#check PadicInt.valuation_mul
#check PadicInt.valuation_pow
#check PadicInt.valuation_p
#check PadicInt.valuation_p_pow_mul
#check PadicInt.mem_span_pow_iff_le_valuation

-- The useful maximal-ideal fact is not `PadicInt.maximalIdeal`.
#check PadicInt.maximalIdeal_eq_span_p

example : IsDiscreteValuationRing (ℤ_[2]) := by infer_instance
example : Field (ℚ_[2]) := by infer_instance

/-!
## Section 1.3 — coercions into `ℤ_[2]` and `ℚ_[2]`
-/

example (n : ℕ) : ℤ_[2] := (n : ℤ_[2])
example (z : ℤ) : ℤ_[2] := (z : ℤ_[2])

example (n : ℕ) : ℚ_[2] := (n : ℚ_[2])
example (z : ℤ) : ℚ_[2] := (z : ℚ_[2])
example (q : ℚ) : ℚ_[2] := (q : ℚ_[2])

example (x : ℤ_[2]) : ℚ_[2] := (x : ℚ_[2])

#check PadicInt.coe_natCast
#check PadicInt.coe_intCast
#check Padic.coe_inj
#check Padic.coe_add
#check Padic.coe_sub
#check Padic.coe_mul
#check Padic.coe_div

-- A rational with odd denominator is a 2-adic integer.
#check Padic.norm_rat_le_one

def ratToZ2 (q : ℚ) (hden : ¬ (2 : ℕ) ∣ q.den) : ℤ_[2] :=
  ⟨(q : ℚ_[2]), Padic.norm_rat_le_one hden⟩

/-!
## Section 1.4 — congruence `n ≡ q (mod 2^k)` in `ℤ_[2]`

Primary representation: ideal membership. This handles the zero
difference correctly, unlike a raw inequality with `PadicInt.valuation`,
because Mathlib has `(0 : ℤ_[2]).valuation = 0` by convention.
-/

def PadicCongruentModPow2 (x y : ℤ_[2]) (k : ℕ) : Prop :=
  x - y ∈ (Ideal.span {((2 : ℤ_[2]) ^ k)} : Ideal ℤ_[2])

-- Divisibility syntax is available, but ideal membership is clearer.
example (x y : ℤ_[2]) (k : ℕ) : Prop :=
  (2 : ℤ_[2]) ^ k ∣ (x - y)

-- In the nonzero case, ideal membership is equivalent to a valuation bound.
example (x y : ℤ_[2]) (k : ℕ) (hxy : x - y ≠ 0) :
    PadicCongruentModPow2 x y k ↔ k ≤ (x - y).valuation := by
  exact PadicInt.mem_span_pow_iff_le_valuation (x - y) hxy k

-- Shape of the future shadowing hypothesis.
example
    (n : ℕ) (q : ℤ_[2]) (k : ℕ)
    (_hcong : PadicCongruentModPow2 (n : ℤ_[2]) q k) :
    True := by
  trivial

/-!
## Section 1.5 — finite congruence APIs kept for comparison

These are useful for comparing with the Python scripts, but should not
be the primary model for Lemma 3.1.
-/

#check Nat.ModEq
#check Int.ModEq
#check Int.emod
#check ZMod

end CollatzShadowing.Inventory
