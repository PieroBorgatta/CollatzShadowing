/-
Basic definitions for the Lean formalization of the Collatz shadowing
lemma.

This file starts Phase 2 of `TODO.md`: the accelerated Syracuse map and
the 2-adic valuation aliases used by later phantom-word definitions.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-04.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

namespace CollatzShadowing

/-!
## 2-adic valuation aliases

Mathlib already provides the underlying p-adic valuation API:

* `padicValNat p n : ℕ`
* `padicValInt p z : ℕ`
* `padicValRat p q : ℤ`
* `PadicInt.valuation x : ℕ`

The aliases below specialize those declarations to `p = 2`, matching the
notation `ν₂` used in the paper.
-/

/-- The 2-adic valuation of a natural number. -/
def nu2Nat (n : ℕ) : ℕ :=
  padicValNat 2 n

/-- Unicode alias for the 2-adic valuation on naturals. -/
def ν₂ (n : ℕ) : ℕ :=
  nu2Nat n

/-- The 2-adic valuation of an integer. -/
def nu2Int (z : ℤ) : ℕ :=
  padicValInt 2 z

/-- The 2-adic valuation of a rational number. -/
def nu2Rat (q : ℚ) : ℤ :=
  padicValRat 2 q

/-- The 2-adic valuation on the 2-adic integers, using Mathlib's API. -/
noncomputable def nu2Z2 (x : ℤ_[2]) : ℕ :=
  x.valuation

/-- Unicode-named 2-adic valuation on `ℤ_[2]`. -/
noncomputable def ν₂Z2 (x : ℤ_[2]) : ℕ :=
  nu2Z2 x

/-!
## Accelerated Syracuse map

The paper's accelerated Syracuse map is used on odd positive integers:

```text
S(n) = (3n + 1) / 2 ^ ν₂(3n + 1).
```

We define it as a total function on `ℕ`; later theorem statements will
carry the oddness/positivity hypotheses needed for the intended use.
-/

/-- Numerator `3n + 1` of the accelerated Syracuse step. -/
def syracuseNumerator (n : ℕ) : ℕ :=
  3 * n + 1

/-- The number of powers of two removed in one accelerated Syracuse step. -/
def syracuseExponent (n : ℕ) : ℕ :=
  nu2Nat (syracuseNumerator n)

/-- Paper Section 2/3: accelerated Syracuse map on odd inputs. -/
def S (n : ℕ) : ℕ :=
  syracuseNumerator n / 2 ^ syracuseExponent n

/-- Descriptive alias for `S`. -/
def syracuseOddStep : ℕ → ℕ :=
  S

/-!
## Basic smoke checks

These are intentionally lightweight and definitional; substantive
properties begin in later phases.
-/

example : syracuseNumerator 1 = 4 := rfl
example : syracuseOddStep = S := rfl

end CollatzShadowing
