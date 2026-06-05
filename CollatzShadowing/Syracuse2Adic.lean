/-
2-adic extension of the accelerated Syracuse map (Phase 3 infrastructure).

This file provides `Syracuse2adic : ℤ_[2] → ℤ_[2]`, the natural
extension to the 2-adic integers of the accelerated Syracuse map
defined in `Basic.lean` on `ℕ`. It is the formal counterpart of the
single map `S` written in the paper, which is iterated symmetrically
on integers `n` and on the rational/2-adic phantom representatives
`q_w` (cf. paper Section 3, Lemma 3.1 proof).

## Faithfulness to the paper

The paper (Section 2 and the proof of Lemma 3.1) treats `S` as a
*single* map satisfying

```text
S(x) := (3·x + 1) / 2^{ν₂(3·x + 1)},
```

defined "wherever both sides make sense". For positive odd integers
the right-hand side is a positive integer; for `q_w ∈ ℤ_[2]` (the
2-adic representative of an expansive phantom) the right-hand side is
again in `ℤ_[2]`. The paper iterates `S^j` symmetrically on both kinds
of input.

We mirror this exactly with a single `Syracuse2adic : ℤ_[2] → ℤ_[2]`.

### Documented deviation: total extension at the degenerate point

The element `x = -1/3 ∈ ℤ_[2]` (which exists, since `3` is a unit in
`ℤ_[2]`) satisfies `3·x + 1 = 0`. The paper does not specify `S` at
this point, since it is not in any phantom orbit and not a positive
integer. Our definition extends `S` by the convention `S(-1/3) := 0`.

This extension is **operationally harmless**:

* No expansive phantom has `q_w = -1/3` (its orbit would be the
  empty cycle, which is not expansive).
* No positive natural `n` casts to `-1/3` in `ℤ_[2]`.
* The shadowing congruence in Lemma 3.1 never places `n` in the
  vicinity of `-1/3` for any input of interest.

The benefit is a single total function with no bookkeeping for
side hypotheses, giving Lean statements that match the paper's
notation 1:1.

Author: AI-assisted (Claude) + Piero Borgatta. Date: 2026-05-04.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import CollatzShadowing.Basic

namespace CollatzShadowing

/-!
## The 2-adic Syracuse map
-/

/--
**Paper Section 2/3, accelerated Syracuse map (2-adic extension).**

The accelerated Syracuse map extended to all of `ℤ_[2]`:

```text
Syracuse2adic(x) = (3·x + 1) / 2^{ν₂(3·x + 1)}.
```

Implemented via `PadicInt.unitCoeff`, which extracts the unit factor
in the canonical decomposition `y = u · 2^{ν₂(y)}` for non-zero
`y ∈ ℤ_[2]`. By convention we set the value at `x = -1/3` (the unique
point where `3·x + 1 = 0`) to `0`; see the file header for justification
of this deviation from the paper.
-/
noncomputable def Syracuse2adic (x : ℤ_[2]) : ℤ_[2] :=
  haveI : Decidable ((3 : ℤ_[2]) * x + 1 = 0) := Classical.dec _
  if h : (3 : ℤ_[2]) * x + 1 = 0 then 0
  else (PadicInt.unitCoeff h : ℤ_[2])

/-- The defining identity: for `x ∈ ℤ_[2]` with `3·x + 1 ≠ 0`, the
2-adic Syracuse step satisfies
`3·x + 1 = Syracuse2adic(x) · 2^{ν₂(3·x + 1)}`. -/
theorem Syracuse2adic_spec (x : ℤ_[2]) (h : (3 : ℤ_[2]) * x + 1 ≠ 0) :
    (3 : ℤ_[2]) * x + 1
      = Syracuse2adic x * (2 : ℤ_[2]) ^ ((3 : ℤ_[2]) * x + 1).valuation := by
  unfold Syracuse2adic
  rw [dif_neg h]
  exact PadicInt.unitCoeff_spec h

/-- At the degenerate point `3·x + 1 = 0` (i.e. `x = -1/3` in `ℤ_[2]`),
the convention is `Syracuse2adic x = 0`. This case is documented in
the file header and never arises for inputs of interest. -/
@[simp] theorem Syracuse2adic_at_singular (x : ℤ_[2])
    (h : (3 : ℤ_[2]) * x + 1 = 0) : Syracuse2adic x = 0 := by
  unfold Syracuse2adic
  rw [dif_pos h]

/-!
## Bridge with the natural-number Syracuse map

For positive odd naturals, `Syracuse2adic` of the natural cast equals
the natural cast of `S` (defined in `Basic.lean`). This is the
operational compatibility statement that lets us mix
`((S^[j] n : ℕ) : ℤ_[2])` and `Syracuse2adic^[j] (n : ℤ_[2])` freely
inside the proof of Lemma 3.1.

The proof uses `unitCoeff_spec` and the matching
`PadicInt.valuation`-vs-`padicValNat` identity for natural casts.
-/

/-- The natural cast `(n : ℤ_[2])` of a positive natural number is
non-zero, since `ℤ_[2]` has characteristic zero. -/
private theorem natCast_ne_zero_z2 (n : ℕ) (hn : 0 < n) :
    ((n : ℕ) : ℤ_[2]) ≠ 0 := by
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  exact_mod_cast hne

/-- The valuation of a positive natural number cast into `ℤ_[2]`
equals its `padicValNat`. Routes through `ℚ_[2]`. -/
theorem valuation_natCast_z2 (n : ℕ) (_hn : 0 < n) :
    ((n : ℕ) : ℤ_[2]).valuation = padicValNat 2 n := by
  have h1 : (((n : ℕ) : ℤ_[2]) : ℚ_[2]).valuation = padicValNat 2 n := by
    have hcast : (((n : ℕ) : ℤ_[2]) : ℚ_[2]) = ((n : ℕ) : ℚ_[2]) := by push_cast; rfl
    rw [hcast, Padic.valuation_natCast]
  rw [PadicInt.valuation_coe] at h1
  exact_mod_cast h1

/--
**Bridge.** For a positive odd natural `n`, the 2-adic Syracuse step
of `(n : ℤ_[2])` agrees with the natural cast of the integer-valued
Syracuse step `S n`. Connects the paper-faithful 2-adic formulation
with the operational `ℕ`-level dynamics.

Strategy: in `ℕ`, `3n+1 = S(n) · 2^{padicValNat 2 (3n+1)}` exactly
(Nat.div_mul_cancel on the canonical 2-power divisor). In `ℤ_[2]`,
`3·x+1 = unitCoeff · 2^{valuation}` (Mathlib's `unitCoeff_spec`).
The two `2^k` factors are equal, so cancelling gives the desired
equality between `S n` and `unitCoeff = Syracuse2adic`.
-/
theorem Syracuse2adic_natCast (n : ℕ) (h_pos : 0 < n) (_h_odd : Odd n) :
    ((S n : ℕ) : ℤ_[2]) = Syracuse2adic ((n : ℕ) : ℤ_[2]) := by
  -- Abbreviations
  have hy_pos : 0 < 3 * n + 1 := by omega
  have hy_ne_z2 : ((3 * n + 1 : ℕ) : ℤ_[2]) ≠ 0 := natCast_ne_zero_z2 _ hy_pos
  -- ℕ-side: 3n+1 = S(n) · 2^padicValNat
  have hy_eq_nat : 3 * n + 1 = S n * 2 ^ padicValNat 2 (3 * n + 1) := by
    conv_rhs =>
      rw [show S n = (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1) from rfl]
    exact (Nat.div_mul_cancel pow_padicValNat_dvd).symm
  -- Bridge `3·x + 1` to ℕ-cast
  have h3xy : (3 : ℤ_[2]) * ((n : ℕ) : ℤ_[2]) + 1 = ((3 * n + 1 : ℕ) : ℤ_[2]) := by
    push_cast; ring
  have h3x_ne : (3 : ℤ_[2]) * ((n : ℕ) : ℤ_[2]) + 1 ≠ 0 := h3xy ▸ hy_ne_z2
  -- Unfold Syracuse2adic
  unfold Syracuse2adic
  rw [dif_neg h3x_ne]
  -- Goal: ((S n : ℕ) : ℤ_[2]) = ↑(PadicInt.unitCoeff h3x_ne)
  -- Cancellation strategy: both sides times 2^k coincide with (3n+1).
  set k : ℕ := padicValNat 2 (3 * n + 1) with hk_def
  have hval : ((3 : ℤ_[2]) * ((n : ℕ) : ℤ_[2]) + 1).valuation = k := by
    rw [h3xy, valuation_natCast_z2 (3 * n + 1) hy_pos]
  have hpow_ne : ((2 : ℤ_[2]) ^ k) ≠ 0 :=
    pow_ne_zero _ (by
      have : (2 : ℕ) ≠ 0 := by decide
      exact_mod_cast this)
  -- LHS · 2^k = 3n+1 in ℤ_[2]
  have hLHS : ((S n : ℕ) : ℤ_[2]) * (2 : ℤ_[2]) ^ k
            = (3 : ℤ_[2]) * ((n : ℕ) : ℤ_[2]) + 1 := by
    rw [h3xy]
    have hcast := congrArg (fun m : ℕ => ((m : ℕ) : ℤ_[2])) hy_eq_nat
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcast
    exact hcast.symm
  -- RHS · 2^k = 3n+1 in ℤ_[2] via unitCoeff_spec
  have hRHS : (PadicInt.unitCoeff h3x_ne : ℤ_[2]) * (2 : ℤ_[2]) ^ k
            = (3 : ℤ_[2]) * ((n : ℕ) : ℤ_[2]) + 1 := by
    have hspec := PadicInt.unitCoeff_spec h3x_ne
    rw [hval] at hspec
    exact hspec.symm
  exact mul_right_cancel₀ hpow_ne (hLHS.trans hRHS.symm)

end CollatzShadowing
