/-
Phantom-word definitions for the Lean formalization of the Collatz
shadowing lemma.

This file starts the second half of Phase 2 of `TODO.md`: the data type
`PhantomWord` that names a finite Syracuse `ν₂`-word
`w = (a_0, ..., a_{L-1})`. Subsequent tasks (2.5–2.8) will add the
affine map `S_w`, the constants `C_w`/`A_w`, the rational fixed point
`q_w`, and the periodic partial sums `B_m` on top of this scaffolding.

Author: AI-assisted (Claude) + Piero Borgatta. Date: 2026-05-04.
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import CollatzShadowing.Basic

namespace CollatzShadowing

/-!
## Phantom words

Paper Section 3, "Phantom words and their rational fixed points":

```text
w = (a_0, a_1, ..., a_{L-1}) ∈ ℕ^L,   A(w) := Σ a_i.
```

The paper requires the word to be nonempty (length `L ≥ 1`) and each
entry to be a positive natural (each `a_i` is the `ν₂` exponent of some
`3·n + 1`, hence `a_i ≥ 1`). We carry both constraints as structure
fields so that downstream definitions can use them without re-proving.
-/

/--
A **phantom word** is a finite, nonempty sequence of positive natural
numbers, intended to represent the `ν₂` word `(a_0, ..., a_{L-1})` of
one period of an expansive Syracuse cycle.

Paper Section 3.
-/
structure PhantomWord where
  /-- The underlying list of `ν₂` exponents. -/
  vals : List ℕ
  /-- Phantom words have at least one Syracuse step. -/
  nonempty : vals ≠ []
  /-- Each `a_i` is the `ν₂` of some `3·n+1`, hence positive. -/
  positive : ∀ a ∈ vals, 0 < a

namespace PhantomWord

/-- Period length `L = |w|`. -/
def length (w : PhantomWord) : ℕ :=
  w.vals.length

/--
Total exponent of one period, `A(w) := Σ_{i=0}^{L-1} a_i`.

Paper Section 3. This is the running exponent in the affine form
`S_w(n) = (3^L n + C_w) / 2^A`.
-/
def A (w : PhantomWord) : ℕ :=
  w.vals.sum

end PhantomWord

/-!
## Affine coefficients of `S_w` (paper eq. (3.1))

Composing `L` Syracuse steps with `ν₂`-word `(a_0, ..., a_{L-1})` gives
the affine map

```text
S_w(n) = (3^L · n + C_w) / 2^A_w,
```

where `C_w` and `A_w := A(w)` satisfy the recursion

```text
C_0 = 0,           A_0 = 0,
C_{j+1} = 3·C_j + 2^{A_j},
A_{j+1} = A_j + a_j.
```

We capture this recursion as a left fold over `w.vals` of the
state pair `(C_j, A_j)`. The right component of the final state equals
`PhantomWord.A` (the running sum of the word).
-/

/--
Single step of the `(C_j, A_j)` recursion of paper eq. (3.1).

Given the current pair `(C_j, A_j)` and the next word entry `a_j`,
returns `(C_{j+1}, A_{j+1}) = (3·C_j + 2^{A_j}, A_j + a_j)`.
-/
def affineFoldStep (state : ℕ × ℕ) (a : ℕ) : ℕ × ℕ :=
  (3 * state.1 + 2 ^ state.2, state.2 + a)

namespace PhantomWord

/--
Affine coefficients `(C_w, A_w)` obtained by folding `affineFoldStep`
over `w.vals` starting from `(0, 0)`.

Paper eq. (3.1).
-/
def affineCoeffs (w : PhantomWord) : ℕ × ℕ :=
  w.vals.foldl affineFoldStep (0, 0)

/-- The numerator constant `C_w` of paper eq. (3.1). -/
def Cw (w : PhantomWord) : ℕ :=
  (affineCoeffs w).1

/--
The exponent `A_w` of paper eq. (3.1). By construction this equals
`PhantomWord.A`, the running sum of `w.vals`; the equality is recorded
below as `Aw_eq_A`.
-/
def Aw (w : PhantomWord) : ℕ :=
  (affineCoeffs w).2

/-- Folding `affineFoldStep` only adds `a` to the second component, so
the running second coordinate of `affineCoeffs` is the partial sum of
the word. This packages the fact for arbitrary starting state. -/
private theorem affineFold_snd_eq (l : List ℕ) (s : ℕ × ℕ) :
    (l.foldl affineFoldStep s).2 = s.2 + l.sum := by
  induction l generalizing s with
  | nil => simp
  | cons a t ih =>
      simp [List.foldl, affineFoldStep, ih, Nat.add_assoc]

/-- The fold-based exponent equals the direct list sum: `A_w = A(w)`. -/
theorem Aw_eq_A (w : PhantomWord) : w.Aw = w.A := by
  unfold Aw affineCoeffs A
  simpa using affineFold_snd_eq w.vals (0, 0)

/-!
## Periodic extension and partial sums

For the Lemma 3.1 statement we need to talk about the `j`-th entry of
the periodic word `w^∞ = (a_0, a_1, …, a_{L-1}, a_0, a_1, …)` and its
running partial sum `B_m = Σ_{i=0}^{m-1} a_{i mod L}` (paper Section 3,
just before Lemma 3.1).
-/

/-- The `j`-th entry of the periodic extension `w^∞`, given by indexing
into `w.vals` with `j mod L`. Out-of-bounds is impossible for an actual
`PhantomWord` since `L ≥ 1`; the explicit `0` default keeps the
function total without a side-condition. -/
def aAt (w : PhantomWord) (j : ℕ) : ℕ :=
  w.vals.getD (j % w.length) 0

/-- Periodic partial sum `B_m := Σ_{i=0}^{m-1} a_{i mod L}` (paper
Section 3), expressed literally as the sum of the first `m` entries of
the periodic word. The closed form
`(m / L) · A + sum (take (m mod L) w.vals)` is recoverable as a separate
theorem when needed; the sum form makes the induction lemma `B_succ`
(used by Lemma 3.1) trivial. -/
def B (w : PhantomWord) (m : ℕ) : ℕ :=
  ((List.range m).map w.aAt).sum

@[simp] theorem B_zero (w : PhantomWord) : w.B 0 = 0 := by
  simp [B]

/-- Every phantom word has positive length. -/
theorem length_pos (w : PhantomWord) : 0 < w.length := by
  rcases hvals : w.vals with _ | ⟨a, t⟩
  · exact absurd hvals w.nonempty
  · simp [length, hvals]

/-- Each entry of the periodic extension is positive. -/
theorem aAt_pos (w : PhantomWord) (j : ℕ) : 0 < w.aAt j := by
  unfold aAt
  have hlt : j % w.length < w.vals.length := Nat.mod_lt j w.length_pos
  rw [List.getD_eq_getElem _ _ hlt]
  exact w.positive _ (List.getElem_mem _)

/-- The cyclic shift of a phantom word by `r` positions, represented by
one full block of the periodic extension starting at `r`. -/
def cyclicShift (w : PhantomWord) (r : ℕ) : PhantomWord where
  vals := (List.range w.length).map (fun i : ℕ => w.aAt (r + i))
  nonempty := by
    intro h
    have hlen := congrArg List.length h
    simp [w.length_pos.ne'] at hlen
  positive := by
    intro a ha
    rw [List.mem_map] at ha
    rcases ha with ⟨i, _hi, rfl⟩
    exact w.aAt_pos (r + i)

@[simp] theorem cyclicShift_length (w : PhantomWord) (r : ℕ) :
    (w.cyclicShift r).length = w.length := by
  simp [cyclicShift, length]

end PhantomWord

/-!
## Affine Syracuse map `S_w`

The map `S_w(x) := (3^L · x + C_w) / 2^A_w` lands in `ℚ_[2]`, not in
`ℤ_[2]`, because `2` is not a unit in `ℤ_[2]`. The Open-Gaps note in
`INVENTORY.md` recommends exactly this typing: keep affine maps in
`ℚ_[2]`, and reserve `ℤ_[2]` for the residue/congruence statements.

For the phantom orbit (when `x = q_w`) the value is in fact a `ℤ_[2]`
integer, but proving that is part of Phase 3.
-/

open PhantomWord in
/--
The affine Syracuse map of one full period of the phantom word `w`,
acting on a `2`-adic integer and returning a `2`-adic rational.

Paper Section 3, equation (3.1):
```text
S_w(x) = (3^L · x + C_w) / 2^A_w.
```
-/
noncomputable def S_w (w : PhantomWord) (x : ℤ_[2]) : ℚ_[2] :=
  ((3 : ℚ_[2]) ^ w.length * (x : ℚ_[2]) + (Cw w : ℚ_[2]))
    / ((2 : ℚ_[2]) ^ Aw w)

/-!
## Rational and `2`-adic fixed points `q_w`

Paper eq. (3.2):
```text
q_w = C_w / (2^A_w - 3^L).
```
Computed in `ℚ` so that the (signed) subtraction makes sense; `ℕ`
truncated subtraction would be wrong for expansive phantoms where
`3^L > 2^A_w`. The lifting to `ℤ_[2]` requires the rational to have
odd denominator, which is true for any nontrivial phantom (since
`2^A_w - 3^L` is odd) but proving it in normalised `ℚ.den` form is
deferred to Phase 3 — see `qwRat_den_odd` placeholder below.
-/

namespace PhantomWord

/-- Rational fixed point of `S_w` (paper eq. (3.2)). For the canonical
expansive phantom `[1]` this evaluates to `-1`. -/
noncomputable def qwRat (w : PhantomWord) : ℚ :=
  (Cw w : ℚ) / ((2 : ℚ) ^ Aw w - (3 : ℚ) ^ w.length)

/-- Hypothesis that `q_w`, in lowest terms, has odd denominator. This
is the hypothesis needed to lift `q_w` into `ℤ_[2]` via
`Padic.norm_rat_le_one`. For expansive phantoms with `length ≥ 1` this
holds; the proof is deferred to Phase 3. -/
def QwOddDen (w : PhantomWord) : Prop :=
  ¬ (2 : ℕ) ∣ (qwRat w).den

end PhantomWord

/-- The `2`-adic representative `q_w ∈ ℤ_[2]` of the phantom word `w`,
parameterised by the proof that `q_w` has odd denominator. The
construction is `Padic.norm_rat_le_one`, the standard inclusion of an
odd-denominator rational into `ℤ_[2]`. -/
noncomputable def qwZ2 (w : PhantomWord) (h : PhantomWord.QwOddDen w) : ℤ_[2] :=
  ⟨((PhantomWord.qwRat w : ℚ) : ℚ_[2]), Padic.norm_rat_le_one h⟩

/-!
## Smoke checks
-/

/-- The single-step phantom word `[1]`, the simplest expansive cycle
sanity check. -/
def phantomOne : PhantomWord where
  vals := [1]
  nonempty := by decide
  positive := by
    intro a ha
    rcases List.mem_singleton.mp ha with rfl
    decide

example : phantomOne.length = 1 := rfl
example : phantomOne.A = 1 := rfl

-- Paper eq. (3.1) hand-computed for `w = [1]`:
--   (C_0, A_0) = (0, 0);
--   (C_1, A_1) = (3·0 + 2^0, 0 + 1) = (1, 1).
example : PhantomWord.Cw phantomOne = 1 := rfl
example : PhantomWord.Aw phantomOne = 1 := rfl

/--
For the length-1 phantom `[1]`, the affine map collapses to the usual
single-step Syracuse formula `(3·x + 1) / 2` inside `ℚ_[2]`. This is
the algebraic version of the acceptance criterion in Task 2.5; the
identification with the natural-number iterate `S` on odd inputs is
left to a later phase (it requires `ν₂(3n+1) = 1` and a Padic cast).
-/
example (x : ℤ_[2]) :
    S_w phantomOne x = ((3 : ℚ_[2]) * (x : ℚ_[2]) + 1) / 2 := by
  unfold S_w
  simp [PhantomWord.length, PhantomWord.Cw, PhantomWord.Aw,
        PhantomWord.affineCoeffs, affineFoldStep, phantomOne]

-- B and aAt sanity checks for the constant-1 phantom word.
example (m : ℕ) : phantomOne.B m = m := by
  induction m with
  | zero => simp [PhantomWord.B]
  | succ n ih =>
    change ((List.range (n + 1)).map phantomOne.aAt).sum = n + 1
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton]
    have hi : ((List.range n).map phantomOne.aAt).sum = n := ih
    have ha : phantomOne.aAt n = 1 := by
      change ([1] : List ℕ).getD (n % 1) 0 = 1
      rw [Nat.mod_one]; rfl
    rw [hi, ha]
example (j : ℕ) : phantomOne.aAt j = 1 := by
  change ([1] : List ℕ).getD (j % 1) 0 = 1
  rw [Nat.mod_one]
  rfl

-- q_{[1]} = -1: the unique negative fixed point of S, with ν₂-word [1].
example : PhantomWord.qwRat phantomOne = -1 := by
  change (1 : ℚ) / ((2 : ℚ) ^ 1 - (3 : ℚ) ^ 1) = -1
  norm_num

end CollatzShadowing
