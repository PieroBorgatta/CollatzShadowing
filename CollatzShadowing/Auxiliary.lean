/-
Auxiliary lemmas for the proof of Lemma 3.1 (Phase 3 of `TODO.md`).

These lemmas correspond, one-to-one, to Phase 3 tasks 3.1, 3.1.5, 3.3,
and 3.4. Task 3.2 (the affine-difference identity) requires extending
the Syracuse map to `ℤ_[2]`, so it lives in a separate Phase 3
follow-up.

Author: AI-assisted (Claude) + Piero Borgatta. Date: 2026-05-04.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Rotate
import Mathlib.Logic.Function.Iterate
import CollatzShadowing.Phantom
import CollatzShadowing.Syracuse2Adic

namespace CollatzShadowing

/-!
## Task 3.4 — `B_m + 1 - B_j ≥ a_j + 1 ↔ B_m ≥ B_{j+1}`

This is purely arithmetical: by the recursion of `B`, the partial sum
satisfies `B (j+1) = B j + a_j`, so the equivalence reduces to
`B_m ≥ B_j + a_j ↔ B_m + 1 ≥ B_j + a_j + 1`, which is `omega`.
-/

namespace PhantomWord

/-- Recursive characterisation of `B` along the periodic word. With
`B` defined as the sum-form `((range m).map aAt).sum`, this is just
`List.range_succ` plus the singleton-sum simplification. -/
theorem B_succ (w : PhantomWord) (j : ℕ) :
    w.B (j + 1) = w.B j + w.aAt j := by
  change ((List.range (j + 1)).map w.aAt).sum = ((List.range j).map w.aAt).sum + w.aAt j
  rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton]

/-- **Task 3.4.** The bound `B_m + 1 - B_j ≥ a_j + 1` is equivalent to
`B_m ≥ B (j+1)`. -/
theorem B_bound_iff (w : PhantomWord) (j m : ℕ) :
    (w.aAt j + 1 ≤ w.B m + 1 - w.B j) ↔ (w.B (j + 1) ≤ w.B m) := by
  rw [B_succ]
  omega

end PhantomWord

/-!
## Task 3.1 — `ν₂(3 · n) = ν₂(n)` in `ℤ_[2]`

Since `3` is a unit in `ℤ_[2]` (its `2`-adic norm is `1`), multiplication
by `3` preserves the valuation. Mathlib gives this through
`PadicInt.valuation_mul` once we know `(3 : ℤ_[2]).valuation = 0`.
-/

/-- `(3 : ℤ_[2])` is non-zero. The `decide` tactic does not work on
`ℤ_[2]` (it lacks decidable equality), so we route through a `Nat`
cast injectivity argument. -/
theorem three_ne_zero_z2 : (3 : ℤ_[2]) ≠ 0 := by
  exact_mod_cast (by decide : (3 : ℕ) ≠ 0)

/-- `(3 : ℤ_[2])` has trivial `2`-adic valuation: `3` is not divisible
by `2`. There is no `PadicInt.valuation_natCast` in Mathlib v4.29.1, so
we route through `ℚ_[2]` via the `valuation_coe` simp lemma and the
existing `Padic.valuation_natCast`. -/
theorem valuation_three_z2 : (3 : ℤ_[2]).valuation = 0 := by
  have h1 : ((3 : ℤ_[2]) : ℚ_[2]).valuation = 0 := by
    have hcast : ((3 : ℤ_[2]) : ℚ_[2]) = ((3 : ℕ) : ℚ_[2]) := by push_cast; rfl
    rw [hcast, Padic.valuation_natCast]
    have h3 : padicValNat 2 3 = 0 :=
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ (2 : ℕ) ∣ 3)
    exact_mod_cast h3
  -- `PadicInt.valuation_coe` gives `(x : ℚ_[p]).valuation = (x.valuation : ℤ)`.
  rw [PadicInt.valuation_coe] at h1
  exact_mod_cast h1

/-- `(2 : ℤ_[2])` is non-zero. -/
theorem two_ne_zero_z2 : (2 : ℤ_[2]) ≠ 0 := by
  exact_mod_cast (by decide : (2 : ℕ) ≠ 0)

/-- `(2 : ℤ_[2]).valuation = 1`. -/
theorem valuation_two_z2 : (2 : ℤ_[2]).valuation = 1 := by
  have h : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by push_cast; rfl
  rw [h]
  exact PadicInt.valuation_p

/-- `((2 : ℤ_[2]) ^ k).valuation = k`. -/
theorem valuation_two_pow_z2 (k : ℕ) : ((2 : ℤ_[2]) ^ k).valuation = k := by
  rw [PadicInt.valuation_pow, valuation_two_z2, mul_one]

/-- **Task 3.1.** Multiplication by `3` is `ν₂`-invariant on `ℤ_[2]`. -/
theorem nu2Z2_three_mul (n : ℤ_[2]) : nu2Z2 (3 * n) = nu2Z2 n := by
  by_cases hn : n = 0
  · simp [hn, nu2Z2]
  · unfold nu2Z2
    rw [PadicInt.valuation_mul three_ne_zero_z2 hn, valuation_three_z2, zero_add]

/-!
## Task 3.1.5 — `QwOddDen` for every phantom

Strategy: lift the rational `qwRat w = Cw / (2^A_w − 3^L)` to its
integer-valued form `Rat.divInt (Cw : ℤ) qwIntDen`, where
`qwIntDen w := (2 : ℤ)^A_w − (3 : ℤ)^L` is non-zero and has odd
absolute value. Then:

* `Rat.den_dvd` gives `((divInt …).den : ℤ) ∣ qwIntDen`.
* `Int.natCast_dvd` converts to `(divInt …).den ∣ qwIntDen.natAbs`.
* `Odd.of_dvd_nat` then gives `Odd (divInt …).den`.
* Odd implies `¬ 2 ∣ den`.
-/

namespace PhantomWord

/-- A phantom word's exponent sum is at least its length: each entry is
≥ 1, hence the sum is ≥ length · 1. -/
theorem length_le_A (w : PhantomWord) : w.length ≤ w.A := by
  exact List.length_le_sum_of_one_le w.vals (fun a ha => w.positive a ha)

/-- `A_w ≥ 1` for any phantom word. -/
theorem one_le_Aw (w : PhantomWord) : 1 ≤ w.Aw := by
  rw [Aw_eq_A]
  have hL : 1 ≤ w.length := by
    rcases hvals : w.vals with _ | ⟨a, t⟩
    · exact absurd hvals w.nonempty
    · simp [PhantomWord.length, hvals]
  exact le_trans hL w.length_le_A

/-- The integer denominator `2^A_w − 3^L`. -/
def qwIntDen (w : PhantomWord) : ℤ :=
  (2 : ℤ) ^ w.Aw - (3 : ℤ) ^ w.length

/-- The integer denominator is odd: `2^A_w` is even (since `A_w ≥ 1`)
and `3^L` is odd, so their difference is odd. -/
theorem qwIntDen_odd (w : PhantomWord) : Odd (qwIntDen w) := by
  unfold qwIntDen
  apply Even.sub_odd
  · -- Even ((2 : ℤ)^Aw): since Aw ≥ 1, 2 ∣ 2^Aw
    rw [even_iff_two_dvd]
    exact dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp w.one_le_Aw)
  · -- Odd ((3 : ℤ)^L): 3 is odd, hence 3^L is odd
    exact Odd.pow ⟨1, by ring⟩

/-- `qwRat w` written as a `Rat.divInt` of two integers. -/
theorem qwRat_eq_divInt (w : PhantomWord) :
    qwRat w = Rat.divInt (Cw w : ℤ) (qwIntDen w) := by
  unfold qwRat qwIntDen
  rw [Rat.divInt_eq_div]
  push_cast
  ring

/-- **Task 3.1.5.** The rational fixed point `q_w` of any phantom word
has odd denominator. Consequently `qwZ2 w` can be applied unconditionally
once we discharge the hypothesis with this theorem. -/
theorem qwOddDen (w : PhantomWord) : QwOddDen w := by
  unfold QwOddDen
  rw [qwRat_eq_divInt]
  -- Step 1: (den : ℤ) ∣ qwIntDen.
  have hdvdInt : ((Rat.divInt (Cw w : ℤ) (qwIntDen w)).den : ℤ) ∣ (qwIntDen w) :=
    Rat.den_dvd _ _
  -- Step 2: convert to ℕ-divisibility on natAbs.
  rw [Int.natCast_dvd] at hdvdInt
  -- hdvdInt : (Rat.divInt _ _).den ∣ (qwIntDen w).natAbs.
  -- Step 3: qwIntDen.natAbs is odd.
  have hodd_nat : Odd (qwIntDen w).natAbs := Odd.natAbs (qwIntDen_odd w)
  -- Step 4: divisor of odd is odd.
  have hden_odd : Odd (Rat.divInt (Cw w : ℤ) (qwIntDen w)).den :=
    Odd.of_dvd_nat hodd_nat hdvdInt
  -- Step 5: odd ⟹ ¬ 2 ∣.
  intro h2dvd
  have hmod0 : (Rat.divInt (Cw w : ℤ) (qwIntDen w)).den % 2 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp h2dvd
  have hmod1 : (Rat.divInt (Cw w : ℤ) (qwIntDen w)).den % 2 = 1 :=
    Nat.odd_iff.mp hden_odd
  omega

end PhantomWord

/-!
## Helpers for Tasks 3.2 and 3.3
-/

/-- The 2-adic valuation alias `ν₂Z2 = nu2Z2` agrees with the underlying
`PadicInt.valuation`, in particular `ν₂Z2 0 = 0`. -/
private theorem nu2Z2_zero : ν₂Z2 (0 : ℤ_[2]) = 0 := by
  unfold ν₂Z2 nu2Z2
  exact PadicInt.valuation_zero

/-- If an element is a 2-power times a 2-adic unit, its `ν₂` is exactly
that exponent. -/
theorem nu2Z2_eq_of_eq_unit_mul_two_pow
    {z u : ℤ_[2]} {a : ℕ}
    (hz : z = u * (2 : ℤ_[2]) ^ a)
    (hu_ne : u ≠ 0)
    (hu_val : u.valuation = 0) :
    ν₂Z2 z = a := by
  have hpow_ne : (2 : ℤ_[2]) ^ a ≠ 0 := pow_ne_zero _ two_ne_zero_z2
  have hz_ne : z ≠ 0 := by
    rw [hz]
    exact mul_ne_zero hu_ne hpow_ne
  unfold ν₂Z2 nu2Z2
  rw [hz, PadicInt.valuation_mul hu_ne hpow_ne, valuation_two_pow_z2, hu_val, zero_add]

/-- If the `i`-th step matches the prescribed positive `aAt w i`, then
the relevant `3·x + 1` cannot be zero. -/
private theorem ne_zero_of_matches (w : PhantomWord) (x : ℤ_[2]) (i : ℕ)
    (h : ν₂Z2 ((3 : ℤ_[2]) * Syracuse2adic^[i] x + 1) = w.aAt i) :
    (3 : ℤ_[2]) * Syracuse2adic^[i] x + 1 ≠ 0 := by
  intro hz
  rw [hz, nu2Z2_zero] at h
  -- h : 0 = w.aAt i, but aAt is positive
  have := w.aAt_pos i
  omega

/-!
## Task 3.2 — Affine difference identity (paper line 276)

After the first `j` Syracuse steps of `n` and `q_w` follow the same
prescribed word `(a_0, ..., a_{j-1})`, the difference of the iterates
in `ℚ_[2]` is

```text
S^j(n) - S^j(q_w) = (3^j / 2^{B_j}) · (n - q_w).
```

The identity lives in `ℚ_[2]` because the `2^{B_j}` denominator is not
invertible in `ℤ_[2]`. Proof deferred (induction on `j` using the
unitCoeff representation of one `Syracuse2adic` step).
-/

/-- Hypothesis that the first `j` Syracuse steps of `x` follow the
phantom word `w`. -/
def MatchesPrefix (w : PhantomWord) (x : ℤ_[2]) (j : ℕ) : Prop :=
  ∀ i, i < j → ν₂Z2 ((3 : ℤ_[2]) * Syracuse2adic^[i] x + 1) = w.aAt i

/-- One Syracuse2adic step transforms the difference of two inputs by
the factor `3 / 2^a`, where `a` is the common 2-adic valuation of
`3·x + 1` and `3·y + 1`. -/
private theorem syracuse_one_step_diff (x y : ℤ_[2])
    (hx : (3 : ℤ_[2]) * x + 1 ≠ 0)
    (hy : (3 : ℤ_[2]) * y + 1 ≠ 0)
    (hval_eq : ((3 : ℤ_[2]) * x + 1).valuation = ((3 : ℤ_[2]) * y + 1).valuation) :
    (Syracuse2adic x : ℚ_[2]) - (Syracuse2adic y : ℚ_[2])
      = (3 : ℚ_[2]) / (2 : ℚ_[2]) ^ ((3 : ℤ_[2]) * x + 1).valuation
        * ((x : ℚ_[2]) - (y : ℚ_[2])) := by
  -- Cast spec to ℚ_[2] for both x and y.
  have sxQ : (3 : ℚ_[2]) * (x : ℚ_[2]) + 1
           = (Syracuse2adic x : ℚ_[2])
              * (2 : ℚ_[2]) ^ ((3 : ℤ_[2]) * x + 1).valuation := by
    have h := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) (Syracuse2adic_spec x hx)
    push_cast at h
    convert h using 2
  have syQ : (3 : ℚ_[2]) * (y : ℚ_[2]) + 1
           = (Syracuse2adic y : ℚ_[2])
              * (2 : ℚ_[2]) ^ ((3 : ℤ_[2]) * y + 1).valuation := by
    have h := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) (Syracuse2adic_spec y hy)
    push_cast at h
    convert h using 2
  -- Combine: same exponent on both via hval_eq.
  rw [hval_eq] at sxQ
  -- 3·(x-y) = (S2 x - S2 y) · 2^v   (subtracting syQ from sxQ in ℚ_[2]).
  have hQ : (3 : ℚ_[2]) * ((x : ℚ_[2]) - (y : ℚ_[2]))
          = ((Syracuse2adic x : ℚ_[2]) - (Syracuse2adic y : ℚ_[2]))
              * (2 : ℚ_[2]) ^ ((3 : ℤ_[2]) * y + 1).valuation := by
    linear_combination sxQ - syQ
  -- Divide both sides by `2^v` (a unit in ℚ_[2]).
  have h2_ne : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have hpow_ne : ((2 : ℚ_[2]) ^ ((3 : ℤ_[2]) * y + 1).valuation) ≠ 0 :=
    pow_ne_zero _ h2_ne
  rw [hval_eq]
  field_simp
  linear_combination -hQ

/--
**Task 3.2.** If `n` and `q_w` follow the same prescribed word for the
first `j` Syracuse steps, then their `j`-th iterates differ by the
affine factor `3^j / 2^{B_j}` times the original difference, in
`ℚ_[2]`. (Paper line 276.)

Proof by induction on `j`. Stated in `ℚ_[2]` because `2^{B_j}` is not
a unit in `ℤ_[2]`.
-/
theorem affine_difference
    (w : PhantomWord) (n : ℤ_[2]) (j : ℕ)
    (h_n : MatchesPrefix w n j)
    (h_qw : MatchesPrefix w (qwZ2 w (PhantomWord.qwOddDen w)) j) :
    (Syracuse2adic^[j] n : ℚ_[2])
        - (Syracuse2adic^[j] (qwZ2 w (PhantomWord.qwOddDen w)) : ℚ_[2])
      = ((3 : ℚ_[2]) ^ j) / ((2 : ℚ_[2]) ^ w.B j)
          * ((n : ℚ_[2]) - (qwZ2 w (PhantomWord.qwOddDen w) : ℚ_[2])) := by
  induction j with
  | zero =>
    simp [Function.iterate_zero, PhantomWord.B_zero]
  | succ k ih =>
    -- IH applies once we drop the (k+1)-th matching constraint.
    have h_n_k : MatchesPrefix w n k := fun i hi => h_n i (Nat.lt_succ_of_lt hi)
    have h_qw_k : MatchesPrefix w (qwZ2 w (PhantomWord.qwOddDen w)) k :=
      fun i hi => h_qw i (Nat.lt_succ_of_lt hi)
    have ih' := ih h_n_k h_qw_k
    -- Set abbreviations for readability.
    set q : ℤ_[2] := qwZ2 w (PhantomWord.qwOddDen w) with hq
    set xn : ℤ_[2] := Syracuse2adic^[k] n with hxn
    set xq : ℤ_[2] := Syracuse2adic^[k] q with hxq
    -- Use the matching hypothesis at step k for both n and q.
    -- Note: `ν₂Z2 = .valuation` by def, so these proofs serve both forms.
    have h_match_n_ν : ν₂Z2 ((3 : ℤ_[2]) * xn + 1) = w.aAt k := h_n k (Nat.lt_succ_self k)
    have h_match_q_ν : ν₂Z2 ((3 : ℤ_[2]) * xq + 1) = w.aAt k := h_qw k (Nat.lt_succ_self k)
    have h_match_n : ((3 : ℤ_[2]) * xn + 1).valuation = w.aAt k := h_match_n_ν
    have h_match_q : ((3 : ℤ_[2]) * xq + 1).valuation = w.aAt k := h_match_q_ν
    have h_xn_ne : (3 : ℤ_[2]) * xn + 1 ≠ 0 := by
      have := ne_zero_of_matches w n k h_match_n_ν
      simpa [hxn] using this
    have h_xq_ne : (3 : ℤ_[2]) * xq + 1 ≠ 0 := by
      have := ne_zero_of_matches w q k h_match_q_ν
      simpa [hxq] using this
    have h_val_eq : ((3 : ℤ_[2]) * xn + 1).valuation = ((3 : ℤ_[2]) * xq + 1).valuation := by
      rw [h_match_n, h_match_q]
    -- One-step difference formula at k.
    have step := syracuse_one_step_diff xn xq h_xn_ne h_xq_ne h_val_eq
    -- Iterates at k+1.
    have h_iter : Syracuse2adic^[k+1] n = Syracuse2adic xn := by
      rw [Function.iterate_succ', Function.comp_apply]
    have h_iter_q : Syracuse2adic^[k+1] q = Syracuse2adic xq := by
      rw [Function.iterate_succ', Function.comp_apply]
    rw [h_iter, h_iter_q, step, h_match_n, w.B_succ k]
    rw [ih']
    -- Algebraic simplification in ℚ_[2].
    have h2_ne : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
    have hpow_Bk : ((2 : ℚ_[2]) ^ w.B k) ≠ 0 := pow_ne_zero _ h2_ne
    have hpow_aAt : ((2 : ℚ_[2]) ^ w.aAt k) ≠ 0 := pow_ne_zero _ h2_ne
    field_simp
    ring

/-!
## Phase-4 helpers: monotonicity of `B` and ℤ_[2]-valued affine difference
-/

namespace PhantomWord

/-- The periodic partial sum `B` is monotonically non-decreasing. -/
theorem B_mono (w : PhantomWord) {j k : ℕ} (h : j ≤ k) : w.B j ≤ w.B k := by
  induction k, h using Nat.le_induction with
  | base => exact le_refl _
  | succ k _ ih =>
    rw [B_succ]
    have := w.aAt_pos k
    omega

/-- The periodic partial sum is positive on every non-empty prefix. -/
theorem B_pos_of_pos (w : PhantomWord) {j : ℕ} (hj : 0 < j) : 0 < w.B j := by
  unfold B
  apply List.sum_pos
  · intro a ha
    rw [List.mem_map] at ha
    rcases ha with ⟨i, _hi, rfl⟩
    exact w.aAt_pos i
  · intro hnil
    have hrange_nil : List.range j = [] := by
      simpa using congrArg List.length hnil
    rw [List.range_eq_nil] at hrange_nil
    omega

/-- Periodicity of the entries of `w^∞`. -/
theorem aAt_add_length (w : PhantomWord) (j : ℕ) :
    w.aAt (j + w.length) = w.aAt j := by
  unfold aAt
  rw [Nat.add_mod_right]

/-- At the start of a full period, the next `i`-th entry is the `i`-th
entry of the underlying finite word. -/
theorem aAt_mul_length_add_of_lt (w : PhantomWord) (b i : ℕ) (hi : i < w.length) :
    w.aAt (b * w.length + i) = w.vals.getD i 0 := by
  unfold aAt
  have hmod : (b * w.length + i) % w.length = i := by
    rw [Nat.mul_comm b w.length]
    rw [Nat.add_comm]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hi
  rw [hmod]

/-- The periodic entries of a cyclic shift are the corresponding shifted
entries of the original periodic word. -/
theorem cyclicShift_aAt (w : PhantomWord) (r i : ℕ) :
    (w.cyclicShift r).aAt i = w.aAt (r + i) := by
  unfold aAt
  rw [cyclicShift_length]
  unfold cyclicShift
  change ((List.range w.length).map (fun i : ℕ => w.aAt (r + i))).getD (i % w.length) 0 =
    w.vals.getD ((r + i) % w.length) 0
  have hlt : i % w.length < ((List.range w.length).map (fun i : ℕ => w.aAt (r + i))).length := by
    simpa using Nat.mod_lt i w.length_pos
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [List.getElem_map, List.getElem_range]
  unfold aAt
  have hmod : (r + i % w.length) % w.length = (r + i) % w.length := by
    simp [Nat.add_mod]
  rw [hmod]

/-- The list underlying a cyclic shift is Mathlib's `List.rotate` of the
original finite word. -/
theorem cyclicShift_vals_eq_rotate (w : PhantomWord) (r : ℕ) :
    (w.cyclicShift r).vals = w.vals.rotate r := by
  apply List.ext_getElem
  · simp [cyclicShift, length]
  · intro i h₁ h₂
    unfold cyclicShift
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getElem_rotate]
    unfold aAt
    change w.vals.getD ((r + i) % w.vals.length) 0 =
      w.vals[(i + r) % w.vals.length]'(Nat.mod_lt _ (by simpa [length] using w.length_pos))
    rw [List.getD_eq_getElem _ _ (Nat.mod_lt (r + i) w.length_pos)]
    congr 1
    simp [Nat.add_mod, Nat.add_comm]

/-- Cyclic shifts preserve the total exponent sum `A`. -/
theorem cyclicShift_A (w : PhantomWord) (r : ℕ) :
    (w.cyclicShift r).A = w.A := by
  unfold A
  rw [cyclicShift_vals_eq_rotate]
  exact (List.rotate_perm w.vals r).sum_eq

/-- Cyclic shifts preserve the folded exponent `Aw`. -/
theorem cyclicShift_Aw (w : PhantomWord) (r : ℕ) :
    (w.cyclicShift r).Aw = w.Aw := by
  rw [Aw_eq_A, Aw_eq_A, cyclicShift_A]

/-- Extensionality for `PhantomWord`: the proof fields are propositions,
so the underlying list determines the structure. -/
theorem ext_vals {w v : PhantomWord} (h : w.vals = v.vals) : w = v := by
  cases w with
  | mk vals hn hp =>
  cases v with
  | mk vals' hn' hp' =>
      simp only at h
      subst h
      rfl

/-- The zero cyclic shift is the original phantom word. -/
theorem cyclicShift_zero (w : PhantomWord) : w.cyclicShift 0 = w := by
  apply ext_vals
  rw [cyclicShift_vals_eq_rotate]
  simp

/-- A one-step cyclic shift composes with a prior cyclic shift by adding
one to the shift amount. -/
theorem cyclicShift_cyclicShift_one (w : PhantomWord) (r : ℕ) :
    (w.cyclicShift r).cyclicShift 1 = w.cyclicShift (r + 1) := by
  apply ext_vals
  calc
    ((w.cyclicShift r).cyclicShift 1).vals
        = (w.cyclicShift r).vals.rotate 1 := cyclicShift_vals_eq_rotate (w.cyclicShift r) 1
    _ = (w.vals.rotate r).rotate 1 := by rw [cyclicShift_vals_eq_rotate]
    _ = w.vals.rotate (r + 1) := by rw [List.rotate_rotate]
    _ = (w.cyclicShift (r + 1)).vals := (cyclicShift_vals_eq_rotate w (r + 1)).symm

/-- Folding affine coefficients from an arbitrary state: first component. -/
private theorem affineFold_general_fst (l : List ℕ) (s : ℕ × ℕ) :
    (l.foldl affineFoldStep s).1 =
      3 ^ l.length * s.1 + (l.foldl affineFoldStep (0, 0)).1 * 2 ^ s.2 := by
  induction l generalizing s with
  | nil =>
      simp
  | cons a t ih =>
      rw [List.foldl_cons, ih (affineFoldStep s a)]
      change 3 ^ t.length * (affineFoldStep s a).1
            + (List.foldl affineFoldStep (0, 0) t).1 * 2 ^ (affineFoldStep s a).2 =
        3 ^ (a :: t).length * s.1
            + (List.foldl affineFoldStep (affineFoldStep (0, 0) a) t).1 * 2 ^ s.2
      rw [ih (affineFoldStep (0, 0) a)]
      simp [affineFoldStep]
      ring

/-- Folding affine coefficients from an arbitrary state: second component. -/
private theorem affineFold_general_snd (l : List ℕ) (s : ℕ × ℕ) :
    (l.foldl affineFoldStep s).2 = s.2 + (l.foldl affineFoldStep (0, 0)).2 := by
  induction l generalizing s with
  | nil =>
      simp
  | cons a t ih =>
      rw [List.foldl_cons, ih (affineFoldStep s a)]
      change (affineFoldStep s a).2 + (List.foldl affineFoldStep (0, 0) t).2 =
        s.2 + (List.foldl affineFoldStep (affineFoldStep (0, 0) a) t).2
      rw [ih (affineFoldStep (0, 0) a)]
      simp [affineFoldStep]
      omega

set_option linter.flexible false in
/-- Coefficient identity for advancing from a phantom word to its
one-step cyclic shift. This is the algebraic numerator relation behind
`3*q_w + 1 = 2^{a_0} q_{shift(w)}`. -/
theorem Cw_step_cyclicShift_one (w : PhantomWord) :
    (3 : ℤ) * (w.Cw : ℤ) + ((2 : ℤ) ^ w.Aw - (3 : ℤ) ^ w.length) =
      (2 : ℤ) ^ w.aAt 0 * ((w.cyclicShift 1).Cw : ℤ) := by
  rcases hvals : w.vals with _ | ⟨a, t⟩
  · exact absurd hvals w.nonempty
  · unfold Cw Aw affineCoeffs length aAt
    simp [hvals, cyclicShift_vals_eq_rotate, affineFoldStep]
    rw [affineFold_general_fst t (1, a), affineFold_general_snd t (1, a),
      affineFold_general_snd t (0, 0)]
    simp
    rw [pow_add]
    ring

/-- Mapping `getD` over all valid list indices recovers the list. -/
private theorem map_getD_range (l : List ℕ) :
    (List.range l.length).map (fun i : ℕ => l.getD i 0) = l := by
  have hfin : List.finRange l.length = (List.range l.length).pmap Fin.mk (by simp) :=
    List.finRange_eq_pmap_range
  have hget : List.map l.get (List.finRange l.length) = l := List.map_get_finRange l
  rw [hfin, List.map_pmap] at hget
  have hpmap_getD :
      (List.range l.length).pmap (fun i (_ : i < l.length) => l.getD i 0)
          (by simp)
        = (List.range l.length).map (fun i : ℕ => l.getD i 0) := by
    rw [List.pmap_eq_map]
  have hpmap_get :
      (List.range l.length).pmap
          (fun i (hi : i < l.length) => l.get ⟨i, hi⟩)
          (by simp)
        =
      (List.range l.length).pmap (fun i (_ : i < l.length) => l.getD i 0)
          (by simp) := by
    apply List.pmap_congr_left
    intro i _hi hlt _hlt'
    exact (List.getD_eq_getElem l 0 hlt).symm
  rw [hpmap_get, hpmap_getD] at hget
  exact hget

/-- Summing `getD` over all valid list indices recovers the list sum. -/
private theorem sum_getD_range (l : List ℕ) :
    ((List.range l.length).map fun i : ℕ => l.getD i 0).sum = l.sum :=
  congrArg List.sum (map_getD_range l)

/-- Summing `getD` over the first `r` valid indices recovers the sum of
the first `r` entries. -/
private theorem sum_getD_range_take (l : List ℕ) {r : ℕ} (hr : r ≤ l.length) :
    ((List.range r).map fun i : ℕ => l.getD i 0).sum = (l.take r).sum := by
  have hlen : (l.take r).length = r := by
    simp [List.length_take, min_eq_left hr]
  have hmap :
      (List.range r).map (fun i : ℕ => l.getD i 0) =
        (List.range (l.take r).length).map (fun i : ℕ => (l.take r).getD i 0) := by
    rw [hlen]
    apply List.map_congr_left
    intro i hi
    have hi_lt_r : i < r := List.mem_range.mp hi
    have hi_lt_l : i < l.length := lt_of_lt_of_le hi_lt_r hr
    rw [List.getD_eq_getElem _ _ hi_lt_l]
    rw [List.getD_eq_getElem _ _ (by simpa [hlen] using hi_lt_r)]
    simp [List.getElem_take]
  rw [hmap]
  exact sum_getD_range (l.take r)

/-- A complete block of `length` many periodic entries sums to `A`. -/
theorem block_sum_mul_length (w : PhantomWord) (b : ℕ) :
    ((List.range w.length).map fun i : ℕ => w.aAt (b * w.length + i)).sum
      = w.A := by
  unfold A length
  have hlist :
      (List.range w.vals.length).map (fun i : ℕ => w.aAt (b * w.vals.length + i))
        = (List.range w.vals.length).map (fun i : ℕ => w.vals.getD i 0) := by
    apply List.map_congr_left
    intro i hi
    exact aAt_mul_length_add_of_lt w b i (by simpa [length] using List.mem_range.mp hi)
  rw [hlist]
  exact sum_getD_range w.vals

/-- The periodic partial sum over `b` complete periods is `b * A`. -/
theorem B_mul_period (w : PhantomWord) (b : ℕ) :
    w.B (b * w.length) = b * w.A := by
  induction b with
  | zero =>
      simp [B]
  | succ b ih =>
      have hblock :
          w.B (b * w.length + w.length) = w.B (b * w.length) + w.A := by
        unfold B
        rw [List.range_add, List.map_append, List.sum_append]
        congr 1
        rw [← block_sum_mul_length w b]
        simp [Function.comp_def]
      calc
        w.B ((b + 1) * w.length)
            = w.B (b * w.length + w.length) := by
                rw [Nat.succ_mul]
        _ = w.B (b * w.length) + w.A := hblock
        _ = b * w.A + w.A := by rw [ih]
        _ = (b + 1) * w.A := by rw [Nat.succ_mul]

/-- Closed form of the periodic partial sum:
`B_m = (m / L) * A + sum (take (m % L) vals)`. -/
theorem B_closed_form (w : PhantomWord) (m : ℕ) :
    w.B m = (m / w.length) * w.A + (w.vals.take (m % w.length)).sum := by
  let q := m / w.length
  let r := m % w.length
  have hr_lt : r < w.length := Nat.mod_lt m w.length_pos
  have hr_le_vals : r ≤ w.vals.length := by
    simpa [length] using le_of_lt hr_lt
  have hm : m = q * w.length + r := by
    dsimp [q, r]
    exact (Nat.div_add_mod' m w.length).symm
  have hdiv : (q * w.length + r) / w.length = q := by
    calc
      (q * w.length + r) / w.length = (r + w.length * q) / w.length := by
        rw [Nat.add_comm, Nat.mul_comm q w.length]
      _ = r / w.length + q := Nat.add_mul_div_left r q w.length_pos
      _ = q := by rw [Nat.div_eq_of_lt hr_lt, zero_add]
  have hmod : (q * w.length + r) % w.length = r := by
    calc
      (q * w.length + r) % w.length = (r + w.length * q) % w.length := by
        rw [Nat.add_comm, Nat.mul_comm q w.length]
      _ = r % w.length := Nat.add_mul_mod_self_left r w.length q
      _ = r := Nat.mod_eq_of_lt hr_lt
  rw [hm]
  unfold B
  rw [List.range_add, List.map_append, List.sum_append]
  simp only [List.map_map, Function.comp_def]
  have hprefix :
      ((List.range (q * w.length)).map w.aAt).sum = q * w.A := by
    simpa [B] using w.B_mul_period q
  have htail :
      ((List.range r).map fun i : ℕ => w.aAt (q * w.length + i)).sum =
        (w.vals.take r).sum := by
    have hmap :
        (List.range r).map (fun i : ℕ => w.aAt (q * w.length + i)) =
          (List.range r).map (fun i : ℕ => w.vals.getD i 0) := by
      apply List.map_congr_left
      intro i hi
      exact aAt_mul_length_add_of_lt w q i
        (lt_of_lt_of_le (List.mem_range.mp hi) (by simpa [length] using hr_le_vals))
    rw [hmap]
    exact sum_getD_range_take w.vals hr_le_vals
  rw [hprefix, htail, hdiv, hmod]

/-!
## Phase-5 helpers: affine coefficients for prefixes of the periodic word

The full-period coefficients `Cw`/`Aw` are defined by folding over
`w.vals`. For the orbit of `q_w`, we also need the same affine
recursion along the first `j` entries of `w^∞`.
-/

/-- Affine coefficients after the first `j` entries of the periodic word
`w^∞`. The first coordinate is the prefix `C_j`; the second coordinate is
the prefix exponent sum, later identified with `B j`. -/
def prefixCoeffs (w : PhantomWord) (j : ℕ) : ℕ × ℕ :=
  (List.range j).foldl (fun state i => affineFoldStep state (w.aAt i)) (0, 0)

@[simp] theorem prefixCoeffs_zero (w : PhantomWord) :
    w.prefixCoeffs 0 = (0, 0) := by
  simp [prefixCoeffs]

/-- One-step recursion for prefix affine coefficients. -/
theorem prefixCoeffs_succ (w : PhantomWord) (j : ℕ) :
    w.prefixCoeffs (j + 1) = affineFoldStep (w.prefixCoeffs j) (w.aAt j) := by
  unfold prefixCoeffs
  rw [List.range_succ, List.foldl_append]
  simp [affineFoldStep]

/-- The second prefix coefficient is the periodic partial sum `B j`. -/
theorem prefixCoeffs_snd_eq_B (w : PhantomWord) (j : ℕ) :
    (w.prefixCoeffs j).2 = w.B j := by
  induction j with
  | zero =>
      simp [prefixCoeffs, B]
  | succ j ih =>
      rw [prefixCoeffs_succ, B_succ]
      simp [affineFoldStep, ih]

/-- Prefix `C_j` coefficient for the first `j` entries of `w^∞`. -/
def prefixC (w : PhantomWord) (j : ℕ) : ℕ :=
  (w.prefixCoeffs j).1

@[simp] theorem prefixC_zero (w : PhantomWord) : w.prefixC 0 = 0 := by
  simp [prefixC]

/-- Recursion for the prefix numerator coefficient. -/
theorem prefixC_succ (w : PhantomWord) (j : ℕ) :
    w.prefixC (j + 1) = 3 * w.prefixC j + 2 ^ w.B j := by
  unfold prefixC
  rw [prefixCoeffs_succ]
  simp [affineFoldStep, prefixCoeffs_snd_eq_B]

/-- Every non-empty prefix numerator coefficient is odd. -/
theorem prefixC_odd_of_pos (w : PhantomWord) {j : ℕ} (hj : 0 < j) :
    Odd (w.prefixC j) := by
  induction j with
  | zero =>
      omega
  | succ k ih =>
      rw [prefixC_succ]
      by_cases hk : k = 0
      · subst hk
        simp [B_zero]
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
        have hodd_left : Odd (3 * w.prefixC k) :=
          Odd.mul ⟨1, by ring⟩ (ih hk_pos)
        have heven_right : Even (2 ^ w.B k) := by
          rw [even_iff_two_dvd]
          exact dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp (w.B_pos_of_pos hk_pos))
        exact Odd.add_even hodd_left heven_right

/-- The first full block of periodic entries is exactly `w.vals`. -/
theorem map_aAt_range_length (w : PhantomWord) :
    (List.range w.length).map w.aAt = w.vals := by
  unfold length
  have hlist :
      (List.range w.vals.length).map (fun i : ℕ => w.aAt i)
        = (List.range w.vals.length).map (fun i : ℕ => w.vals.getD i 0) := by
    apply List.map_congr_left
    intro i hi
    have hlt : i < w.length := by simpa [length] using List.mem_range.mp hi
    simpa using aAt_mul_length_add_of_lt w 0 i hlt
  rw [hlist]
  exact map_getD_range w.vals

/-- Prefix coefficients over one full period recover the original
full-period affine coefficients. -/
theorem prefixCoeffs_length_eq_affineCoeffs (w : PhantomWord) :
    w.prefixCoeffs w.length = w.affineCoeffs := by
  unfold prefixCoeffs affineCoeffs
  rw [← map_aAt_range_length w]
  rw [List.foldl_map]

/-- The full-period prefix numerator is `Cw`. -/
theorem prefixC_length_eq_Cw (w : PhantomWord) :
    w.prefixC w.length = w.Cw := by
  unfold prefixC Cw
  rw [prefixCoeffs_length_eq_affineCoeffs]

/-- The full-period numerator coefficient `C_w` is odd. -/
theorem Cw_odd (w : PhantomWord) : Odd w.Cw := by
  rw [← prefixC_length_eq_Cw]
  exact w.prefixC_odd_of_pos w.length_pos

/-- The full-period numerator coefficient `C_w` is non-zero. -/
theorem Cw_ne_zero (w : PhantomWord) : w.Cw ≠ 0 := by
  intro h
  have hodd := w.Cw_odd
  rw [h] at hodd
  rcases hodd with ⟨k, hk⟩
  omega

/-- The integer denominator `2^A_w - 3^L` is non-zero. -/
theorem qwIntDen_ne_zero (w : PhantomWord) : qwIntDen w ≠ 0 := by
  intro hzero
  have hodd := qwIntDen_odd w
  rw [hzero] at hodd
  rcases hodd with ⟨k, hk⟩
  omega

/-- The rational denominator `2^A_w - 3^L` is non-zero. -/
theorem qwRat_denominator_ne_zero (w : PhantomWord) :
    (2 : ℚ) ^ w.Aw - (3 : ℚ) ^ w.length ≠ 0 := by
  have h := qwIntDen_ne_zero w
  unfold qwIntDen at h
  exact_mod_cast h

/-- The rational phantom representative is non-zero. -/
theorem qwRat_ne_zero (w : PhantomWord) : qwRat w ≠ 0 := by
  rw [qwRat_eq_divInt]
  exact Rat.divInt_ne_zero_of_ne_zero (by exact_mod_cast w.Cw_ne_zero) (qwIntDen_ne_zero w)

/-- The rational phantom representative has trivial 2-adic valuation. -/
theorem padicValRat_qwRat_zero (w : PhantomWord) : padicValRat 2 (qwRat w) = 0 := by
  have hCnotNat : ¬ (2 : ℕ) ∣ w.Cw := by
    intro h
    have heven : Even w.Cw := (even_iff_two_dvd).2 h
    exact (Nat.not_even_iff_odd.mpr w.Cw_odd) heven
  have hCnotInt : ¬ (2 : ℤ) ∣ (w.Cw : ℤ) := by
    intro h
    have hn : (2 : ℕ) ∣ w.Cw := by exact_mod_cast h
    exact hCnotNat hn
  have hDnotInt : ¬ (2 : ℤ) ∣ qwIntDen w := by
    intro h
    have heven : Even (qwIntDen w) := (even_iff_two_dvd).2 h
    exact (Int.not_even_iff_odd.mpr (qwIntDen_odd w)) heven
  rw [qwRat_eq_divInt, Rat.divInt_eq_div]
  rw [padicValRat.div]
  · rw [padicValRat.of_int, padicValRat.of_int]
    rw [padicValInt.eq_zero_of_not_dvd hCnotInt, padicValInt.eq_zero_of_not_dvd hDnotInt]
    norm_num
  · exact_mod_cast w.Cw_ne_zero
  · exact_mod_cast qwIntDen_ne_zero w

/-- The 2-adic representative `q_w` is a unit: its valuation is zero. -/
theorem valuation_qwZ2_zero (w : PhantomWord) :
    (qwZ2 w (PhantomWord.qwOddDen w)).valuation = 0 := by
  have hQ :
      (((qwZ2 w (PhantomWord.qwOddDen w) : ℤ_[2]) : ℚ_[2]).valuation : ℤ) = 0 := by
    change (((qwRat w : ℚ) : ℚ_[2]).valuation : ℤ) = 0
    rw [Padic.valuation_ratCast]
    exact padicValRat_qwRat_zero w
  rw [PadicInt.valuation_coe] at hQ
  exact_mod_cast hQ

/-- Rational one-step identity for `q_w` and the one-step cyclic shift. -/
theorem qwRat_step_cyclicShift_one (w : PhantomWord) :
    (3 : ℚ) * qwRat w + 1 = (2 : ℚ) ^ w.aAt 0 * qwRat (w.cyclicShift 1) := by
  unfold qwRat
  have hD : (2 : ℚ) ^ w.Aw - (3 : ℚ) ^ w.length ≠ 0 := qwRat_denominator_ne_zero w
  have hstep := Cw_step_cyclicShift_one w
  have hstepQ :
      (3 : ℚ) * (w.Cw : ℚ) + ((2 : ℚ) ^ w.Aw - (3 : ℚ) ^ w.length) =
        (2 : ℚ) ^ w.aAt 0 * ((w.cyclicShift 1).Cw : ℚ) := by
    exact_mod_cast hstep
  rw [cyclicShift_Aw, cyclicShift_length]
  field_simp [hD]
  linear_combination hstepQ

/-- 2-adic rational one-step identity for `q_w`. -/
theorem qwZ2_step_cyclicShift_one_Qp (w : PhantomWord) :
    (3 : ℚ_[2]) * (qwZ2 w (PhantomWord.qwOddDen w) : ℚ_[2]) + 1 =
      (2 : ℚ_[2]) ^ w.aAt 0 *
        (qwZ2 (w.cyclicShift 1) (PhantomWord.qwOddDen (w.cyclicShift 1)) : ℚ_[2]) := by
  change (3 : ℚ_[2]) * ((qwRat w : ℚ) : ℚ_[2]) + 1 =
      (2 : ℚ_[2]) ^ w.aAt 0 * (((qwRat (w.cyclicShift 1) : ℚ) : ℚ_[2]))
  exact_mod_cast qwRat_step_cyclicShift_one w

/-- The 2-adic representative `q_w` is non-zero. -/
theorem qwZ2_ne_zero (w : PhantomWord) :
    qwZ2 w (PhantomWord.qwOddDen w) ≠ 0 := by
  intro h
  have hQ : (((qwRat w : ℚ) : ℚ_[2])) = 0 := by
    simpa [qwZ2] using congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) h
  have hRat : qwRat w = 0 := by exact_mod_cast hQ
  exact w.qwRat_ne_zero hRat

/-- 2-adic-integer one-step identity for `q_w`. -/
theorem qwZ2_step_cyclicShift_one_z2 (w : PhantomWord) :
    (3 : ℤ_[2]) * qwZ2 w (PhantomWord.qwOddDen w) + 1 =
      qwZ2 (w.cyclicShift 1) (PhantomWord.qwOddDen (w.cyclicShift 1)) *
        (2 : ℤ_[2]) ^ w.aAt 0 := by
  apply PadicInt.ext
  have h := qwZ2_step_cyclicShift_one_Qp w
  change (3 : ℚ_[2]) * (qwZ2 w (PhantomWord.qwOddDen w) : ℚ_[2]) + 1 =
    (qwZ2 (w.cyclicShift 1) (PhantomWord.qwOddDen (w.cyclicShift 1)) : ℚ_[2]) *
      (2 : ℚ_[2]) ^ w.aAt 0
  rw [h]
  ring

/-- The first valuation of the `q_w` orbit is the first entry of `w`. -/
theorem qwZ2_first_match (w : PhantomWord) :
    ν₂Z2 ((3 : ℤ_[2]) * qwZ2 w (PhantomWord.qwOddDen w) + 1) = w.aAt 0 := by
  exact nu2Z2_eq_of_eq_unit_mul_two_pow
    (qwZ2_step_cyclicShift_one_z2 w)
    (qwZ2_ne_zero (w.cyclicShift 1))
    (valuation_qwZ2_zero (w.cyclicShift 1))

/-- The first Syracuse step sends `q_w` to the representative of the
one-step cyclic shift of `w`. -/
theorem Syracuse2adic_qwZ2_eq_cyclicShift_one (w : PhantomWord) :
    Syracuse2adic (qwZ2 w (PhantomWord.qwOddDen w)) =
      qwZ2 (w.cyclicShift 1) (PhantomWord.qwOddDen (w.cyclicShift 1)) := by
  have hval := qwZ2_first_match w
  have hne : (3 : ℤ_[2]) * qwZ2 w (PhantomWord.qwOddDen w) + 1 ≠ 0 := by
    rw [qwZ2_step_cyclicShift_one_z2]
    exact mul_ne_zero (qwZ2_ne_zero (w.cyclicShift 1)) (pow_ne_zero _ two_ne_zero_z2)
  have hspec := Syracuse2adic_spec (qwZ2 w (PhantomWord.qwOddDen w)) hne
  have hval' : ((3 : ℤ_[2]) * qwZ2 w (PhantomWord.qwOddDen w) + 1).valuation =
      w.aAt 0 := hval
  rw [hval'] at hspec
  have hstep := qwZ2_step_cyclicShift_one_z2 w
  have hpow_ne : (2 : ℤ_[2]) ^ w.aAt 0 ≠ 0 := pow_ne_zero _ two_ne_zero_z2
  exact mul_right_cancel₀ hpow_ne (hspec.symm.trans hstep)

/-- The `j`-th iterate of `q_w` is the representative attached to the
`j`-fold cyclic shift of `w`. -/
theorem Syracuse2adic_iterate_qwZ2_eq_cyclicShift
    (w : PhantomWord) (j : ℕ) :
    Syracuse2adic^[j] (qwZ2 w (PhantomWord.qwOddDen w)) =
      qwZ2 (w.cyclicShift j) (PhantomWord.qwOddDen (w.cyclicShift j)) := by
  induction j with
  | zero =>
      rw [Function.iterate_zero_apply, cyclicShift_zero]
  | succ j ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih,
        Syracuse2adic_qwZ2_eq_cyclicShift_one, cyclicShift_cyclicShift_one]

/-- The orbit of `q_w` matches the phantom word over one full period. -/
theorem qw_orbit_matches_one_period (w : PhantomWord) :
    MatchesPrefix w (qwZ2 w (PhantomWord.qwOddDen w)) w.length := by
  intro j hj
  rw [Syracuse2adic_iterate_qwZ2_eq_cyclicShift]
  have h := qwZ2_first_match (w.cyclicShift j)
  rw [cyclicShift_aAt] at h
  simpa using h

/-- The 2-adic representative `q_w` is a fixed point of the full-period
affine map `S_w`. -/
theorem qwZ2_fixed_by_S_w (w : PhantomWord) :
    S_w w (qwZ2 w (PhantomWord.qwOddDen w))
      = (qwZ2 w (PhantomWord.qwOddDen w) : ℚ_[2]) := by
  unfold S_w qwZ2 qwRat
  have hdenQ : (2 : ℚ) ^ w.Aw - (3 : ℚ) ^ w.length ≠ 0 :=
    qwRat_denominator_ne_zero w
  have hdenQ2 : (((2 : ℚ) ^ w.Aw - (3 : ℚ) ^ w.length : ℚ) : ℚ_[2]) ≠ 0 := by
    exact_mod_cast hdenQ
  have hpow2 : ((2 : ℚ_[2]) ^ w.Aw) ≠ 0 := pow_ne_zero _ two_ne_zero
  push_cast
  field_simp [hdenQ2, hpow2]
  set D : ℚ_[2] := (((2 : ℚ) ^ w.Aw - (3 : ℚ) ^ w.length : ℚ) : ℚ_[2])
  set P : ℚ_[2] := (2 : ℚ_[2]) ^ w.Aw
  set T : ℚ_[2] := (3 : ℚ_[2]) ^ w.length
  set C : ℚ_[2] := (w.Cw : ℚ_[2])
  have hD : D = P - T := by
    unfold D P T
    push_cast
    ring
  have hD_ne : P - T ≠ 0 := by
    rw [← hD]
    exact hdenQ2
  field_simp [hD_ne]
  ring

end PhantomWord

/-- **Prefix affine form for one orbit.** If the first `j` steps of `x`
match the prescribed word, then the `j`-th 2-adic Syracuse iterate is the
affine prefix `(3^j x + C_j) / 2^{B_j}` in `ℚ_[2]`. -/
theorem affine_iterate_prefix
    (w : PhantomWord) (x : ℤ_[2]) (j : ℕ)
    (h_match : MatchesPrefix w x j) :
    (Syracuse2adic^[j] x : ℚ_[2])
      = ((3 : ℚ_[2]) ^ j * (x : ℚ_[2]) + (w.prefixC j : ℚ_[2]))
          / ((2 : ℚ_[2]) ^ w.B j) := by
  induction j with
  | zero =>
      simp [Function.iterate_zero, PhantomWord.B_zero, PhantomWord.prefixC_zero]
  | succ k ih =>
      have h_match_k : MatchesPrefix w x k :=
        fun i hi => h_match i (Nat.lt_succ_of_lt hi)
      have ih' := ih h_match_k
      set xk : ℤ_[2] := Syracuse2adic^[k] x with hxk
      have h_val_ν : ν₂Z2 ((3 : ℤ_[2]) * xk + 1) = w.aAt k := h_match k (Nat.lt_succ_self k)
      have h_val : ((3 : ℤ_[2]) * xk + 1).valuation = w.aAt k := h_val_ν
      have h_xk_ne : (3 : ℤ_[2]) * xk + 1 ≠ 0 := by
        have := ne_zero_of_matches w x k h_val_ν
        simpa [hxk] using this
      have hspecQ :
          (Syracuse2adic xk : ℚ_[2])
            = ((3 : ℚ_[2]) * (xk : ℚ_[2]) + 1)
                / ((2 : ℚ_[2]) ^ w.aAt k) := by
        have h := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) (Syracuse2adic_spec xk h_xk_ne)
        push_cast at h
        rw [h_val] at h
        have hpow_ne : ((2 : ℚ_[2]) ^ w.aAt k) ≠ 0 := pow_ne_zero _ two_ne_zero
        rw [eq_div_iff hpow_ne]
        simpa using h.symm
      have h_iter : Syracuse2adic^[k + 1] x = Syracuse2adic xk := by
        rw [Function.iterate_succ', Function.comp_apply]
      rw [h_iter, hspecQ, ih', w.B_succ k, w.prefixC_succ k]
      have h2_ne : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
      have hpow_Bk : ((2 : ℚ_[2]) ^ w.B k) ≠ 0 := pow_ne_zero _ h2_ne
      have hpow_aAt : ((2 : ℚ_[2]) ^ w.aAt k) ≠ 0 := pow_ne_zero _ h2_ne
      field_simp [hpow_Bk, hpow_aAt, pow_add]
      push_cast
      rw [pow_add]
      ring

/-!
## Phase-5 reduction: one-period matching implies full matching

The remaining intrinsic property of `q_w` is now reduced to a finite
prefix statement: it is enough to verify the `ν₂` word over one full
period. The fixed-point identity for `q_w` then repeats that block
forever.
-/

/-- If `q_w` matches one full period, its `length`-th Syracuse iterate
returns to `q_w`. -/
theorem qwZ2_iterate_length_eq_self_of_matches
    (w : PhantomWord)
    (h_period : MatchesPrefix w (qwZ2 w (PhantomWord.qwOddDen w)) w.length) :
    Syracuse2adic^[w.length] (qwZ2 w (PhantomWord.qwOddDen w))
      = qwZ2 w (PhantomWord.qwOddDen w) := by
  apply PadicInt.ext
  have h_aff :=
    affine_iterate_prefix w (qwZ2 w (PhantomWord.qwOddDen w)) w.length h_period
  have hB : w.B w.length = w.Aw := by
    calc
      w.B w.length = w.B (1 * w.length) := by simp
      _ = 1 * w.A := w.B_mul_period 1
      _ = w.A := by simp
      _ = w.Aw := by rw [w.Aw_eq_A]
  rw [h_aff]
  simpa [S_w, hB, PhantomWord.prefixC_length_eq_Cw] using w.qwZ2_fixed_by_S_w

/-- A point fixed by `f^[L]` is fixed by every whole-period iterate,
even after an additional prefix of length `r`. -/
private theorem iterate_period_mul_add_eq
    {α : Type*} (f : α → α) (x : α) (L b r : ℕ)
    (hfix : f^[L] x = x) :
    f^[b * L + r] x = f^[r] x := by
  induction b with
  | zero =>
      simp
  | succ b ih =>
      have hcomm : f^[L] (f^[r] x) = f^[r] (f^[L] x) := by
        change (f^[L] ∘ f^[r]) x = (f^[r] ∘ f^[L]) x
        rw [← Function.iterate_add, ← Function.iterate_add, Nat.add_comm]
      calc
        f^[(b + 1) * L + r] x
            = f^[L + (b * L + r)] x := by
                congr 1
                ring
        _ = f^[L] (f^[b * L + r] x) := by
                rw [Function.iterate_add, Function.comp_apply]
        _ = f^[L] (f^[r] x) := by rw [ih]
        _ = f^[r] (f^[L] x) := hcomm
        _ = f^[r] x := by rw [hfix]

/-- If the orbit of `q_w` matches the phantom word over one complete
period, then it matches the periodic word at every step. -/
theorem qw_orbit_matches_of_period
    (w : PhantomWord)
    (h_period : MatchesPrefix w (qwZ2 w (PhantomWord.qwOddDen w)) w.length) :
    ∀ k,
      ν₂Z2 ((3 : ℤ_[2]) * Syracuse2adic^[k]
              (qwZ2 w (PhantomWord.qwOddDen w)) + 1) = w.aAt k := by
  intro k
  set q : ℤ_[2] := qwZ2 w (PhantomWord.qwOddDen w) with hq
  set r : ℕ := k % w.length with hr_def
  have hr_lt : r < w.length := by
    rw [hr_def]
    exact Nat.mod_lt k w.length_pos
  have hfix : Syracuse2adic^[w.length] q = q := by
    simpa [hq] using qwZ2_iterate_length_eq_self_of_matches w h_period
  have hk_decomp : k = (k / w.length) * w.length + r := by
    calc
      k = w.length * (k / w.length) + k % w.length := by
            exact (Nat.div_add_mod k w.length).symm
      _ = (k / w.length) * w.length + r := by
            rw [Nat.mul_comm, hr_def]
  have h_iter :
      Syracuse2adic^[k] q = Syracuse2adic^[r] q := by
    rw [hk_decomp]
    exact iterate_period_mul_add_eq Syracuse2adic q w.length (k / w.length) r hfix
  have haAt : w.aAt r = w.aAt k := by
    unfold PhantomWord.aAt
    rw [hr_def]
    rw [Nat.mod_eq_of_lt hr_lt]
  rw [h_iter]
  exact (h_period r hr_lt).trans haAt

/-- The intrinsic matching property of the phantom representative:
the `q_w` orbit produces the periodic word `w^∞`. -/
theorem qw_orbit_matches (w : PhantomWord) :
    ∀ k,
      ν₂Z2 ((3 : ℤ_[2]) * Syracuse2adic^[k]
              (qwZ2 w (PhantomWord.qwOddDen w)) + 1) = w.aAt k :=
  qw_orbit_matches_of_period w (PhantomWord.qw_orbit_matches_one_period w)

/-- **`ℤ_[2]`-valued affine difference identity.** Multiplied form
of `affine_difference`, valid in `ℤ_[2]` (no division).

Proved by direct induction on `j`, mirroring `affine_difference` but
staying in `ℤ_[2]` throughout (the `2^{B_j}` factor sits on the LHS,
so no division is needed). -/
theorem affine_difference_z2
    (w : PhantomWord) (n : ℤ_[2]) (j : ℕ)
    (h_n : MatchesPrefix w n j)
    (h_qw : MatchesPrefix w (qwZ2 w (PhantomWord.qwOddDen w)) j) :
    (Syracuse2adic^[j] n - Syracuse2adic^[j] (qwZ2 w (PhantomWord.qwOddDen w)))
        * (2 : ℤ_[2]) ^ w.B j
      = (3 : ℤ_[2]) ^ j * (n - qwZ2 w (PhantomWord.qwOddDen w)) := by
  induction j with
  | zero =>
    simp [Function.iterate_zero, PhantomWord.B_zero]
  | succ k ih =>
    have h_n_k : MatchesPrefix w n k := fun i hi => h_n i (Nat.lt_succ_of_lt hi)
    have h_qw_k : MatchesPrefix w (qwZ2 w (PhantomWord.qwOddDen w)) k :=
      fun i hi => h_qw i (Nat.lt_succ_of_lt hi)
    have ih' := ih h_n_k h_qw_k
    set q : ℤ_[2] := qwZ2 w (PhantomWord.qwOddDen w) with hq
    set xn : ℤ_[2] := Syracuse2adic^[k] n with hxn
    set xq : ℤ_[2] := Syracuse2adic^[k] q with hxq
    have h_match_n_ν : ν₂Z2 ((3 : ℤ_[2]) * xn + 1) = w.aAt k := h_n k (Nat.lt_succ_self k)
    have h_match_q_ν : ν₂Z2 ((3 : ℤ_[2]) * xq + 1) = w.aAt k := h_qw k (Nat.lt_succ_self k)
    have h_match_n : ((3 : ℤ_[2]) * xn + 1).valuation = w.aAt k := h_match_n_ν
    have h_match_q : ((3 : ℤ_[2]) * xq + 1).valuation = w.aAt k := h_match_q_ν
    have h_xn_ne : (3 : ℤ_[2]) * xn + 1 ≠ 0 := by
      have := ne_zero_of_matches w n k h_match_n_ν
      simpa [hxn] using this
    have h_xq_ne : (3 : ℤ_[2]) * xq + 1 ≠ 0 := by
      have := ne_zero_of_matches w q k h_match_q_ν
      simpa [hxq] using this
    have sx := Syracuse2adic_spec xn h_xn_ne
    have sq := Syracuse2adic_spec xq h_xq_ne
    rw [h_match_n] at sx
    rw [h_match_q] at sq
    -- One step difference identity in ℤ_[2].
    have h_step_z2 : (3 : ℤ_[2]) * (xn - xq)
                   = (Syracuse2adic xn - Syracuse2adic xq) * (2 : ℤ_[2]) ^ w.aAt k := by
      linear_combination sx - sq
    have h_iter : Syracuse2adic^[k+1] n = Syracuse2adic xn := by
      rw [Function.iterate_succ', Function.comp_apply]
    have h_iter_q : Syracuse2adic^[k+1] q = Syracuse2adic xq := by
      rw [Function.iterate_succ', Function.comp_apply]
    rw [h_iter, h_iter_q, w.B_succ k]
    -- Goal now: (S2 xn - S2 xq) * 2^{B k + aAt k} = 3^{k+1} * (n - q)
    calc (Syracuse2adic xn - Syracuse2adic xq) * (2 : ℤ_[2]) ^ (w.B k + w.aAt k)
        = ((Syracuse2adic xn - Syracuse2adic xq) * (2 : ℤ_[2]) ^ w.aAt k)
              * (2 : ℤ_[2]) ^ w.B k := by rw [pow_add]; ring
      _ = ((3 : ℤ_[2]) * (xn - xq)) * (2 : ℤ_[2]) ^ w.B k := by rw [← h_step_z2]
      _ = (3 : ℤ_[2]) * ((xn - xq) * (2 : ℤ_[2]) ^ w.B k) := by ring
      _ = (3 : ℤ_[2]) * ((3 : ℤ_[2]) ^ k * (n - q)) := by rw [ih']
      _ = (3 : ℤ_[2]) ^ (k + 1) * (n - q) := by ring

/-!
## Task 3.3 — Stable `ν₂` under 2-adic proximity

Under the prefix-matching hypothesis (and hence with the affine
difference of Task 3.2 controlled), `ν₂(3·x + 1)` and `ν₂(3·y + 1)`
agree and equal the prescribed `a_j` whenever the 2-adic distance
between `x` and `y` is at least `a_j + 1`.
-/

/-- Negation preserves the 2-adic valuation in `ℤ_[2]`. -/
private theorem valuation_z2_neg (x : ℤ_[2]) (hx : x ≠ 0) :
    (-x).valuation = x.valuation := by
  have h_neg_ne : -x ≠ 0 := neg_ne_zero.mpr hx
  have hnorm_eq : ‖-x‖ = ‖x‖ := norm_neg x
  rw [PadicInt.norm_eq_zpow_neg_valuation hx,
      PadicInt.norm_eq_zpow_neg_valuation h_neg_ne] at hnorm_eq
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h2_ne_one : (2 : ℝ) ≠ 1 := by norm_num
  -- (2:ℝ)^(-v(-x)) = (2:ℝ)^(-v(x)) ⟹ -v(-x) = -v(x) ⟹ v(-x) = v(x)
  have h_eq_zpow : (-((-x).valuation : ℤ)) = (-(x.valuation : ℤ)) :=
    zpow_right_injective₀ h2_pos h2_ne_one hnorm_eq
  omega

/-- **Strict ultrametric on `ℤ_[2]`.** When the 2-adic valuations of two
non-zero `ℤ_[2]`-elements differ strictly, the valuation of the sum
equals the smaller of the two. -/
private theorem valuation_add_eq_left_of_lt
    (a b : ℤ_[2]) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (hlt : a.valuation < b.valuation) :
    (a + b).valuation = a.valuation := by
  -- ≥ direction.
  have hge : a.valuation ≤ (a + b).valuation := by
    have h := PadicInt.le_valuation_add hab
    have hmin : min a.valuation b.valuation = a.valuation := min_eq_left (le_of_lt hlt)
    omega
  -- ≤ direction by contradiction: a = (a + b) + (-b).
  have hle : (a + b).valuation ≤ a.valuation := by
    by_contra hgt
    push Not at hgt
    have h_a_eq : a = (a + b) + (-b) := by ring
    have h_neg_b_ne : -b ≠ 0 := neg_ne_zero.mpr hb
    have h_sum_ne : (a + b) + (-b) ≠ 0 := by rw [← h_a_eq]; exact ha
    have h_min_lt : a.valuation < min (a + b).valuation (-b).valuation := by
      rw [valuation_z2_neg b hb]
      exact lt_min hgt hlt
    have h_le := PadicInt.le_valuation_add h_sum_ne
    rw [← h_a_eq] at h_le
    omega
  omega

/--
**Task 3.3.** If the 2-adic difference between two `ℤ_[2]`-elements
has valuation at least `a_j + 1`, then both produce the same `ν₂` of
`3·· + 1`, equal to `a_j`. (Used to feed the inductive step of
Lemma 3.1.)
-/
theorem nu2_stable_under_proximity
    (w : PhantomWord) (x y : ℤ_[2]) (j : ℕ)
    (h_match_y : ν₂Z2 ((3 : ℤ_[2]) * y + 1) = w.aAt j)
    (h_close : ((w.aAt j) + 1 : ℕ) ≤ ν₂Z2 (x - y)) :
    ν₂Z2 ((3 : ℤ_[2]) * x + 1) = w.aAt j ∧
      ν₂Z2 ((3 : ℤ_[2]) * y + 1) = w.aAt j := by
  refine ⟨?_, h_match_y⟩
  -- Set a := 3y+1, b := 3(x-y), so a + b = 3x+1.
  set a : ℤ_[2] := (3 : ℤ_[2]) * y + 1 with ha_def
  set b : ℤ_[2] := (3 : ℤ_[2]) * (x - y) with hb_def
  have hab_eq : a + b = (3 : ℤ_[2]) * x + 1 := by
    change (3 : ℤ_[2]) * y + 1 + 3 * (x - y) = 3 * x + 1
    ring
  -- ν(a) = aAt w j (from hypothesis, ν₂Z2 = .valuation).
  have hva : a.valuation = w.aAt j := h_match_y
  -- ν(b) ≥ aAt w j + 1 (since ν(3·z) = ν(z) on ℤ_[2], Task 3.1).
  have hvb_ge : w.aAt j + 1 ≤ b.valuation := by
    have h := h_close
    change w.aAt j + 1 ≤ ((3 : ℤ_[2]) * (x - y)).valuation
    have hmul : ν₂Z2 ((3 : ℤ_[2]) * (x - y)) = ν₂Z2 (x - y) := nu2Z2_three_mul (x - y)
    -- ν₂Z2 = .valuation by def
    have hval : ν₂Z2 ((3 : ℤ_[2]) * (x - y)) = ((3 : ℤ_[2]) * (x - y)).valuation := rfl
    omega
  -- Strict comparison: v(a) < v(b).
  have hlt : a.valuation < b.valuation := by rw [hva]; omega
  -- Non-zero conditions.
  have ha_ne : a ≠ 0 := by
    intro h
    have : a.valuation = 0 := by rw [h]; exact PadicInt.valuation_zero
    rw [hva] at this
    have := w.aAt_pos j
    omega
  have hb_ne : b ≠ 0 := by
    intro h
    have : b.valuation = 0 := by rw [h]; exact PadicInt.valuation_zero
    have := w.aAt_pos j
    omega
  have hab_ne : a + b ≠ 0 := by
    intro h
    have : a.valuation = b.valuation := by
      have ha_eq : a = -b := by
        have : a + b = 0 := h
        linear_combination this
      rw [ha_eq, valuation_z2_neg b hb_ne]
    omega
  -- Apply the strict ultrametric.
  have h_sum := valuation_add_eq_left_of_lt a b ha_ne hb_ne hab_ne hlt
  rw [hab_eq] at h_sum
  -- ν₂Z2 = .valuation by def; combine with hva.
  change ((3 : ℤ_[2]) * x + 1).valuation = w.aAt j
  omega

end CollatzShadowing
