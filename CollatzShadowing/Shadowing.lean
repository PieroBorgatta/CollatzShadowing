/-
Paper Section 3, Lemma 3.1 — Exact congruential shadowing.

Phase 4 of `TODO.md`: the proof itself, mirroring the paper's
induction (lines 269-302).

Author: AI-assisted (Claude) + Piero Borgatta. Date: 2026-05-04.
-/

import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Logic.Function.Iterate
import CollatzShadowing.Phantom
import CollatzShadowing.Auxiliary
import CollatzShadowing.Syracuse2Adic

namespace CollatzShadowing

/-!
## Shadowing congruence in `ℤ_[2]`

Per `INVENTORY.md` §1.4, congruences `x ≡ y (mod 2^k)` inside `ℤ_[2]`
are encoded as ideal membership. Robust to the edge case `x = y` and
agrees with the standard 2-adic congruence relation.
-/

/-- The shadowing congruence `x ≡ y (mod 2^k)` in `ℤ_[2]`, expressed
as `x - y ∈ ⟨2^k⟩`. -/
def PadicCongruentModPow2 (x y : ℤ_[2]) (k : ℕ) : Prop :=
  x - y ∈ (Ideal.span {((2 : ℤ_[2]) ^ k)} : Ideal ℤ_[2])

/-- Bridge: when `x - y ≠ 0`, `PadicCongruentModPow2 x y k` is
equivalent to `k ≤ ν₂Z2 (x - y)`. -/
theorem PadicCongruentModPow2_iff_le_valuation
    {x y : ℤ_[2]} (hxy : x - y ≠ 0) (k : ℕ) :
    PadicCongruentModPow2 x y k ↔ k ≤ ν₂Z2 (x - y) := by
  unfold PadicCongruentModPow2
  exact PadicInt.mem_span_pow_iff_le_valuation (x - y) hxy k

/-!
## Phase-4 helpers: power valuations
-/

/-- `(3 : ℤ_[2]) ^ j` is non-zero (it is a unit). -/
private theorem three_pow_ne_zero_z2 (j : ℕ) : (3 : ℤ_[2]) ^ j ≠ 0 :=
  pow_ne_zero _ three_ne_zero_z2

/-- `(2 : ℤ_[2]) ^ k` is non-zero. -/
private theorem two_pow_ne_zero_z2 (k : ℕ) : (2 : ℤ_[2]) ^ k ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast (by decide : (2 : ℕ) ≠ 0))

/-- `((3 : ℤ_[2]) ^ j).valuation = 0`. -/
private theorem valuation_three_pow_z2 (j : ℕ) : ((3 : ℤ_[2]) ^ j).valuation = 0 := by
  rw [PadicInt.valuation_pow, valuation_three_z2, mul_zero]

/-!
## Lemma 3.1 (paper-faithful, with `q_w` matching as hypothesis)

Paper Section 3:

> Let `w` be an expansive phantom with `2`-adic representative `q_w`,
> and let `n` be a positive odd integer. If `n ≡ q_w (mod 2^{B_m+1})`
> then the first `m` Syracuse steps of `n` produce exactly the word
> `(a_0, a_1, ..., a_{m-1})`.

The matching property of `q_w`'s own orbit is supplied by
`qw_orbit_matches`, proved in `Auxiliary.lean`: the orbit of `q_w`
under `Syracuse2adic` is periodic with `ν₂` word `w` repeated.
-/

/--
**Paper Section 3, Lemma 3.1 (Exact congruential shadowing).**

Given the congruence `n ≡ q_w (mod 2^{B_m + 1})`, the first `m` Syracuse
iterates of `n` (computed inside `ℤ_[2]` via `Syracuse2adic`) produce
exactly the periodic word `(a_0, a_1, ..., a_{m-1})` of `w`.

Proof: induction on `j`. At step `j < m`:
* `affine_difference_z2` gives `(S^j(n) - S^j(q_w)) · 2^{B_j} =
  3^j · (n - q_w)` in `ℤ_[2]`.
* Taking valuations and using `h_cong`, one obtains
  `ν₂(S^j(n) - S^j(q_w)) ≥ B_m + 1 - B_j ≥ aAt(j) + 1`
  (the second inequality from `B_mono` and `B_succ`).
* `nu2_stable_under_proximity` (Task 3.3) then gives
  `ν₂(3·S^j(n) + 1) = ν₂(3·S^j(q_w) + 1) = aAt(j)`.
-/
theorem exact_shadowing
    (w : PhantomWord) (n : ℕ) (_h_pos : 0 < n) (_h_odd : Odd n) (m : ℕ)
    (h_cong :
      PadicCongruentModPow2 (n : ℤ_[2])
        (qwZ2 w (PhantomWord.qwOddDen w)) (w.B m + 1)) :
    ∀ j, j < m →
      ν₂Z2 ((3 : ℤ_[2]) * Syracuse2adic^[j] ((n : ℕ) : ℤ_[2]) + 1) = w.aAt j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    intro hjm
    set q : ℤ_[2] := qwZ2 w (PhantomWord.qwOddDen w) with hq_def
    -- Build MatchesPrefix at j for both `n` and `q_w`.
    have h_n_match : MatchesPrefix w ((n : ℕ) : ℤ_[2]) j := by
      intro k hk
      exact IH k hk (Nat.lt_trans hk hjm)
    have h_qw_match : MatchesPrefix w q j := by
      intro k _
      exact qw_orbit_matches w k
    -- Case split on whether (n : ℤ_[2]) = q.
    by_cases h_eq : ((n : ℕ) : ℤ_[2]) = q
    · -- Equal case: iterates match, conclusion from `qw_orbit_matches`.
      have heq_iter : Syracuse2adic^[j] ((n : ℕ) : ℤ_[2]) = Syracuse2adic^[j] q := by
        rw [h_eq]
      rw [heq_iter]
      exact qw_orbit_matches w j
    · -- Generic case: use `affine_difference_z2` + valuation arithmetic + Task 3.3.
      have h_diff_ne : ((n : ℕ) : ℤ_[2]) - q ≠ 0 := sub_ne_zero.mpr h_eq
      -- The affine identity in ℤ_[2].
      have h_affine := affine_difference_z2 w ((n : ℕ) : ℤ_[2]) j h_n_match h_qw_match
      -- Both sides of the affine identity are non-zero.
      have h_RHS_ne : (3 : ℤ_[2]) ^ j * (((n : ℕ) : ℤ_[2]) - q) ≠ 0 :=
        mul_ne_zero (three_pow_ne_zero_z2 j) h_diff_ne
      have h_LHS_ne :
          (Syracuse2adic^[j] ((n : ℕ) : ℤ_[2]) - Syracuse2adic^[j] q)
            * (2 : ℤ_[2]) ^ w.B j ≠ 0 := by
        rw [h_affine]; exact h_RHS_ne
      have h_diffj_ne :
          Syracuse2adic^[j] ((n : ℕ) : ℤ_[2]) - Syracuse2adic^[j] q ≠ 0 :=
        left_ne_zero_of_mul h_LHS_ne
      -- Compute the valuation of the difference at step j.
      have h_LHS_val := PadicInt.valuation_mul h_diffj_ne (two_pow_ne_zero_z2 (w.B j))
      have h_RHS_val := PadicInt.valuation_mul (three_pow_ne_zero_z2 j) h_diff_ne
      have h_val_eq :
          (Syracuse2adic^[j] ((n : ℕ) : ℤ_[2]) - Syracuse2adic^[j] q).valuation + w.B j
            = (((n : ℕ) : ℤ_[2]) - q).valuation := by
        have hcongr := congrArg PadicInt.valuation h_affine
        rw [h_LHS_val, h_RHS_val, valuation_two_pow_z2, valuation_three_pow_z2,
            zero_add] at hcongr
        exact hcongr
      -- Bound from h_cong: B_m + 1 ≤ ν₂(n - q_w).
      have h_cong_val : w.B m + 1 ≤ (((n : ℕ) : ℤ_[2]) - q).valuation :=
        (PadicCongruentModPow2_iff_le_valuation h_diff_ne (w.B m + 1)).mp h_cong
      -- B is monotonic; B (j+1) = B j + aAt w j; j+1 ≤ m.
      have h_Bjp1_le_Bm : w.B (j + 1) ≤ w.B m := w.B_mono hjm
      have h_Bjp1 : w.B (j + 1) = w.B j + w.aAt j := w.B_succ j
      -- Combining gives v(diff_j) ≥ aAt w j + 1.
      have h_close_val :
          w.aAt j + 1 ≤
            (Syracuse2adic^[j] ((n : ℕ) : ℤ_[2]) - Syracuse2adic^[j] q).valuation := by
        omega
      -- ν₂Z2 unfolds to .valuation by def.
      have h_close :
          w.aAt j + 1 ≤
            ν₂Z2 (Syracuse2adic^[j] ((n : ℕ) : ℤ_[2]) - Syracuse2adic^[j] q) :=
        h_close_val
      -- Apply Task 3.3.
      have h_match_q_at_j : ν₂Z2 ((3 : ℤ_[2]) * Syracuse2adic^[j] q + 1) = w.aAt j :=
        qw_orbit_matches w j
      have h_3_3 := nu2_stable_under_proximity w (Syracuse2adic^[j] ((n : ℕ) : ℤ_[2]))
                      (Syracuse2adic^[j] q) j h_match_q_at_j h_close
      exact h_3_3.1

/-!
## Periodic specialisation `m = b · L`

Paper "in particular" clause of Lemma 3.1.

`exact_shadowing_periods` is the specialisation to `m = b · L` (i.e.
shadowing for `b` full periods). The congruence bound is expressed in
the paper's form `b · A`, and converted to `B (b · L)` by
`PhantomWord.B_mul_period`.
-/

/--
**Lemma 3.1, period form (literal specialisation).**

If `n ≡ q_w (mod 2^{b·A + 1})`, then `n` shadows `w^∞` for the
first `b · L` Syracuse steps. The bound is stated as `b · A`, matching
the paper's "in particular" clause.
-/
theorem exact_shadowing_periods
    (w : PhantomWord) (n : ℕ) (h_pos : 0 < n) (h_odd : Odd n) (b : ℕ)
    (h_cong :
      PadicCongruentModPow2 (n : ℤ_[2])
        (qwZ2 w (PhantomWord.qwOddDen w)) (b * w.A + 1)) :
    ∀ j, j < b * w.length →
      ν₂Z2 ((3 : ℤ_[2]) * Syracuse2adic^[j] ((n : ℕ) : ℤ_[2]) + 1) = w.aAt j :=
  have h_cong' :
      PadicCongruentModPow2 (n : ℤ_[2])
        (qwZ2 w (PhantomWord.qwOddDen w)) (w.B (b * w.length) + 1) := by
    simpa [w.B_mul_period b] using h_cong
  exact_shadowing w n h_pos h_odd (b * w.length) h_cong'

end CollatzShadowing
