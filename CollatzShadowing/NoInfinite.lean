/-
Paper Section 3, Corollary 3.4 — no infinite congruential shadowing.

This file isolates the 2-adic core of the no-infinite-shadowing
corollary: congruence to a fixed 2-adic integer at arbitrarily high
2-power precision forces equality in `ℤ_[2]`.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-06.
-/

import CollatzShadowing.Shadowing

namespace CollatzShadowing

/-!
## No Infinite Congruential Shadowing

The paper's Corollary 3.4 combines two facts:

1. Congruence to `q_w` at arbitrarily high 2-adic precision forces
   equality in `ℤ_[2]`.
2. For expansive phantoms, `q_w` is a negative rational, hence cannot
   equal a positive natural number.

This file proves both parts for the Lean definition of an expansive
phantom below.
-/

namespace PhantomWord

/-- A phantom word is expansive when the odd multiplier over one period
dominates the power of two removed over that period. This is the Lean
form of the paper condition `3^L > 2^A`. -/
def Expansive (w : PhantomWord) : Prop :=
  (2 : ℕ) ^ w.Aw < (3 : ℕ) ^ w.length

/-- For an expansive phantom, the rational representative `q_w` is
negative. -/
theorem qwRat_neg_of_expansive (w : PhantomWord) (h_exp : w.Expansive) :
    qwRat w < 0 := by
  unfold qwRat
  have hnum : (0 : ℚ) < (w.Cw : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero w.Cw_ne_zero
  have hden : (2 : ℚ) ^ w.Aw - (3 : ℚ) ^ w.length < 0 := by
    apply sub_neg.mpr
    exact_mod_cast h_exp
  exact div_neg_of_pos_of_neg hnum hden

/-- For an expansive phantom, `q_w` cannot be the 2-adic cast of a
positive natural number. -/
theorem qwZ2_ne_natCast_of_expansive
    (w : PhantomWord) (h_exp : w.Expansive) (n : ℕ) (hn : 0 < n) :
    ((n : ℕ) : ℤ_[2]) ≠ qwZ2 w (PhantomWord.qwOddDen w) := by
  intro h
  have hQ : (((n : ℕ) : ℚ_[2])) = (((qwRat w : ℚ) : ℚ_[2])) := by
    simpa [qwZ2] using congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) h
  have hRat : (n : ℚ) = qwRat w := by exact_mod_cast hQ
  have hnat_pos : (0 : ℚ) < n := by exact_mod_cast hn
  have hqw_neg := w.qwRat_neg_of_expansive h_exp
  rw [hRat] at hnat_pos
  linarith

end PhantomWord

/-- If two 2-adic integers are congruent modulo `2^k` for every `k`,
then they are equal. -/
theorem eq_of_padic_congruent_all_pow2
    (x y : ℤ_[2])
    (h_all : ∀ k : ℕ, PadicCongruentModPow2 x y k) :
    x = y := by
  by_contra hne_eq
  have hdiff_ne : x - y ≠ 0 := sub_ne_zero.mpr hne_eq
  have hbound : (x - y).valuation + 1 ≤ (x - y).valuation := by
    exact (PadicCongruentModPow2_iff_le_valuation hdiff_ne ((x - y).valuation + 1)).mp
      (h_all ((x - y).valuation + 1))
  omega

/-- No natural number distinct from `q_w` can be congruent to `q_w`
modulo every power of two. -/
theorem no_infinite_congruence_to_qw
    (w : PhantomWord) (n : ℕ)
    (h_not_eq : ((n : ℕ) : ℤ_[2]) ≠ qwZ2 w (PhantomWord.qwOddDen w)) :
    ¬ ∀ k : ℕ,
      PadicCongruentModPow2 (n : ℤ_[2])
        (qwZ2 w (PhantomWord.qwOddDen w)) k := by
  intro h_all
  exact h_not_eq (eq_of_padic_congruent_all_pow2 _ _ h_all)

/-- Period-form no-infinite-shadowing obstruction. If a natural number
is not equal to `q_w` in `ℤ_[2]`, then it cannot satisfy the period
shadowing congruence `n ≡ q_w (mod 2^{b*A+1})` for every `b`. -/
theorem no_infinite_period_congruence_to_qw
    (w : PhantomWord) (n : ℕ)
    (h_not_eq : ((n : ℕ) : ℤ_[2]) ≠ qwZ2 w (PhantomWord.qwOddDen w)) :
    ¬ ∀ b : ℕ,
      PadicCongruentModPow2 (n : ℤ_[2])
        (qwZ2 w (PhantomWord.qwOddDen w)) (b * w.A + 1) := by
  intro h_all
  set q : ℤ_[2] := qwZ2 w (PhantomWord.qwOddDen w) with hq
  have hdiff_ne : (n : ℤ_[2]) - q ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa [hq] using h_not_eq)
  let b := ((n : ℤ_[2]) - q).valuation + 1
  have hA : 1 ≤ w.A := by
    rw [← w.Aw_eq_A]
    exact w.one_le_Aw
  have hle :
      b * w.A + 1 ≤ ((n : ℤ_[2]) - q).valuation := by
    exact (PadicCongruentModPow2_iff_le_valuation hdiff_ne (b * w.A + 1)).mp
      (h_all b)
  have hgt : ((n : ℤ_[2]) - q).valuation < b * w.A + 1 := by
    dsimp [b]
    have hmul :
        ((n : ℤ_[2]) - q).valuation + 1 ≤
          (((n : ℤ_[2]) - q).valuation + 1) * w.A :=
      Nat.le_mul_of_pos_right _ hA
    omega
  omega

/-- **Paper Section 3, Corollary 3.4 (period-congruence form).**

For an expansive phantom, no positive natural number can remain in the
periodic shadowing congruence class of `q_w` for every number of
periods. -/
theorem no_infinite_period_congruence_expansive
    (w : PhantomWord) (h_exp : w.Expansive)
    (n : ℕ) (hn : 0 < n) :
    ¬ ∀ b : ℕ,
      PadicCongruentModPow2 (n : ℤ_[2])
        (qwZ2 w (PhantomWord.qwOddDen w)) (b * w.A + 1) := by
  exact no_infinite_period_congruence_to_qw w n
    (w.qwZ2_ne_natCast_of_expansive h_exp n hn)

/--
Boundary theorem for eventual periodic expansive phantom shadowing.

This is the post-prefix form of `no_infinite_period_congruence_expansive`.
After any finite prefix, the endpoint of a positive accelerated integer orbit
is again a positive natural.  Such an endpoint cannot remain, for all numbers
of periods, in the congruence classes of an expansive phantom period.

This deliberately addresses only the eventually periodic obstruction.  It does
not rule out an aperiodic infinite valuation word that shadows different
phantom neighborhoods successively.
-/
theorem no_positive_endpoint_eventually_periodic_expansive_congruence
    (w : PhantomWord) (h_exp : w.Expansive)
    (endpoint : ℕ) (h_endpoint_pos : 0 < endpoint) :
    ¬ ∀ b : ℕ,
      PadicCongruentModPow2 (endpoint : ℤ_[2])
        (qwZ2 w (PhantomWord.qwOddDen w)) (b * w.A + 1) :=
  no_infinite_period_congruence_expansive w h_exp endpoint h_endpoint_pos

end CollatzShadowing
