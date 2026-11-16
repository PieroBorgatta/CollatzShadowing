/-
Arithmetic constraints for changing an interior and terminal exponent while
preserving the total valuation. These are necessary congruences, not a
construction of a positive-density transport.

AI-assisted development: Codex with Piero Borgatta, 2026-11-13.
-/

import CollatzShadowing.SignedTransport

namespace CollatzShadowing.WordSurgery

/-- Splitting a word splits its affine constant with the exact scales. -/
theorem constant_append (u v : List ℕ) :
    syracuseWordConst (u ++ v) =
      3 ^ v.length * syracuseWordConst u + 2 ^ u.sum * syracuseWordConst v := by
  induction u with
  | nil => simp [syracuseWordConst]
  | cons a rest ih =>
      simp only [List.cons_append, List.length_append, List.sum_cons,
        syracuseWordConst, ih, pow_add]
      ring

/-- The exact change of the constant when one interior exponent increases.
The last exponent can then be decreased without changing either constant. -/
theorem interior_constant_shift (pref tail : List ℕ) (a d : ℕ) :
    syracuseWordConst (pref ++ (a + d) :: tail) +
        2 ^ (pref.sum + a) * syracuseWordConst tail =
      syracuseWordConst (pref ++ a :: tail) +
        2 ^ (pref.sum + a + d) * syracuseWordConst tail := by
  simp only [constant_append, syracuseWordConst, List.length_cons, pow_add]
  ring

/-- The full and suffix affine identities impose a terminal-depth congruence.
P is the exponent sum through the changed interior position; q is the number
of remaining steps. The displayed constant shift preserves the total sum. -/
theorem balanced_shift_terminal_congruence
    (k q P B d u v n y C T m : ℕ) (hq : q ≤ k)
    (hold : 3 ^ k * u + C = 2 ^ (P + B) * n)
    (hnew : 3 ^ k * v + (C + (2 ^ d - 1) * 2 ^ P * T) =
      2 ^ (P + B) * y)
    (htail : 3 ^ q * m + T = 2 ^ B * n) :
    Nat.ModEq (3 ^ q) y (2 ^ d * n) := by
  have hdiv : 3 ^ q ∣ 3 ^ k := Nat.pow_dvd_pow 3 hq
  have hzero (z : ℕ) : Nat.ModEq (3 ^ q) (3 ^ k * z) 0 := by
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hdiv z)
  have ho : Nat.ModEq (3 ^ q) C (2 ^ (P + B) * n) := by
    rw [← hold]
    simpa using ((hzero u).add_right C).symm
  have ht : Nat.ModEq (3 ^ q) T (2 ^ B * n) := by
    rw [← htail]
    have hz : Nat.ModEq (3 ^ q) (3 ^ q * m) 0 := by
      exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)
    simpa using (hz.add_right T).symm
  have hn : Nat.ModEq (3 ^ q) (2 ^ (P + B) * y)
      (C + (2 ^ d - 1) * 2 ^ P * T) := by
    rw [← hnew]
    simpa using (hzero v).add_right (C + (2 ^ d - 1) * 2 ^ P * T)
  have hm := hn.trans (ho.add (ht.mul_left ((2 ^ d - 1) * 2 ^ P)))
  have hp : 1 ≤ (2 : ℕ) ^ d := Nat.one_le_pow d 2 (by norm_num)
  have hsub : 2 ^ d - 1 + 1 = (2 : ℕ) ^ d := Nat.sub_add_cancel hp
  have heq : 2 ^ (P + B) * n + (2 ^ d - 1) * 2 ^ P * (2 ^ B * n) =
      2 ^ (P + B) * (2 ^ d * n) := by
    rw [pow_add]
    calc
      _ = 2 ^ P * 2 ^ B * ((2 ^ d - 1 + 1) * n) := by ring
      _ = _ := by rw [hsub]
  rw [heq] at hm
  have hcop : (3 ^ q).Coprime (2 ^ (P + B)) :=
    Nat.Coprime.pow_left q (Nat.Coprime.pow_right (P + B) (by norm_num))
  exact Nat.ModEq.cancel_left_of_coprime hcop hm

/-- For fixed distinct odd targets and a bounded positive shift, the changed
position must remain within a finite arithmetic distance from the end. -/
theorem terminal_depth_budget {q n y d : ℕ}
    (hn : Odd n) (hy : Odd y) (hne : n ≠ y)
    (hmod : Nat.ModEq (3 ^ q) y (2 ^ d * n)) :
    3 ^ q ≤ max y (2 ^ d * n) := by
  exact SignedTransport.congruent_shift_requires_large hy hn hne.symm hmod

end CollatzShadowing.WordSurgery
