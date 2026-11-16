/-
Exact dyadic cylinders for finite Syracuse exponent words.

The final parity bit is essential.  Divisibility by `2 ^ w.sum` only
certifies an integral affine endpoint; the modulus `2 ^ (w.sum + 1)`
certifies that this endpoint is odd, and hence that every prescribed
valuation is exact.
-/

import CollatzShadowing.FirstBarrier
import CollatzShadowing.Shadowing

namespace CollatzShadowing

/-- The affine numerator of a prescribed exponent word. -/
def syracuseWordAffineNumerator (w : List ℕ) (n : ℕ) : ℕ :=
  3 ^ w.length * n + syracuseWordConst w

private theorem wordConst_mod_two_of_positive_head
    {a : ℕ} (rest : List ℕ) (ha : 0 < a) :
    syracuseWordConst (a :: rest) % 2 = 1 := by
  have hpow : 2 ^ a % 2 = 0 :=
    Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (Nat.ne_of_gt ha))
  simp [syracuseWordConst, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hpow]

/-- The exact final residue is equivalent to an integral odd affine endpoint. -/
private theorem exactResidue_iff_odd_endpoint (w : List ℕ) (n : ℕ) :
    syracuseWordAffineNumerator w n % syracuseWordExactResidueModulus w = 2 ^ w.sum
      ↔ ∃ m : ℕ, Odd m ∧
          2 ^ w.sum * m = syracuseWordAffineNumerator w n := by
  let q : ℕ := 2 ^ w.sum
  have hmod : syracuseWordExactResidueModulus w = q * 2 := by
    simp [syracuseWordExactResidueModulus, q, pow_add]
  constructor
  · intro h
    let t := syracuseWordAffineNumerator w n / syracuseWordExactResidueModulus w
    refine ⟨2 * t + 1, ⟨t, by omega⟩, ?_⟩
    have hdiv := Nat.mod_add_div (syracuseWordAffineNumerator w n)
      (syracuseWordExactResidueModulus w)
    rw [h, hmod] at hdiv
    change q * (2 * t + 1) = syracuseWordAffineNumerator w n
    calc
      q * (2 * t + 1) = q + q * 2 * t := by ring
      _ = syracuseWordAffineNumerator w n := hdiv
  · rintro ⟨m, ⟨t, rfl⟩, heq⟩
    rw [← heq, hmod]
    change (q * (2 * t + 1)) % (q * 2) = q
    have hq : 0 < q := by simp [q]
    rw [Nat.mul_mod_mul_left]
    simp [Nat.add_mod]

/-- A positive exponent suffix has odd affine constant. -/
private theorem wordConst_mod_two_of_positive
    {w : List ℕ} (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 0 < a) :
    syracuseWordConst w % 2 = 1 := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons a rest =>
      exact wordConst_mod_two_of_positive_head rest (hpos a (by simp))

/--
Reverse the affine identity through a positive exponent word.  An odd
endpoint forces every intermediate quotient to be odd, so no earlier
valuation can exceed its prescribed value.
-/
private theorem matches_of_odd_affine_endpoint :
    ∀ (w : List ℕ) (n m : ℕ),
      (∀ a ∈ w, 0 < a) → Odd m →
      2 ^ w.sum * m = syracuseWordAffineNumerator w n →
      SyracuseWordMatchesFrom w n
  | [], _n, _m, _hpos, _hodd, _heq => trivial
  | a :: rest, n, m, hpos, hodd, heq => by
      have hposRest : ∀ b ∈ rest, 0 < b := by
        intro b hb
        exact hpos b (by simp [hb])
      have ha : 0 < a := hpos a (by simp)
      have haff :
          2 ^ a * (2 ^ rest.sum * m) =
            3 ^ rest.length * (3 * n + 1) +
              2 ^ a * syracuseWordConst rest := by
        dsimp [syracuseWordAffineNumerator, syracuseWordConst] at heq
        simp only [pow_add, pow_succ] at heq
        nlinarith [heq]
      have hpow : 0 < 2 ^ a := pow_pos (by norm_num) _
      have hdivProd : 2 ^ a ∣ 3 ^ rest.length * (3 * n + 1) := by
        have hdivRight : 2 ^ a ∣ 2 ^ a * syracuseWordConst rest :=
          dvd_mul_right _ _
        have hdivTotal :
            2 ^ a ∣ 3 ^ rest.length * (3 * n + 1) +
              2 ^ a * syracuseWordConst rest := by
          rw [← haff]
          exact dvd_mul_right _ _
        exact (Nat.dvd_add_iff_left hdivRight).mpr hdivTotal
      have hcop : (2 ^ a).Coprime (3 ^ rest.length) :=
        Nat.Coprime.pow_left a
          (Nat.Coprime.pow_right rest.length (by norm_num : Nat.Coprime 2 3))
      have hdiv : 2 ^ a ∣ 3 * n + 1 :=
        hcop.dvd_mul_left.mp hdivProd
      let t : ℕ := (3 * n + 1) / 2 ^ a
      have hnum : 3 * n + 1 = 2 ^ a * t := by
        simpa [t, Nat.mul_comm] using (Nat.div_mul_cancel hdiv).symm
      have hcancel :
          2 ^ a * (2 ^ rest.sum * m) =
            2 ^ a * (3 ^ rest.length * t + syracuseWordConst rest) := by
        calc
          2 ^ a * (2 ^ rest.sum * m)
              = 3 ^ rest.length * (3 * n + 1) +
                  2 ^ a * syracuseWordConst rest := haff
          _ = 2 ^ a * (3 ^ rest.length * t + syracuseWordConst rest) := by
                rw [hnum]
                ring
      have htail :
          2 ^ rest.sum * m = syracuseWordAffineNumerator rest t := by
        unfold syracuseWordAffineNumerator
        exact mul_left_cancel₀ (Nat.ne_of_gt hpow) hcancel
      have htodd : Odd t := by
        by_cases hrest : rest = []
        · subst rest
          simp [syracuseWordAffineNumerator, syracuseWordConst] at htail
          simpa [htail] using hodd
        · have hsum : 0 < rest.sum := by
            cases rest with
            | nil => exact False.elim (hrest rfl)
            | cons b bs =>
                have hb : 0 < b := hposRest b (by simp)
                simp only [List.sum_cons]
                omega
          have hqmod : 2 ^ rest.sum % 2 = 0 :=
            Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (Nat.ne_of_gt hsum))
          have hpmod : 3 ^ rest.length % 2 = 1 := by
            simp [Nat.pow_mod]
          have hcmod : syracuseWordConst rest % 2 = 1 :=
            wordConst_mod_two_of_positive hrest hposRest
          have hmod := congrArg (fun x : ℕ => x % 2) htail
          unfold syracuseWordAffineNumerator at hmod
          have hleftmod : (2 ^ rest.sum * m) % 2 = 0 := by
            rw [Nat.mul_mod, hqmod]
            simp
          have hrightmod :
              (3 ^ rest.length * t + syracuseWordConst rest) % 2 =
                (t % 2 + 1) % 2 := by
            rw [Nat.add_mod, Nat.mul_mod, hpmod, hcmod]
            simp
          change (2 ^ rest.sum * m) % 2 =
            (3 ^ rest.length * t + syracuseWordConst rest) % 2 at hmod
          rw [hleftmod, hrightmod] at hmod
          have htmod : t % 2 = 1 := by omega
          exact Nat.odd_iff.mpr htmod
      have hstep := syracuseStep_of_num_eq_two_pow_mul_odd
        (n := n) (a := a) (m := t) (by simpa [syracuseNumerator] using hnum) htodd
      have hrestmatch := matches_of_odd_affine_endpoint
        rest t m hposRest hodd htail
      simpa [SyracuseWordMatchesFrom, hstep.2] using
        (show syracuseExponent n = a ∧ SyracuseWordMatchesFrom rest t from
          ⟨hstep.1, hrestmatch⟩)

/--
Exact cylinder theorem for every nonempty word of positive Syracuse
exponents: its entire valuation pattern is equivalent to one congruence.
-/
theorem syracuseWordMatches_iff_exactResidue
    (w : List ℕ) (n : ℕ) (hw : w ≠ [])
    (hpos : ∀ a ∈ w, 0 < a) :
    SyracuseWordMatchesFrom w n ↔
      syracuseWordAffineNumerator w n % syracuseWordExactResidueModulus w = 2 ^ w.sum := by
  constructor
  · intro hmatch
    exact syracuseWordAffine_mod_exactResidueModulus_of_matches
      hmatch (List.length_pos_iff_ne_nil.mpr hw)
  · intro hmod
    obtain ⟨m, hodd, haff⟩ := (exactResidue_iff_odd_endpoint w n).mp hmod
    exact matches_of_odd_affine_endpoint w n m hpos hodd haff

/-- A finite number of complete copies of a phantom exponent word. -/
def repeatPhantomWord (w : PhantomWord) : ℕ → List ℕ
  | 0 => []
  | k + 1 => w.vals ++ repeatPhantomWord w k

theorem repeatPhantomWord_sum (w : PhantomWord) (k : ℕ) :
    (repeatPhantomWord w k).sum = k * w.A := by
  induction k with
  | zero => simp [repeatPhantomWord]
  | succ k ih =>
      simp [repeatPhantomWord, List.sum_append, ih, PhantomWord.A,
        Nat.succ_mul, Nat.add_comm]

theorem repeatPhantomWord_length (w : PhantomWord) (k : ℕ) :
    (repeatPhantomWord w k).length = k * w.length := by
  induction k with
  | zero => simp [repeatPhantomWord]
  | succ k ih =>
      simp [repeatPhantomWord, List.length_append, ih, PhantomWord.length,
        Nat.succ_mul, Nat.add_comm]

private theorem repeatPhantomWord_positive (w : PhantomWord) (k : ℕ) :
    ∀ a ∈ repeatPhantomWord w k, 0 < a := by
  induction k with
  | zero => simp [repeatPhantomWord]
  | succ k ih =>
      intro a ha
      have ha' : a ∈ w.vals ++ repeatPhantomWord w k := by
        simpa [repeatPhantomWord] using ha
      rcases List.mem_append.mp ha' with hleft | hright
      · exact w.positive a hleft
      · exact ih a hright

private theorem repeatPhantomWord_nonempty (w : PhantomWord) (k : ℕ)
    (hk : 0 < k) : repeatPhantomWord w k ≠ [] := by
  cases k with
  | zero => omega
  | succ j =>
      intro h
      have hnil : w.vals ++ repeatPhantomWord w j = [] := by
        simpa [repeatPhantomWord] using h
      exact w.nonempty (List.append_eq_nil_iff.mp hnil).1

/--
For `k > 0` repeated periods, all `k * length` valuations are certified by
one congruence modulo `2 ^ (k * A + 1)`.
-/
theorem repeatPhantomWord_matches_iff_exactResidue
    (w : PhantomWord) (k n : ℕ) (hk : 0 < k) :
    SyracuseWordMatchesFrom (repeatPhantomWord w k) n ↔
      (3 ^ (k * w.length) * n +
          syracuseWordConst (repeatPhantomWord w k)) %
        2 ^ (k * w.A + 1) = 2 ^ (k * w.A) := by
  have h := syracuseWordMatches_iff_exactResidue
    (repeatPhantomWord w k) n
    (repeatPhantomWord_nonempty w k hk)
    (repeatPhantomWord_positive w k)
  simpa [syracuseWordAffineNumerator, syracuseWordExactResidueModulus,
    repeatPhantomWord_sum, repeatPhantomWord_length] using h

end CollatzShadowing
