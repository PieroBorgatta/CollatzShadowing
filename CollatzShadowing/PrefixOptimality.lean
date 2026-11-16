/-
Exact optimality of certificates based only on a dyadic input prefix.

The second input is always the actual polynomial f_v(x), and every counted
bit is the parity of an actual iterate of the shortcut Collatz map T.
The positive witness is constructed by arithmetic lifts of x, not by
postulating realizability of binary words. No assertion about the exact
tower source, convergence, or binomial multiplicities is made here.

AI-assisted development: Codex with Piero Borgatta, 2026-09-26.
Specification: notes/post_v6_renewal_2026-09-26/PROOF_IT.md, sections 2-4.
-/
import CollatzShadowing.ShortcutCoverage

namespace CollatzShadowing.PrefixOptimality

open ShortcutCoverage

/-- Number of odd states among the first `k` shortcut steps from `x`. -/
def J (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => x % 2 + J (T x) k

/-- The exact relation between adjacent normalized tower sources. -/
def f (v x : ℕ) : ℕ := x + 2 ^ (v + 2) * x ^ 2

theorem J_succ (x k : ℕ) : J x (k + 1) = J x k + (T^[k] x) % 2 := by
  induction k generalizing x with
  | zero => simp [J]
  | succ k ih =>
      change x % 2 + J (T x) (k + 1) =
        (x % 2 + J (T x) k) + (T^[k + 1] x) % 2
      rw [ih, Function.iterate_succ_apply]
      omega

theorem J_le (x k : ℕ) : J x k ≤ k := by
  induction k generalizing x with
  | zero => simp [J]
  | succ k ih =>
      have := ih (T x)
      have := Nat.mod_lt x (by decide : 0 < 2)
      simp only [J]
      omega

/-- Exact effect of adding a multiple of 2^(k+1) before one shortcut step. -/
private theorem T_lift (a k t : ℕ) :
    T (a + 2 ^ (k + 1) * t) = T a + 2 ^ k * (3 ^ (a % 2) * t) := by
  have hp : 2 ^ (k + 1) * t = 2 * (2 ^ k * t) := by rw [pow_succ]; ring
  have hm : (a + 2 ^ (k + 1) * t) % 2 = a % 2 := by rw [hp]; omega
  unfold T
  rw [hm]
  split_ifs with ha
  · rw [ha]
    simp only [pow_zero, one_mul]
    rw [hp]
    omega
  · have ho : a % 2 = 1 := by omega
    rw [ho]
    simp only [pow_one]
    rw [hp, show 2 ^ k * (3 * t) = 3 * (2 ^ k * t) by ring]
    omega

/-- Arithmetic lift identity, including preservation of every counted prefix.
It holds for all natural inputs, including zero. -/
theorem iterate_lift (a k t : ℕ) :
    J (a + 2 ^ k * t) k = J a k ∧
    T^[k] (a + 2 ^ k * t) = T^[k] a + 3 ^ (J a k) * t := by
  induction k generalizing a t with
  | zero => simp [J]
  | succ k ih =>
      have hm : (a + 2 ^ (k + 1) * t) % 2 = a % 2 := by
        simp [pow_succ, Nat.add_mod, Nat.mul_mod]
      have h := ih (T a) (3 ^ (a % 2) * t)
      constructor
      · simp only [J, hm, T_lift, h.1]
      · rw [Function.iterate_succ_apply, T_lift, h.2,
          Function.iterate_succ_apply]
        simp only [J, pow_add]
        ring

/-- Congruent inputs have equal parity counts up to the exposed precision. -/
theorem J_eq_of_modEq {x y k : ℕ} (h : x ≡ y [MOD 2 ^ k]) : J x k = J y k := by
  have hx := (iterate_lift (x % 2 ^ k) k (x / 2 ^ k)).1
  have hy := (iterate_lift (y % 2 ^ k) k (y / 2 ^ k)).1
  rw [Nat.mod_add_div] at hx hy
  exact hx.trans ((congrArg (fun a => J a k) h).trans hy.symm)

theorem f_modEq {v x y k : ℕ} (h : x ≡ y [MOD 2 ^ k]) :
    f v x ≡ f v y [MOD 2 ^ k] := by
  exact h.add ((h.pow 2).mul_left (2 ^ (v + 2)))

/-- Exact polynomial identity behind the one-bit extension construction. -/
theorem f_lift (v x k : ℕ) :
    f v (x + 2 ^ k) = f v x + 2 ^ k * (1 + 2 ^ (v + 2) * (2 * x + 2 ^ k)) := by
  unfold f
  ring

/-- The last still-undetermined parity flips under the next input lift. -/
theorem f_lift_flips_parity (v x k : ℕ) :
    (T^[k] (f v (x + 2 ^ k))) % 2 ≠ (T^[k] (f v x)) % 2 := by
  rw [f_lift, (iterate_lift _ _ _).2]
  have hcoeff : (1 + 2 ^ (v + 2) * (2 * x + 2 ^ k)) % 2 = 1 := by
    simp [pow_succ, Nat.add_mod, Nat.mul_mod]
  have hpow : 3 ^ J (f v x) k % 2 = 1 := by simp [Nat.pow_mod]
  rw [Nat.add_mod, Nat.mul_mod, hpow, hcoeff]
  omega

/-- Every additional step contributes at most one odd state. -/
theorem J_add_le (x M d : ℕ) : J x (M + d) ≤ J x M + d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, J_succ]
      have := Nat.mod_lt (T^[M + d] x) (by decide : 0 < 2)
      omega

/-- Arithmetic realization of the all-one upper suffix, with a positive input
in the prescribed dyadic class. The equality uses the exact polynomial `f`. -/
theorem all_one_suffix_attained (v Q M K : ℕ) (hQ : 0 < Q) (hMK : M ≤ K) :
    ∃ x : ℕ, 0 < x ∧ x ≡ Q [MOD 2 ^ M] ∧
      J (f v x) K = J (f v Q) M + (K - M) := by
  induction K, hMK using Nat.le_induction with
  | base => exact ⟨Q, hQ, Nat.ModEq.refl _, by simp⟩
  | succ k hMk ih =>
      obtain ⟨x, hx, hmod, hcount⟩ := ih
      by_cases hodd : (T^[k] (f v x)) % 2 = 1
      · refine ⟨x, hx, hmod, ?_⟩
        rw [J_succ, hcount, hodd]
        omega
      · have hflip := f_lift_flips_parity v x k
        have hone : (T^[k] (f v (x + 2 ^ k))) % 2 = 1 := by omega
        have hpres : J (f v (x + 2 ^ k)) k = J (f v x) k := by
          rw [f_lift]
          exact (iterate_lift _ _ _).1
        have hmodlift : x + 2 ^ k ≡ x [MOD 2 ^ M] := by
          have hd : 2 ^ M ∣ 2 ^ k := pow_dvd_pow 2 hMk
          change (x + 2 ^ k) % 2 ^ M = x % 2 ^ M
          simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
        refine ⟨x + 2 ^ k, lt_of_lt_of_le hx (Nat.le_add_right _ _), hmodlift.trans hmod, ?_⟩
        rw [J_succ, hpres, hcount, hone]
        omega

/-- Signed defect, avoiding truncated subtraction of natural counts. -/
def defect (v H K x : ℕ) : ℤ := (J (f v x) K : ℤ) - 2 * (J x H : ℤ)

/-- The maximum compatible with the exposed input prefix. -/
def prefixMaximum (v Q H M K : ℕ) : ℤ :=
  (J (f v Q) M : ℤ) + (K - M : ℕ) - 2 * (J Q H : ℤ)

theorem defect_le_prefixMaximum {v Q H M K x : ℕ}
    (hHM : H ≤ M) (hMK : M ≤ K) (hx : x ≡ Q [MOD 2 ^ M]) :
    defect v H K x ≤ prefixMaximum v Q H M K := by
  have hlower : J x H = J Q H :=
    J_eq_of_modEq (hx.of_dvd (pow_dvd_pow 2 hHM))
  have hupper : J (f v x) M = J (f v Q) M := J_eq_of_modEq (f_modEq hx)
  have hbound := J_add_le (f v x) M (K - M)
  rw [Nat.add_sub_of_le hMK, hupper] at hbound
  unfold defect prefixMaximum
  rw [hlower]
  exact sub_le_sub_right (by exact_mod_cast hbound) _

/-- Exact maximum theorem: the bound holds throughout the dyadic information
class and is attained by an actual positive natural input. -/
theorem prefixMaximum_exact (v Q H M K : ℕ)
    (hQ : 0 < Q) (hHM : H ≤ M) (hMK : M ≤ K) :
    (∀ x : ℕ, 0 < x → x ≡ Q [MOD 2 ^ M] →
      defect v H K x ≤ prefixMaximum v Q H M K) ∧
    (∃ x : ℕ, 0 < x ∧ x ≡ Q [MOD 2 ^ M] ∧
      defect v H K x = prefixMaximum v Q H M K) := by
  constructor
  · intro x _ hx
    exact defect_le_prefixMaximum hHM hMK hx
  · obtain ⟨x, hx, hmod, hcount⟩ := all_one_suffix_attained v Q M K hQ hMK
    have hlower := J_eq_of_modEq (hmod.of_dvd (pow_dvd_pow 2 hHM))
    refine ⟨x, hx, hmod, ?_⟩
    unfold defect prefixMaximum
    rw [hcount, hlower, Nat.cast_add]

/-- A proposed integer threshold is certified exactly when it bounds the
explicit attainable maximum; the universal quantifier is over actual inputs. -/
theorem certificate_iff_maximum_le (v Q H M K : ℕ) (g : ℤ)
    (hQ : 0 < Q) (hHM : H ≤ M) (hMK : M ≤ K) :
    (∀ x : ℕ, 0 < x → x ≡ Q [MOD 2 ^ M] → defect v H K x ≤ g) ↔
      prefixMaximum v Q H M K ≤ g := by
  obtain ⟨hbound, x, hx, hmod, hmax⟩ := prefixMaximum_exact v Q H M K hQ hHM hMK
  constructor
  · intro h
    rw [← hmax]
    exact h x hx hmod
  · intro h x hx hmod
    exact (hbound x hx hmod).trans h

/-- Zeros actually observed in the upper prefix of length `M`. -/
def observedZeros (v Q M : ℕ) : ℕ := M - J (f v Q) M

theorem prefixMaximum_eq_sub_zeros {v Q H M K : ℕ} (hMK : M ≤ K) :
    prefixMaximum v Q H M K = (K : ℤ) - 2 * (J Q H : ℤ) - observedZeros v Q M := by
  have hJ := J_le (f v Q) M
  unfold prefixMaximum observedZeros
  rw [Nat.cast_sub hMK, Nat.cast_sub hJ]
  ring

/-- The exact stopping rule: enough upper zeros have already been observed.
This includes nonpositive thresholds and the degenerate horizons M=H=0. -/
theorem certificate_iff_zeros (v Q H M K : ℕ) (g : ℤ)
    (hQ : 0 < Q) (hHM : H ≤ M) (hMK : M ≤ K) :
    (∀ x : ℕ, 0 < x → x ≡ Q [MOD 2 ^ M] → defect v H K x ≤ g) ↔
      (K : ℤ) - 2 * (J Q H : ℤ) - g ≤ (observedZeros v Q M : ℤ) := by
  rw [certificate_iff_maximum_le v Q H M K g hQ hHM hMK,
    prefixMaximum_eq_sub_zeros hMK]
  omega

/-- Before the zero threshold, a positive arithmetically realized input
violates the claimed certificate while preserving the exact relation f_v. -/
theorem counterexample_before_threshold (v Q H M K : ℕ) (g : ℤ)
    (hQ : 0 < Q) (hHM : H ≤ M) (hMK : M ≤ K)
    (hshort : (observedZeros v Q M : ℤ) < (K : ℤ) - 2 * (J Q H : ℤ) - g) :
    ∃ x : ℕ, 0 < x ∧ x ≡ Q [MOD 2 ^ M] ∧ g < defect v H K x := by
  obtain ⟨x, hx, hmod, heq⟩ := (prefixMaximum_exact v Q H M K hQ hHM hMK).2
  refine ⟨x, hx, hmod, ?_⟩
  rw [heq, prefixMaximum_eq_sub_zeros hMK]
  omega

/-- The excess over the actual defect is exactly the number of upper zeros
that remain unobserved, expressed without truncated integer subtraction. -/
theorem prefixMaximum_eq_actual_add_remaining_zeros {v Q H M K : ℕ}
    (hMK : M ≤ K) :
    prefixMaximum v Q H M K = defect v H K Q +
      (observedZeros v Q K : ℤ) - (observedZeros v Q M : ℤ) := by
  rw [prefixMaximum_eq_sub_zeros hMK]
  unfold defect observedZeros
  rw [Nat.cast_sub (J_le (f v Q) K)]
  ring

/-- Some admissible precision certifies the bound iff the actual source
satisfies it. This is a characterization, not an estimate of that source. -/
theorem exists_certifying_precision_iff (v Q H K : ℕ) (g : ℤ)
    (hQ : 0 < Q) (hHK : H ≤ K) :
    (∃ M : ℕ, H ≤ M ∧ M ≤ K ∧
      ∀ x : ℕ, 0 < x → x ≡ Q [MOD 2 ^ M] → defect v H K x ≤ g) ↔
      defect v H K Q ≤ g := by
  constructor
  · rintro ⟨M, _, _, h⟩
    exact h Q hQ (Nat.ModEq.refl _)
  · intro h
    refine ⟨K, hHK, le_refl _, ?_⟩
    apply (certificate_iff_maximum_le v Q H K K g hQ hHK (le_refl _)).mpr
    simpa [prefixMaximum, defect] using h

end CollatzShadowing.PrefixOptimality
