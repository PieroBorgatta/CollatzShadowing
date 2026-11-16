/-
Exact parity moments and dyadic packing for the shortcut Collatz map.

Exact parity moments, finite packing, and finite geometric sums give a
universal reciprocal budget for every finite injective trajectory.
No asymptotic estimate or external preprint is an input to the proof.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/
import CollatzShadowing.PrefixOptimality
import CollatzShadowing.FiniteOrbitTransfer
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic

namespace CollatzShadowing.OrbitReciprocal

open ShortcutCoverage PrefixOptimality
open scoped BigOperators

/-- A denominator-free affine upper bound, valid also at the zero input. -/
theorem iterate_affine_lt (n N : ℕ) :
    2 ^ N * T^[N] n < 3 ^ J n N * (n + 2 ^ N) := by
  induction N generalizing n with
  | zero => simp [J]
  | succ N ih =>
      have h := ih (T n)
      have htwo : 0 < 2 ^ N := by positivity
      have hthree : 0 < 3 ^ J (T n) N := by positivity
      simp only [Function.iterate_succ_apply, J, pow_add, pow_one]
      by_cases he : n % 2 = 0
      · have ht : 2 * T n = n := by simp only [T, if_pos he]; omega
        rw [he]
        simp only [pow_zero, one_mul]
        nlinarith
      · have ho : n % 2 = 1 := by omega
        have ht : 2 * T n = 3 * n + 1 := by simp only [T, if_neg he]; omega
        rw [ho]
        simp only [pow_one]
        nlinarith

/-- Below the parity modulus every endpoint with m odd steps is < 2*3^m. -/
theorem iterate_lt_two_mul_three_pow {s N : ℕ} (hs : s < 2 ^ N) :
    T^[N] s < 2 * 3 ^ J s N := by
  have h := iterate_affine_lt s N
  have hp : 0 < 2 ^ N := by positivity
  have hq : 0 < 3 ^ J s N := by positivity
  nlinarith

/-- The last exposed bit is complemented by adding the previous modulus. -/
theorem last_bit_complement (s N : ℕ) :
    (T^[N] s) % 2 + (T^[N] (s + 2 ^ N)) % 2 = 1 := by
  have hl := (iterate_lift s N 1).2
  simp only [mul_one] at hl
  rw [hl, Nat.add_mod]
  have hp : 3 ^ J s N % 2 = 1 := by simp [Nat.pow_mod]
  rw [hp]
  have hm := Nat.mod_lt (T^[N] s) (by decide : 0 < 2)
  omega

/-- Pairing the two halves of a parity cylinder gives the Bernoulli moment. -/
theorem parity_moment_pair {R : Type*} [CommSemiring R] (q : R) (s N : ℕ) :
    q ^ J s (N + 1) + q ^ J (s + 2 ^ N) (N + 1) =
      (1 + q) * q ^ J s N := by
  have hp := (iterate_lift s N 1).1
  simp only [mul_one] at hp
  have hb := last_bit_complement s N
  rw [J_succ, J_succ, hp, pow_add, pow_add]
  have hm := Nat.mod_lt (T^[N] s) (by decide : 0 < 2)
  by_cases hz : (T^[N] s) % 2 = 0
  · have ho : (T^[N] (s + 2 ^ N)) % 2 = 1 := by omega
    rw [hz, ho]
    simp only [pow_zero, pow_one, mul_one]
    ring
  · have ho : (T^[N] s) % 2 = 1 := by omega
    have hz' : (T^[N] (s + 2 ^ N)) % 2 = 0 := by omega
    rw [ho, hz']
    simp only [pow_zero, pow_one, mul_one]
    ring

/-- Exact moment identity for all parity classes, with no analytic estimate. -/
theorem parity_moment {R : Type*} [CommSemiring R] (q : R) (N : ℕ) :
    ∑ s ∈ Finset.range (2 ^ N), q ^ J s N = (1 + q) ^ N := by
  induction N with
  | zero => simp [J]
  | succ N ih =>
      rw [pow_succ, show 2 ^ N * 2 = 2 ^ N + 2 ^ N by omega,
        Finset.sum_range_add]
      conv_lhs =>
        rhs
        arg 2
        intro s
        rw [Nat.add_comm]
      rw [← Finset.sum_add_distrib]
      simp_rw [parity_moment_pair]
      rw [← Finset.mul_sum, ih, pow_succ]
      ring

/-- In one dyadic band, a fixed odd-step count has only 2*3^m images.
Only N-step injectivity on this finite set is needed. -/
theorem dyadic_fiber_card_le (A : Finset ℕ) (N m : ℕ)
    (hband : ∀ n ∈ A, 2 ^ N ≤ n ∧ n < 2 ^ (N + 1))
    (hinj : Set.InjOn (T^[N]) (↑A : Set ℕ)) :
    (A.filter (fun n => J (n - 2 ^ N) N = m)).card ≤ 2 * 3 ^ m := by
  let cell := A.filter (fun n => J (n - 2 ^ N) N = m)
  have hcell : ∀ n ∈ cell, n - 2 ^ N < 2 ^ N := by
    intro n hn
    obtain ⟨_, hnlt⟩ := hband n (Finset.mem_filter.mp hn).1
    rw [pow_succ] at hnlt
    omega
  have hmap : Set.MapsTo (fun n => T^[N] (n - 2 ^ N))
      (↑cell : Set ℕ) (↑(Finset.range (2 * 3 ^ m)) : Set ℕ) := by
    intro n hn
    have hc := (Finset.mem_filter.mp hn).2
    simpa only [Finset.mem_coe, Finset.mem_range, hc] using
      iterate_lt_two_mul_three_pow (hcell n hn)
  have hi : Set.InjOn (fun n => T^[N] (n - 2 ^ N)) (↑cell : Set ℕ) := by
    intro a ha b hb hab
    have ham := (Finset.mem_filter.mp ha).2
    have hbm := (Finset.mem_filter.mp hb).2
    have haA := (Finset.mem_filter.mp ha).1
    have hbA := (Finset.mem_filter.mp hb).1
    have hal := (hband a haA).1
    have hbl := (hband b hbA).1
    have hla := (iterate_lift (a - 2 ^ N) N 1).2
    have hlb := (iterate_lift (b - 2 ^ N) N 1).2
    simp only [mul_one, Nat.sub_add_cancel hal, Nat.sub_add_cancel hbl,
      ham, hbm] at hla hlb
    apply hinj haA hbA
    change T^[N] (a - 2 ^ N) = T^[N] (b - 2 ^ N) at hab
    rw [hla, hlb, hab]
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn
    (fun n => T^[N] (n - 2 ^ N)) hmap hi

private theorem sum_two_mul_three_pow (M : ℕ) :
    (∑ m ∈ Finset.range M, 2 * 3 ^ m) + 1 = 3 ^ M := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- Summing the light fibers removes any factor depending on the depth. -/
theorem dyadic_light_card_le (A : Finset ℕ) (N M : ℕ)
    (hband : ∀ n ∈ A, 2 ^ N ≤ n ∧ n < 2 ^ (N + 1))
    (hinj : Set.InjOn (T^[N]) (↑A : Set ℕ)) :
    (A.filter (fun n => J (n - 2 ^ N) N < M)).card < 3 ^ M := by
  have hf := Finset.sum_card_fiberwise_eq_card_filter A (Finset.range M)
    (fun n => J (n - 2 ^ N) N)
  simp only [Finset.mem_range] at hf
  rw [← hf]
  have hsum := Finset.sum_le_sum (s := Finset.range M)
    (fun m _ => dyadic_fiber_card_le A N m hband hinj)
  have hgeom := sum_two_mul_three_pow M
  omega

/-- An exact finite Chernoff bound derived from the parity moment identity. -/
theorem heavy_residue_card_bound (N M : ℕ) :
    ((Finset.range (2 ^ N)).filter (fun s => M ≤ J s N)).card *
      (3 / 2 : ℚ) ^ M ≤ (5 / 2 : ℚ) ^ N := by
  let heavy := (Finset.range (2 ^ N)).filter (fun s => M ≤ J s N)
  have hlower : (heavy.card : ℚ) * (3 / 2 : ℚ) ^ M ≤
      ∑ s ∈ heavy, (3 / 2 : ℚ) ^ J s N := by
    calc
      (heavy.card : ℚ) * (3 / 2 : ℚ) ^ M =
          ∑ _s ∈ heavy, (3 / 2 : ℚ) ^ M := by simp
      _ ≤ ∑ s ∈ heavy, (3 / 2 : ℚ) ^ J s N := by
        apply Finset.sum_le_sum
        intro s hs
        exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 3 / 2)
          (Finset.mem_filter.mp hs).2
  have hupper : (∑ s ∈ heavy, (3 / 2 : ℚ) ^ J s N) ≤
      ∑ s ∈ Finset.range (2 ^ N), (3 / 2 : ℚ) ^ J s N := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro s _ _; positivity
  calc
    _ ≤ ∑ s ∈ Finset.range (2 ^ N), (3 / 2 : ℚ) ^ J s N :=
      hlower.trans hupper
    _ = (5 / 2 : ℚ) ^ N := by
      convert parity_moment (3 / 2 : ℚ) N using 1
      norm_num

/-- Translating one dyadic band gives a subset of the parity representatives. -/
theorem dyadic_heavy_card_bound (A : Finset ℕ) (N M : ℕ)
    (hband : ∀ n ∈ A, 2 ^ N ≤ n ∧ n < 2 ^ (N + 1)) :
    ((A.filter (fun n => M ≤ J (n - 2 ^ N) N)).card : ℚ) *
      (3 / 2 : ℚ) ^ M ≤ (5 / 2 : ℚ) ^ N := by
  let heavy := A.filter (fun n => M ≤ J (n - 2 ^ N) N)
  have hc : heavy.card ≤ ((Finset.range (2 ^ N)).filter (fun s => M ≤ J s N)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n - 2 ^ N)
    · intro n hn
      obtain ⟨hnA, hm⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnlo, hnhi⟩ := hband n hnA
      rw [pow_succ] at hnhi
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hm⟩
      change n - 2 ^ N < 2 ^ N
      omega
    · intro a ha b hb hab
      have hal := (hband a (Finset.mem_filter.mp ha).1).1
      have hbl := (hband b (Finset.mem_filter.mp hb).1).1
      change a - 2 ^ N = b - 2 ^ N at hab
      omega
  have hc' : (heavy.card : ℚ) ≤
      (((Finset.range (2 ^ N)).filter (fun s => M ≤ J s N)).card : ℚ) := by
    exact_mod_cast hc
  exact (mul_le_mul_of_nonneg_right hc' (by positivity)).trans
    (heavy_residue_card_bound N M)

/-- The normalized dyadic estimate, without entropy or a depth factor. -/
theorem dyadic_card_bound (A : Finset ℕ) (N M : ℕ)
    (hband : ∀ n ∈ A, 2 ^ N ≤ n ∧ n < 2 ^ (N + 1))
    (hinj : Set.InjOn (T^[N]) (↑A : Set ℕ)) :
    (A.card : ℚ) / 2 ^ N ≤
      (5 / 4 : ℚ) ^ N * (2 / 3 : ℚ) ^ M + 3 ^ M / 2 ^ N := by
  have hl := dyadic_light_card_le A N M hband hinj
  have hh := dyadic_heavy_card_bound A N M hband
  have hpartition : (A.filter (fun n => J (n - 2 ^ N) N < M)).card +
      (A.filter (fun n => M ≤ J (n - 2 ^ N) N)).card = A.card := by
    simpa only [not_lt] using Finset.card_filter_add_card_filter_not
      (s := A) (p := fun n => J (n - 2 ^ N) N < M)
  have hl' : ((A.filter (fun n => J (n - 2 ^ N) N < M)).card : ℚ) ≤ 3 ^ M := by
    exact_mod_cast Nat.le_of_lt hl
  have hpartition' : ((A.filter (fun n => J (n - 2 ^ N) N < M)).card : ℚ) +
      ((A.filter (fun n => M ≤ J (n - 2 ^ N) N)).card : ℚ) = A.card := by
    exact_mod_cast hpartition
  have hheavy : ((A.filter (fun n => M ≤ J (n - 2 ^ N) N)).card : ℚ) ≤
      (5 / 2 : ℚ) ^ N * (2 / 3 : ℚ) ^ M := by
    have hrec : (3 / 2 : ℚ) ^ M * (2 / 3 : ℚ) ^ M = 1 := by
      rw [← mul_pow]; norm_num
    have hm := mul_le_mul_of_nonneg_right hh (by positivity : (0 : ℚ) ≤ (2 / 3 : ℚ) ^ M)
    simpa only [mul_assoc, hrec, mul_one] using hm
  have hsum : (A.card : ℚ) ≤ 3 ^ M + (5 / 2 : ℚ) ^ N * (2 / 3 : ℚ) ^ M := by
    linarith
  have hp : (0 : ℚ) < 2 ^ N := by positivity
  apply (div_le_iff₀ hp).mpr
  have hid : ((5 / 4 : ℚ) ^ N * (2 / 3 : ℚ) ^ M + 3 ^ M / 2 ^ N) * 2 ^ N =
      3 ^ M + (5 / 2 : ℚ) ^ N * (2 / 3 : ℚ) ^ M := by
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hp)]
    have heq : (5 / 4 : ℚ) ^ N * 2 ^ N = (5 / 2 : ℚ) ^ N := by
      rw [← mul_pow]; norm_num
    rw [show (5 / 4 : ℚ) ^ N * (2 / 3 : ℚ) ^ M * 2 ^ N =
      ((5 / 4 : ℚ) ^ N * 2 ^ N) * (2 / 3 : ℚ) ^ M by ring, heq]
    ring
  simpa only [hid] using hsum

/-- The actual Collatz finite-orbit estimate, with its terminal error. -/
theorem finite_orbit_dyadic_card_bound (u length N M : ℕ)
    (hinj : ∀ i < length, ∀ j < length, T^[i] u = T^[j] u → i = j) :
    (((FiniteOrbitTransfer.segment T u length).filter
      (fun n => n ∈ Finset.Ico (2 ^ N) (2 ^ (N + 1)))).card : ℚ) / 2 ^ N ≤
      (N : ℚ) / 2 ^ N +
      (5 / 4 : ℚ) ^ N * (2 / 3 : ℚ) ^ M + 3 ^ M / 2 ^ N := by
  let W := Finset.Ico (2 ^ N) (2 ^ (N + 1))
  let P := (FiniteOrbitTransfer.segment T u (length - N)).filter (fun n => n ∈ W)
  have hband : ∀ n ∈ P, 2 ^ N ≤ n ∧ n < 2 ^ (N + 1) := by
    intro n hn
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hn).2
  have hp : Set.InjOn (T^[N]) (↑P : Set ℕ) := by
    apply (FiniteOrbitTransfer.iterate_injOn_prefix T u length N hinj).mono
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hbound := dyadic_card_bound P N M hband hp
  have hcard := FiniteOrbitTransfer.window_card_le_prefix_add T u length N W
  have hcard' : (((FiniteOrbitTransfer.segment T u length).filter (fun n => n ∈ W)).card : ℚ) ≤
      (P.card : ℚ) + N := by exact_mod_cast hcard
  have hpow : (0 : ℚ) < 2 ^ N := by positivity
  have hdiv := (div_le_div_iff_of_pos_right hpow).mpr hcard'
  dsimp only [W] at hdiv
  rw [add_div] at hdiv
  linarith [hdiv, hbound]

/-- Rational envelope for the heavy parity classes. -/
def heavyEnvelope (j : ℕ) : ℚ := (5 / 4 : ℚ) ^ j * (2 / 3 : ℚ) ^ (3 * j / 5)

/-- Rational envelope for the light parity classes. -/
def lightEnvelope (j : ℕ) : ℚ := (3 : ℚ) ^ (3 * j / 5) / 2 ^ j

private theorem heavyEnvelope_block (r s : ℕ) :
    heavyEnvelope (5 * r + s) = (3125 / 3456 : ℚ) ^ r * heavyEnvelope s := by
  have he : 3 * (5 * r + s) / 5 = 3 * r + 3 * s / 5 := by omega
  simp only [heavyEnvelope, he, pow_add, pow_mul]
  have hb : (5 / 4 : ℚ) ^ 5 * (2 / 3 : ℚ) ^ 3 = 3125 / 3456 := by norm_num
  rw [← hb, mul_pow]
  ring

private theorem lightEnvelope_block (r s : ℕ) :
    lightEnvelope (5 * r + s) = (27 / 32 : ℚ) ^ r * lightEnvelope s := by
  have he : 3 * (5 * r + s) / 5 = 3 * r + 3 * s / 5 := by omega
  simp only [lightEnvelope, he, pow_add, pow_mul]
  have hb : (3 : ℚ) ^ 3 / 2 ^ 5 = 27 / 32 := by norm_num
  rw [← hb, div_pow]
  ring

private theorem sum_blocks (f : ℕ → ℚ) (q : ℚ)
    (hf : ∀ r s, f (5 * r + s) = q ^ r * f s) (R : ℕ) :
    ∑ j ∈ Finset.range (5 * R), f j =
      (∑ s ∈ Finset.range 5, f s) * ∑ r ∈ Finset.range R, q ^ r := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [show 5 * (R + 1) = 5 * R + 5 by omega, Finset.sum_range_add, ih]
      simp_rw [hf]
      rw [← Finset.mul_sum, Finset.sum_range_succ (f := fun r => q ^ r)]
      ring

private theorem geom_sum_rat_le {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q < 1) (R : ℕ) :
    ∑ r ∈ Finset.range R, q ^ r ≤ 1 / (1 - q) := by
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  rw [geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hq0 R)

/-- A finite rational geometric sum certifies the heavy envelope budget. -/
theorem heavyEnvelope_sum_le (R : ℕ) :
    ∑ j ∈ Finset.range (5 * R), heavyEnvelope j ≤ (3271 / 576 : ℚ) / (1 - 3125 / 3456) := by
  rw [sum_blocks heavyEnvelope (3125 / 3456) heavyEnvelope_block R]
  have hs : (∑ s ∈ Finset.range 5, heavyEnvelope s) = (3271 / 576 : ℚ) := by
    norm_num [heavyEnvelope, Finset.sum_range_succ]
  rw [hs]
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left (geom_sum_rat_le (q := 3125 / 3456) (by norm_num) (by norm_num) R)
      (by norm_num : (0 : ℚ) ≤ 3271 / 576)

/-- A finite rational geometric sum certifies the light envelope budget. -/
theorem lightEnvelope_sum_le (R : ℕ) :
    ∑ j ∈ Finset.range (5 * R), lightEnvelope j ≤ (51 / 16 : ℚ) / (1 - 27 / 32) := by
  rw [sum_blocks lightEnvelope (27 / 32) lightEnvelope_block R]
  have hs : (∑ s ∈ Finset.range 5, lightEnvelope s) = (51 / 16 : ℚ) := by
    norm_num [lightEnvelope, Finset.sum_range_succ]
  rw [hs]
  simpa only [one_div, div_eq_mul_inv, one_mul] using
    mul_le_mul_of_nonneg_left (geom_sum_rat_le (q := 27 / 32) (by norm_num) (by norm_num) R)
      (by norm_num : (0 : ℚ) ≤ 51 / 16)

private theorem terminal_budget_identity (N : ℕ) :
    (∑ j ∈ Finset.range N, (j : ℚ) / 2 ^ j) + (2 * N + 2 : ℚ) / 2 ^ N = 2 := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Finset.sum_range_succ, pow_succ]
      push_cast
      have hp : (2 : ℚ) ^ N ≠ 0 := by positivity
      field_simp [hp] at ih ⊢
      nlinarith

/-- The temporal truncations have a total reciprocal budget at most two. -/
theorem terminal_budget_sum_le (N : ℕ) :
    ∑ j ∈ Finset.range N, (j : ℚ) / 2 ^ j ≤ 2 := by
  have h := terminal_budget_identity N
  have hp : (0 : ℚ) ≤ (2 * N + 2 : ℚ) / 2 ^ N := by positivity
  linarith

/-- A finite positive set is counted by its dyadic bands with the correct
reciprocal weights. The upper cutoff is finite and explicit. -/
theorem reciprocal_sum_le_band_sum (A : Finset ℕ) (K : ℕ)
    (hpos : ∀ n ∈ A, 0 < n) (hcut : ∀ n ∈ A, n < 2 ^ K) :
    ∑ n ∈ A, (1 : ℚ) / n ≤
      ∑ j ∈ Finset.range K,
        ((A.filter (fun n => n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)))).card : ℚ) / 2 ^ j := by
  have hmap : ∀ n ∈ A, Nat.log 2 n ∈ Finset.range K := by
    intro n hn
    exact Finset.mem_range.mpr
      ((Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (ne_of_gt (hpos n hn))).mpr (hcut n hn))
  have hpoint : (∑ n ∈ A, (1 : ℚ) / n) ≤
      ∑ n ∈ A, (1 : ℚ) / 2 ^ Nat.log 2 n := by
    apply Finset.sum_le_sum
    intro n hn
    apply one_div_le_one_div_of_le (by positivity : (0 : ℚ) < 2 ^ Nat.log 2 n)
    exact_mod_cast Nat.pow_log_le_self 2 (ne_of_gt (hpos n hn))
  have hfilter (j : ℕ) : A.filter (fun n => Nat.log 2 n = j) =
      A.filter (fun n => n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1))) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨hn, hj⟩
      refine ⟨hn, ?_⟩
      rw [← hj]
      exact ⟨Nat.pow_log_le_self 2 (ne_of_gt (hpos n hn)),
        Nat.lt_pow_succ_log_self (by decide : 1 < 2) n⟩
    · rintro ⟨hn, hlo, hhi⟩
      exact ⟨hn, Nat.log_eq_of_pow_le_of_lt_pow hlo hhi⟩
  have hsum : (∑ n ∈ A, (1 : ℚ) / 2 ^ Nat.log 2 n) =
      ∑ j ∈ Finset.range K,
        ((A.filter (fun n => n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)))).card : ℚ) / 2 ^ j := by
    rw [← Finset.sum_fiberwise_of_maps_to' hmap (fun j => (1 : ℚ) / 2 ^ j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [hfilter j]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  exact hpoint.trans_eq hsum

/-- Every state in a finite shortcut segment started at a positive source is
positive, including the terminal state when it is present. -/
theorem segment_pos {u : ℕ} (hu : 0 < u) (length : ℕ) :
    ∀ n ∈ FiniteOrbitTransfer.segment T u length, 0 < n := by
  have hall (i : ℕ) : 0 < T^[i] u := by
    induction i with
    | zero => simpa using hu
    | succ i ih =>
        rw [Function.iterate_succ_apply']
        exact T_pos ih
  intro n hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact hall i

private theorem band_zero_card_le (A : Finset ℕ) :
    ((A.filter (fun n => n ∈ Finset.Ico (2 ^ 0) (2 ^ (0 + 1)))).card : ℚ) / 2 ^ 0 ≤ 1 := by
  have hsub : A.filter (fun n => n ∈ Finset.Ico (2 ^ 0) (2 ^ (0 + 1))) ⊆ {1} := by
    intro n hn
    have h := Finset.mem_Ico.mp (Finset.mem_filter.mp hn).2
    norm_num at h
    simp only [Finset.mem_singleton]
    omega
  have hc := Finset.card_le_card hsub
  norm_num only [Finset.card_singleton] at hc
  norm_num only [pow_zero, div_one]
  exact_mod_cast hc

/-- A universal reciprocal budget for every finite injective shortcut
trajectory. This theorem has no convergence, window estimate, entropy,
external preprint, or infinite-series hypothesis. -/
theorem finite_orbit_reciprocal_sum_le (u length : ℕ) (hu : 0 < u)
    (hinj : ∀ i < length, ∀ j < length, T^[i] u = T^[j] u → i = j) :
    ∑ n ∈ FiniteOrbitTransfer.segment T u length, (1 : ℚ) / n ≤
      (133547 / 1655 : ℚ) := by
  let A := FiniteOrbitTransfer.segment T u length
  let R := A.sup id + 1
  let K := 5 * R
  let F := fun j => ((A.filter
    (fun n => n ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)))).card : ℚ) / 2 ^ j
  let G := fun j : ℕ => (j : ℚ) / 2 ^ j + heavyEnvelope j + lightEnvelope j
  have hR : 0 < R := by dsimp [R]; omega
  have hK : 0 < K := by dsimp [K]; omega
  have hcut : ∀ n ∈ A, n < 2 ^ K := by
    intro n hn
    have hnle : n ≤ A.sup id := Finset.le_sup (f := id) hn
    have hnK : n ≤ K := by dsimp [K, R]; omega
    have hpowK : K < 2 ^ K := Nat.lt_two_pow_self
    exact lt_of_le_of_lt hnK hpowK
  have hrec : (∑ n ∈ A, (1 : ℚ) / n) ≤ ∑ j ∈ Finset.range K, F j :=
    reciprocal_sum_le_band_sum A K (segment_pos hu length) hcut
  have hbound (j : ℕ) : F j ≤ G j := by
    exact finite_orbit_dyadic_card_bound u length j (3 * j / 5) hinj
  have hzero : F 0 ≤ 1 := band_zero_card_le A
  have hdelta : (∑ j ∈ Finset.range K, if j = 0 then (1 : ℚ) else 0) = 1 := by
    simp [hK]
  have hsum : (∑ j ∈ Finset.range K, F j) + 1 ≤ ∑ j ∈ Finset.range K, G j := by
    have h := Finset.sum_le_sum (s := Finset.range K)
      (f := fun j => F j + if j = 0 then (1 : ℚ) else 0) (g := G) (fun j _ => by
        by_cases hj : j = 0
        · subst j
          norm_num [G, heavyEnvelope, lightEnvelope] at *
          linarith
        · simpa only [if_neg hj, add_zero] using hbound j)
    simpa only [Finset.sum_add_distrib, hdelta] using h
  have hG : (∑ j ∈ Finset.range K, G j) =
      (∑ j ∈ Finset.range K, (j : ℚ) / 2 ^ j) +
      (∑ j ∈ Finset.range K, heavyEnvelope j) +
      ∑ j ∈ Finset.range K, lightEnvelope j := by
    simp only [G, Finset.sum_add_distrib]
  have ht := terminal_budget_sum_le K
  have hh := heavyEnvelope_sum_le R
  have hl := lightEnvelope_sum_le R
  change (∑ j ∈ Finset.range K, heavyEnvelope j) ≤ _ at hh
  change (∑ j ∈ Finset.range K, lightEnvelope j) ≤ _ at hl
  norm_num at hh hl
  rw [hG] at hsum
  linarith

/-- A convenient integral version of the universal reciprocal budget. -/
theorem finite_orbit_reciprocal_sum_lt_eighty_one (u length : ℕ) (hu : 0 < u)
    (hinj : ∀ i < length, ∀ j < length, T^[i] u = T^[j] u → i = j) :
    ∑ n ∈ FiniteOrbitTransfer.segment T u length, (1 : ℚ) / n < 81 := by
  exact (finite_orbit_reciprocal_sum_le u length hu hinj).trans_lt (by norm_num)

/-- The same universal estimate in real scalars for analytic applications. -/
theorem finite_orbit_reciprocal_sum_real_lt_eighty_one (u length : ℕ) (hu : 0 < u)
    (hinj : ∀ i < length, ∀ j < length, T^[i] u = T^[j] u → i = j) :
    ∑ n ∈ FiniteOrbitTransfer.segment T u length, (1 : ℝ) / n < 81 := by
  have h := finite_orbit_reciprocal_sum_lt_eighty_one u length hu hinj
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).2 h

end CollatzShadowing.OrbitReciprocal
