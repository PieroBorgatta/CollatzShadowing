/-
Finite weak bridge lemmas for Phase 10.

These lemmas are deliberately independent of the Collatz-specific trace
machinery.  They formalize the elementary row-source estimate used by the
A0 weak averaged program:

  average row-L1 drift controls the finite `ell_infty -> L1` error.

This is not a Gate-10.B proof and does not construct an infinite operator.
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

namespace CollatzShadowing
namespace WeakBridge

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Row-source action of a finite real kernel on an observable. -/
def rowAction (K : ι → κ → ℝ) (f : κ → ℝ) (i : ι) : ℝ :=
  ∑ j, K i j * f j

/-- Row `L1` distance between two finite kernels. -/
def rowL1 (K L : ι → κ → ℝ) (i : ι) : ℝ :=
  ∑ j, |K i j - L i j|

/-- Weighted average row `L1` distance. -/
def weightedRowL1 (μ : ι → ℝ) (K L : ι → κ → ℝ) : ℝ :=
  ∑ i, μ i * rowL1 K L i

theorem rowAction_sub_eq_sum (K L : ι → κ → ℝ) (f : κ → ℝ) (i : ι) :
    rowAction K f i - rowAction L f i =
      ∑ j, (K i j - L i j) * f j := by
  simp [rowAction, Finset.sum_sub_distrib, sub_mul]

/--
Finite row estimate: if `|f| <= C`, then one source row is controlled by
the row `L1` distance times `C`.
-/
theorem rowAction_diff_le
    (K L : ι → κ → ℝ) (f : κ → ℝ) (C : ℝ)
    (hf : ∀ j, |f j| ≤ C)
    (i : ι) :
    |rowAction K f i - rowAction L f i| ≤ C * rowL1 K L i := by
  rw [rowAction_sub_eq_sum]
  calc
    |∑ j, (K i j - L i j) * f j|
        ≤ ∑ j, |(K i j - L i j) * f j| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |K i j - L i j| * |f j| := by
          simp [abs_mul]
    _ ≤ ∑ j, |K i j - L i j| * C := by
          exact Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hf j) (abs_nonneg _)
    _ = C * rowL1 K L i := by
          rw [rowL1, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring

/--
Finite weak bridge: average row `L1` drift controls the weighted `L1`
error of the row-source action on observables bounded by `C`.
-/
theorem weighted_action_diff_le
    (μ : ι → ℝ) (K L : ι → κ → ℝ) (f : κ → ℝ) (C : ℝ)
    (hμ : ∀ i, 0 ≤ μ i)
    (hf : ∀ j, |f j| ≤ C) :
    ∑ i, μ i * |rowAction K f i - rowAction L f i|
      ≤ C * weightedRowL1 μ K L := by
  calc
    ∑ i, μ i * |rowAction K f i - rowAction L f i|
        ≤ ∑ i, μ i * (C * rowL1 K L i) := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left
              (rowAction_diff_le K L f C hf i)
              (hμ i)
    _ = C * weightedRowL1 μ K L := by
          rw [weightedRowL1, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

namespace FiniteSplit

variable {ι : Type*} [Fintype ι]

/-- Weighted contribution of a predicate-selected finite subpopulation. -/
def weightedSubsum (μ d : ι → ℝ) (P : ι → Prop) [DecidablePred P] : ℝ :=
  (Finset.univ.filter P).sum fun i => μ i * d i

/-- Weighted mass of a predicate-selected finite subpopulation. -/
def weightedSubmass (μ : ι → ℝ) (P : ι → Prop) [DecidablePred P] : ℝ :=
  (Finset.univ.filter P).sum μ

/--
Finite low/tail split for a nonnegative weighted average.

If `High` is the tail predicate and `d` is bounded by `B` on the tail,
then the full weighted sum is bounded by the exact low contribution plus
`B` times the high-tail mass.  This is a purely finite lemma; any
Collatz meaning must be supplied by separate identifications of `High`,
`d`, `μ`, and `B`.
-/
theorem weighted_sum_le_low_plus_tail
    (μ d : ι → ℝ) (High : ι → Prop) [DecidablePred High] (B : ℝ)
    (hμ : ∀ i, 0 ≤ μ i)
    (hdHigh : ∀ i, High i → d i ≤ B) :
    (∑ i, μ i * d i)
      ≤ weightedSubsum μ d (fun i => ¬ High i)
        + B * weightedSubmass μ High := by
  classical
  let low : Finset ι := Finset.univ.filter fun i => ¬ High i
  let high : Finset ι := Finset.univ.filter High
  have hdisj : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro i hil hih
    have hil' : ¬ High i := by
      simpa [low] using hil
    have hih' : High i := by
      simpa [high] using hih
    exact hil' hih'
  have hunion : low ∪ high = Finset.univ := by
    ext i
    by_cases hi : High i
    · simp [low, high, hi]
    · simp [low, high, hi]
  have htail :
      high.sum (fun i => μ i * d i) ≤ high.sum (fun i => μ i * B) := by
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left
        (hdHigh i (by simpa [high] using hi))
        (hμ i)
  calc
    (∑ i, μ i * d i)
        = (low ∪ high).sum (fun i => μ i * d i) := by
          rw [hunion]
    _ = low.sum (fun i => μ i * d i) + high.sum (fun i => μ i * d i) := by
          exact Finset.sum_union hdisj
    _ ≤ low.sum (fun i => μ i * d i) + high.sum (fun i => μ i * B) := by
          exact add_le_add (le_refl _) htail
    _ = low.sum (fun i => μ i * d i) + B * high.sum μ := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = weightedSubsum μ d (fun i => ¬ High i)
        + B * weightedSubmass μ High := by
          unfold weightedSubsum weightedSubmass
          simp [low, high]

/-- Dyadic return weight attached to a nonnegative bit-length jump. -/
noncomputable def dyadicWeight (δ : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ δ

theorem dyadicWeight_nonneg (δ : ℕ) : 0 ≤ dyadicWeight δ := by
  unfold dyadicWeight
  positivity

theorem dyadicWeight_le_one (δ : ℕ) : dyadicWeight δ ≤ 1 := by
  unfold dyadicWeight
  induction δ with
  | zero =>
      norm_num
  | succ δ ih =>
      rw [pow_succ]
      calc
        ((1 : ℝ) / 2) ^ δ * ((1 : ℝ) / 2)
            ≤ 1 * ((1 : ℝ) / 2) := by
              exact mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ 1 := by norm_num

theorem abs_dyadicWeight_sub_le_one (δ₁ δ₂ : ℕ) :
    |dyadicWeight δ₁ - dyadicWeight δ₂| ≤ 1 := by
  have h1_nonneg := dyadicWeight_nonneg δ₁
  have h2_nonneg := dyadicWeight_nonneg δ₂
  have h1_le := dyadicWeight_le_one δ₁
  have h2_le := dyadicWeight_le_one δ₂
  rw [abs_sub_le_iff]
  constructor <;> nlinarith

/--
Finite boundary estimate for `delta_only` weight changes.

If two dyadic return weights have the same `delta` away from a boundary
predicate, then the weighted average of their pointwise difference is
bounded by the boundary mass.  This is the Lean bookkeeping counterpart
of the Phase-10 A0 reduction: the remaining `delta_only` term is harmless
once its archimedean boundary has vanishing mass.
-/
theorem weighted_dyadic_delta_boundary_le
    (μ : ι → ℝ) (δ₁ δ₂ : ι → ℕ)
    (Boundary : ι → Prop) [DecidablePred Boundary]
    (hμ : ∀ i, 0 ≤ μ i)
    (hδ : ∀ i, ¬ Boundary i → δ₁ i = δ₂ i) :
    (∑ i, μ i * |dyadicWeight (δ₁ i) - dyadicWeight (δ₂ i)|)
      ≤ weightedSubmass μ Boundary := by
  classical
  let d : ι → ℝ := fun i => |dyadicWeight (δ₁ i) - dyadicWeight (δ₂ i)|
  have hsplit :
      (∑ i, μ i * d i)
        ≤ weightedSubsum μ d (fun i => ¬ Boundary i)
          + (1 : ℝ) * weightedSubmass μ Boundary := by
    exact weighted_sum_le_low_plus_tail μ d Boundary 1 hμ
      (fun i _ => abs_dyadicWeight_sub_le_one (δ₁ i) (δ₂ i))
  have hlow_zero :
      weightedSubsum μ d (fun i => ¬ Boundary i) = 0 := by
    unfold weightedSubsum
    apply Finset.sum_eq_zero
    intro i hi
    have hnot : ¬ Boundary i := by
      simpa using hi
    have hδeq := hδ i hnot
    simp [d, hδeq]
  calc
    (∑ i, μ i * |dyadicWeight (δ₁ i) - dyadicWeight (δ₂ i)|)
        = ∑ i, μ i * d i := by rfl
    _ ≤ weightedSubsum μ d (fun i => ¬ Boundary i)
          + (1 : ℝ) * weightedSubmass μ Boundary := hsplit
    _ = weightedSubmass μ Boundary := by
          rw [hlow_zero]
          ring

end FiniteSplit

namespace BitLength

/--
Natural-number bit length compatible with Python's `int.bit_length` at
`0`, and with `Nat.log 2 n + 1` for positive `n`.
-/
def bitLength (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.log 2 n + 1

theorem bitLength_zero : bitLength 0 = 0 := by
  simp [bitLength]

theorem bitLength_pos {n : ℕ} (hn : n ≠ 0) : 0 < bitLength n := by
  simp [bitLength, hn]

/--
Characterization on one dyadic window: if `n` lies in
`[2^k, 2^(k+1))`, then its bit length is `k+1`.
-/
theorem bitLength_eq_succ_of_pow_le_lt
    {n k : ℕ} (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1)) :
    bitLength n = k + 1 := by
  have hn : n ≠ 0 := by
    have hpow_pos : 0 < 2 ^ k := by positivity
    exact ne_of_gt (lt_of_lt_of_le hpow_pos hlo)
  have hlog : Nat.log 2 n = k := by
    exact Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
  unfold bitLength
  simp only [hn, ↓reduceIte]
  rw [hlog]

/--
Adding a nonnegative perturbation does not change bit length if both
endpoints stay in the same dyadic window.
-/
theorem bitLength_add_eq_of_same_window
    {n c k : ℕ} (hlo : 2 ^ k ≤ n) (hhi : n + c < 2 ^ (k + 1)) :
    bitLength (n + c) = bitLength n := by
  have hn_le : n ≤ n + c := by omega
  have hleft : bitLength n = k + 1 :=
    bitLength_eq_succ_of_pow_le_lt hlo (lt_of_le_of_lt hn_le hhi)
  have hright : bitLength (n + c) = k + 1 :=
    bitLength_eq_succ_of_pow_le_lt (le_trans hlo hn_le) hhi
  exact hright.trans hleft.symm

/--
Subtracting a perturbation does not change bit length if both endpoints
stay in the same dyadic window.
-/
theorem bitLength_sub_eq_of_same_window
    {n c k : ℕ} (hc : c ≤ n)
    (hlo : 2 ^ k ≤ n - c) (hhi : n < 2 ^ (k + 1)) :
    bitLength (n - c) = bitLength n := by
  have hsum : n - c + c = n := by omega
  have hsame :
      bitLength (n - c + c) = bitLength (n - c) :=
    bitLength_add_eq_of_same_window (n := n - c) (c := c) (k := k) hlo
      (by simpa [hsum] using hhi)
  rw [hsum] at hsame
  exact hsame.symm

/--
If adding `c` changes bit length, then the interval `(n, n+c]` crosses a
dyadic endpoint.  This is the proof-facing boundary formulation for
bounded additive perturbations.
-/
theorem exists_dyadic_boundary_of_bitLength_add_ne
    {n c : ℕ} (hn : n ≠ 0)
    (hne : bitLength (n + c) ≠ bitLength n) :
    ∃ k, n < 2 ^ k ∧ 2 ^ k ≤ n + c := by
  let k := Nat.log 2 n + 1
  have hlo : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn
  have hnot : ¬ n + c < 2 ^ (Nat.log 2 n + 1) := by
    intro hhi
    exact hne (bitLength_add_eq_of_same_window hlo hhi)
  have hle : 2 ^ (Nat.log 2 n + 1) ≤ n + c := le_of_not_gt hnot
  have hlt : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two n
  exact ⟨k, hlt, hle⟩

/--
If subtracting `c` changes bit length and the lower endpoint is positive,
then the interval `(n-c, n]` crosses a dyadic endpoint.
-/
theorem exists_dyadic_boundary_of_bitLength_sub_ne
    {n c : ℕ} (hc : c ≤ n) (hsub : n - c ≠ 0)
    (hne : bitLength (n - c) ≠ bitLength n) :
    ∃ k, n - c < 2 ^ k ∧ 2 ^ k ≤ n := by
  let k := Nat.log 2 (n - c) + 1
  have hlo : 2 ^ Nat.log 2 (n - c) ≤ n - c :=
    Nat.pow_log_le_self 2 hsub
  have hnot : ¬ n < 2 ^ (Nat.log 2 (n - c) + 1) := by
    intro hhi
    exact hne (bitLength_sub_eq_of_same_window hc hlo hhi)
  have hle : 2 ^ (Nat.log 2 (n - c) + 1) ≤ n := le_of_not_gt hnot
  have hlt : n - c < 2 ^ (Nat.log 2 (n - c) + 1) :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two (n - c)
  exact ⟨k, hlt, hle⟩

/-- The interval `(t,t+c]` crosses the dyadic endpoint `2^k`. -/
def crossesDyadicEndpoint (t c k : ℕ) : Prop :=
  t < 2 ^ k ∧ 2 ^ k ≤ t + c

instance instDecidableCrossesDyadicEndpoint (t c k : ℕ) :
    Decidable (crossesDyadicEndpoint t c k) := by
  unfold crossesDyadicEndpoint
  infer_instance

/-- The backward `c`-neighborhood immediately before the endpoint `2^k`. -/
def dyadicBackNeighborhood (t c k : ℕ) : Prop :=
  2 ^ k - c ≤ t ∧ t < 2 ^ k

theorem dyadic_boundary_mem_back_neighborhood
    {t c k : ℕ} (h : crossesDyadicEndpoint t c k) :
    dyadicBackNeighborhood t c k := by
  dsimp [crossesDyadicEndpoint, dyadicBackNeighborhood] at h ⊢
  omega

/--
For one fixed dyadic endpoint `2^k`, at most `c` source indices in any
finite prefix can cross that endpoint under the perturbation `(t,t+c]`.
-/
theorem fixed_dyadic_endpoint_crossing_count_le
    (N c k : ℕ) :
    ((Finset.range N).filter fun t => crossesDyadicEndpoint t c k).card ≤ c := by
  classical
  let window : Finset ℕ := Finset.Ico (2 ^ k - c) (2 ^ k)
  have hsubset :
      ((Finset.range N).filter fun t => crossesDyadicEndpoint t c k) ⊆ window := by
    intro t ht
    have hcross : crossesDyadicEndpoint t c k := by
      have ht' :
          t ∈ Finset.range N ∧ crossesDyadicEndpoint t c k := by
        simpa using ht
      exact ht'.2
    have hwin := dyadic_boundary_mem_back_neighborhood hcross
    simpa [window, dyadicBackNeighborhood] using hwin
  calc
    ((Finset.range N).filter fun t => crossesDyadicEndpoint t c k).card
        ≤ window.card := Finset.card_le_card hsubset
    _ = 2 ^ k - (2 ^ k - c) := by
          simp [window]
    _ ≤ c := by
          omega

/-- Source indices `t < N` that cross the fixed endpoint `2^k`. -/
def fixedEndpointCrossingSet (N c k : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun t => crossesDyadicEndpoint t c k

/--
All source indices in `t < N` that cross any dyadic endpoint relevant to
the perturbation `(t,t+c]`.
-/
def endpointCrossingUnion (N c : ℕ) : Finset ℕ :=
  (Finset.range (bitLength (N + c) + 1)).biUnion fun k =>
    fixedEndpointCrossingSet N c k

theorem endpoint_index_lt_of_crosses_in_prefix
    {t N c k : ℕ} (ht : t < N)
    (hcross : crossesDyadicEndpoint t c k) :
    k < bitLength (N + c) + 1 := by
  have htadd : t + c < N + c := Nat.add_lt_add_right ht c
  have hpow_lt : 2 ^ k < N + c := lt_of_le_of_lt hcross.2 htadd
  have hNc : N + c ≠ 0 := by
    have hpow_pos : 0 < 2 ^ k := by positivity
    exact ne_of_gt (lt_trans hpow_pos hpow_lt)
  have hpow_le : 2 ^ k ≤ N + c := le_of_lt hpow_lt
  have hklog : k ≤ Nat.log 2 (N + c) :=
    (Nat.le_log_iff_pow_le Nat.one_lt_two hNc).2 hpow_le
  have hbit : bitLength (N + c) = Nat.log 2 (N + c) + 1 := by
    unfold bitLength
    simp only [hNc, ↓reduceIte]
  omega

theorem mem_endpointCrossingUnion_of_crosses
    {t N c k : ℕ} (ht : t < N)
    (hcross : crossesDyadicEndpoint t c k) :
    t ∈ endpointCrossingUnion N c := by
  classical
  have hk : k ∈ Finset.range (bitLength (N + c) + 1) := by
    exact Finset.mem_range.mpr (endpoint_index_lt_of_crosses_in_prefix ht hcross)
  unfold endpointCrossingUnion fixedEndpointCrossingSet
  exact Finset.mem_biUnion.mpr
    ⟨k, hk, by simp [ht, hcross]⟩

/--
Union bound over all dyadic endpoints relevant to the prefix `t < N`.

This is intentionally coarse but proof-facing: for fixed perturbation
size `c`, the number of possible bit-length boundary indices grows only
logarithmically with `N`.
-/
theorem endpointCrossingUnion_card_le (N c : ℕ) :
    (endpointCrossingUnion N c).card ≤ c * (bitLength (N + c) + 1) := by
  classical
  unfold endpointCrossingUnion fixedEndpointCrossingSet
  calc
    ((Finset.range (bitLength (N + c) + 1)).biUnion fun k =>
        (Finset.range N).filter fun t => crossesDyadicEndpoint t c k).card
        ≤ ∑ k ∈ Finset.range (bitLength (N + c) + 1),
            ((Finset.range N).filter fun t => crossesDyadicEndpoint t c k).card := by
          exact Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range (bitLength (N + c) + 1), c := by
          exact Finset.sum_le_sum fun k _ =>
            fixed_dyadic_endpoint_crossing_count_le N c k
    _ = (bitLength (N + c) + 1) * c := by
          simp
    _ = c * (bitLength (N + c) + 1) := by
          rw [Nat.mul_comm]

theorem bitLength_add_eq_of_no_dyadic_cross
    {n c : ℕ} (hn : n ≠ 0)
    (hno : ∀ k, ¬ crossesDyadicEndpoint n c k) :
    bitLength (n + c) = bitLength n := by
  by_contra hne
  obtain ⟨k, hk⟩ := exists_dyadic_boundary_of_bitLength_add_ne hn hne
  exact hno k (by simpa [crossesDyadicEndpoint] using hk)

theorem not_crosses_of_not_mem_endpointCrossingUnion
    {t N c : ℕ} (ht : t < N)
    (hnot : t ∉ endpointCrossingUnion N c) :
    ∀ k, ¬ crossesDyadicEndpoint t c k := by
  intro k hcross
  exact hnot (mem_endpointCrossingUnion_of_crosses ht hcross)

/-- The affine interval `(a*t+b, a*t+b+c]` crosses `2^k`. -/
def affineCrossesDyadicEndpoint (a b t c k : ℕ) : Prop :=
  a * t + b < 2 ^ k ∧ 2 ^ k ≤ a * t + b + c

instance instDecidableAffineCrossesDyadicEndpoint (a b t c k : ℕ) :
    Decidable (affineCrossesDyadicEndpoint a b t c k) := by
  unfold affineCrossesDyadicEndpoint
  infer_instance

/-- Source indices `t < N` whose affine image crosses the fixed endpoint `2^k`. -/
def fixedAffineEndpointCrossingSet (a b N c k : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun t => affineCrossesDyadicEndpoint a b t c k

/--
All source indices `t < N` whose affine image crosses any dyadic endpoint
relevant to the perturbation `(a*t+b, a*t+b+c]`.
-/
def affineEndpointCrossingUnion (a b N c : ℕ) : Finset ℕ :=
  (Finset.range (bitLength (a * N + b + c) + 1)).biUnion fun k =>
    fixedAffineEndpointCrossingSet a b N c k

theorem affine_boundary_values_close
    {a b t₁ t₂ c k : ℕ}
    (h₁ : affineCrossesDyadicEndpoint a b t₁ c k)
    (h₂ : affineCrossesDyadicEndpoint a b t₂ c k) :
    a * t₁ ≤ a * t₂ + c ∧ a * t₂ ≤ a * t₁ + c := by
  unfold affineCrossesDyadicEndpoint at h₁ h₂
  constructor <;> omega

/--
For one fixed dyadic endpoint, affine crossings have at most `2*c+1`
distinct source indices when the affine slope is positive.  This bound is
coarse but enough for the proof route: fixed-`c` boundary mass is still
logarithmic in the dyadic scale after summing over endpoints.
-/
theorem fixed_affine_endpoint_crossing_count_le
    (a b N c k : ℕ) (ha : 0 < a) :
    (fixedAffineEndpointCrossingSet a b N c k).card ≤ 2 * c + 1 := by
  classical
  by_cases hempty : fixedAffineEndpointCrossingSet a b N c k = ∅
  · simp [hempty]
  · have hnonempty : (fixedAffineEndpointCrossingSet a b N c k).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨t₀, ht₀⟩ := hnonempty
    have hcross₀ : affineCrossesDyadicEndpoint a b t₀ c k := by
      have ht₀' :
          t₀ ∈ Finset.range N ∧ affineCrossesDyadicEndpoint a b t₀ c k := by
        simpa [fixedAffineEndpointCrossingSet] using ht₀
      exact ht₀'.2
    have hsubset :
        fixedAffineEndpointCrossingSet a b N c k
          ⊆ Finset.Icc (t₀ - c) (t₀ + c) := by
      intro t ht
      have hcross : affineCrossesDyadicEndpoint a b t c k := by
        have ht' :
            t ∈ Finset.range N ∧ affineCrossesDyadicEndpoint a b t c k := by
          simpa [fixedAffineEndpointCrossingSet] using ht
        exact ht'.2
      have hclose := affine_boundary_values_close hcross hcross₀
      have ht_le : t ≤ t₀ + c := by
        have hmul : a * t ≤ a * (t₀ + c) := by
          calc
            a * t ≤ a * t₀ + c := hclose.1
            _ ≤ a * t₀ + a * c := by
                  exact Nat.add_le_add_left (Nat.le_mul_of_pos_left c ha) (a * t₀)
            _ = a * (t₀ + c) := by
                  rw [Nat.mul_add]
        exact Nat.le_of_mul_le_mul_left hmul ha
      have htc : t₀ ≤ t + c := by
        have hmul : a * t₀ ≤ a * (t + c) := by
          calc
            a * t₀ ≤ a * t + c := hclose.2
            _ ≤ a * t + a * c := by
                  exact Nat.add_le_add_left (Nat.le_mul_of_pos_left c ha) (a * t)
            _ = a * (t + c) := by
                  rw [Nat.mul_add]
        exact Nat.le_of_mul_le_mul_left hmul ha
      simpa using ⟨htc, ht_le⟩
    calc
      (fixedAffineEndpointCrossingSet a b N c k).card
          ≤ (Finset.Icc (t₀ - c) (t₀ + c)).card :=
            Finset.card_le_card hsubset
      _ = t₀ + c + 1 - (t₀ - c) := by
            simp
      _ ≤ 2 * c + 1 := by
            omega

theorem affine_endpoint_index_lt_of_crosses_in_prefix
    {a b t N c k : ℕ} (ht : t < N)
    (hcross : affineCrossesDyadicEndpoint a b t c k) :
    k < bitLength (a * N + b + c) + 1 := by
  have hmono : a * t + b + c ≤ a * N + b + c := by
    have hmul : a * t ≤ a * N := Nat.mul_le_mul_left a (le_of_lt ht)
    omega
  have hpow_le : 2 ^ k ≤ a * N + b + c := le_trans hcross.2 hmono
  have hM : a * N + b + c ≠ 0 := by
    have hpow_pos : 0 < 2 ^ k := by positivity
    exact ne_of_gt (lt_of_lt_of_le hpow_pos hpow_le)
  have hklog : k ≤ Nat.log 2 (a * N + b + c) :=
    (Nat.le_log_iff_pow_le Nat.one_lt_two hM).2 hpow_le
  have hbit :
      bitLength (a * N + b + c) = Nat.log 2 (a * N + b + c) + 1 := by
    unfold bitLength
    simp only [hM, ↓reduceIte]
  omega

theorem mem_affineEndpointCrossingUnion_of_crosses
    {a b t N c k : ℕ} (ht : t < N)
    (hcross : affineCrossesDyadicEndpoint a b t c k) :
    t ∈ affineEndpointCrossingUnion a b N c := by
  classical
  have hk : k ∈ Finset.range (bitLength (a * N + b + c) + 1) := by
    exact Finset.mem_range.mpr
      (affine_endpoint_index_lt_of_crosses_in_prefix ht hcross)
  unfold affineEndpointCrossingUnion fixedAffineEndpointCrossingSet
  exact Finset.mem_biUnion.mpr
    ⟨k, hk, by simp [ht, hcross]⟩

/--
Coarse finite union bound for affine bit-length boundary crossings.

For fixed slope/intercept and fixed perturbation size `c`, the number of
source indices in `t < N` whose affine image crosses a dyadic endpoint is
`O(c log N)`.  This is the finite arithmetic estimate needed before
normalizing by block size in the Phase-10 low-`v2` route.
-/
theorem affineEndpointCrossingUnion_card_le
    (a b N c : ℕ) (ha : 0 < a) :
    (affineEndpointCrossingUnion a b N c).card
      ≤ (2 * c + 1) * (bitLength (a * N + b + c) + 1) := by
  classical
  unfold affineEndpointCrossingUnion fixedAffineEndpointCrossingSet
  calc
    ((Finset.range (bitLength (a * N + b + c) + 1)).biUnion fun k =>
        (Finset.range N).filter fun t => affineCrossesDyadicEndpoint a b t c k).card
        ≤ ∑ k ∈ Finset.range (bitLength (a * N + b + c) + 1),
            ((Finset.range N).filter fun t =>
              affineCrossesDyadicEndpoint a b t c k).card := by
          exact Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range (bitLength (a * N + b + c) + 1), (2 * c + 1) := by
          exact Finset.sum_le_sum fun k _ =>
            fixed_affine_endpoint_crossing_count_le a b N c k ha
    _ = (bitLength (a * N + b + c) + 1) * (2 * c + 1) := by
          simp
    _ = (2 * c + 1) * (bitLength (a * N + b + c) + 1) := by
          rw [Nat.mul_comm]

theorem not_affineCrosses_of_not_mem_affineEndpointCrossingUnion
    {a b t N c : ℕ} (ht : t < N)
    (hnot : t ∉ affineEndpointCrossingUnion a b N c) :
    ∀ k, ¬ affineCrossesDyadicEndpoint a b t c k := by
  intro k hcross
  exact hnot (mem_affineEndpointCrossingUnion_of_crosses ht hcross)

/-- Bit-length delta of a positive affine return branch. -/
def affineDelta (a b t : ℕ) : ℕ :=
  bitLength (a * t + b) - bitLength t

/--
For an affine branch `F(t)=a*t+b`, the bit-length delta is invariant under
a fixed shift `p` if neither the source interval `(t,t+p]` nor the target
interval `(F(t),F(t)+a*p]` crosses a dyadic endpoint.
-/
theorem affineDelta_period_eq_of_no_crosses
    (a b p t : ℕ)
    (ht : t ≠ 0) (hF : a * t + b ≠ 0)
    (hsrc : ∀ k, ¬ crossesDyadicEndpoint t p k)
    (hdst : ∀ k, ¬ affineCrossesDyadicEndpoint a b t (a * p) k) :
    affineDelta a b (t + p) = affineDelta a b t := by
  have hsrc_eq : bitLength (t + p) = bitLength t :=
    bitLength_add_eq_of_no_dyadic_cross ht hsrc
  have hdst_no : ∀ k, ¬ crossesDyadicEndpoint (a * t + b) (a * p) k := by
    intro k hcross
    exact hdst k (by
      simpa [crossesDyadicEndpoint, affineCrossesDyadicEndpoint] using hcross)
  have hdst_base :
      bitLength (a * t + b + a * p) = bitLength (a * t + b) :=
    bitLength_add_eq_of_no_dyadic_cross hF hdst_no
  have htarget : a * (t + p) + b = a * t + b + a * p := by
    rw [Nat.mul_add]
    omega
  unfold affineDelta
  rw [htarget, hdst_base, hsrc_eq]

/--
Bad source indices for period-`p` affine-delta invariance: either the
source bit length crosses a dyadic endpoint under `t -> t+p`, or the
target affine value crosses under `F(t) -> F(t)+a*p`.
-/
def affineDeltaBadSet (a b N p : ℕ) : Finset ℕ :=
  endpointCrossingUnion N p ∪ affineEndpointCrossingUnion a b N (a * p)

theorem affineDeltaBadSet_card_le
    (a b N p : ℕ) (ha : 0 < a) :
    (affineDeltaBadSet a b N p).card
      ≤ p * (bitLength (N + p) + 1)
        + (2 * (a * p) + 1) * (bitLength (a * N + b + a * p) + 1) := by
  classical
  unfold affineDeltaBadSet
  calc
    (endpointCrossingUnion N p ∪ affineEndpointCrossingUnion a b N (a * p)).card
        ≤ (endpointCrossingUnion N p).card
          + (affineEndpointCrossingUnion a b N (a * p)).card :=
          Finset.card_union_le _ _
    _ ≤ p * (bitLength (N + p) + 1)
        + (2 * (a * p) + 1) * (bitLength (a * N + b + a * p) + 1) := by
          exact Nat.add_le_add
            (endpointCrossingUnion_card_le N p)
            (affineEndpointCrossingUnion_card_le a b N (a * p) ha)

theorem affineDelta_period_eq_of_not_mem_badSet
    (a b N p t : ℕ) (htN : t < N)
    (ht : t ≠ 0) (hF : a * t + b ≠ 0)
    (hnot : t ∉ affineDeltaBadSet a b N p) :
    affineDelta a b (t + p) = affineDelta a b t := by
  have hnotSrc : t ∉ endpointCrossingUnion N p := by
    intro hmem
    exact hnot (by
      unfold affineDeltaBadSet
      exact Finset.mem_union.mpr (Or.inl hmem))
  have hnotDst : t ∉ affineEndpointCrossingUnion a b N (a * p) := by
    intro hmem
    exact hnot (by
      unfold affineDeltaBadSet
      exact Finset.mem_union.mpr (Or.inr hmem))
  exact affineDelta_period_eq_of_no_crosses a b p t ht hF
    (not_crosses_of_not_mem_endpointCrossingUnion htN hnotSrc)
    (not_affineCrosses_of_not_mem_affineEndpointCrossingUnion htN hnotDst)

/--
Bit-length delta for a return branch written on a residue progression:
the source index is `q*u+r` and the returned index is `a*u+b`.

This is the right abstract shape for fixed valuation-word branches whose
raw slope in `t` is dyadic/rational.
-/
def biAffineDelta (a b q r u : ℕ) : ℕ :=
  bitLength (a * u + b) - bitLength (q * u + r)

/--
Bad parameter indices for a bi-affine branch under the period shift
`u -> u+p`: either the source affine form or the target affine form
crosses a dyadic endpoint.
-/
def biAffineDeltaBadSet (a b q r N p : ℕ) : Finset ℕ :=
  affineEndpointCrossingUnion q r N (q * p)
    ∪ affineEndpointCrossingUnion a b N (a * p)

theorem biAffineDeltaBadSet_card_le
    (a b q r N p : ℕ) (ha : 0 < a) (hq : 0 < q) :
    (biAffineDeltaBadSet a b q r N p).card
      ≤ (2 * (q * p) + 1) * (bitLength (q * N + r + q * p) + 1)
        + (2 * (a * p) + 1) * (bitLength (a * N + b + a * p) + 1) := by
  classical
  unfold biAffineDeltaBadSet
  calc
    (affineEndpointCrossingUnion q r N (q * p)
        ∪ affineEndpointCrossingUnion a b N (a * p)).card
        ≤ (affineEndpointCrossingUnion q r N (q * p)).card
          + (affineEndpointCrossingUnion a b N (a * p)).card :=
          Finset.card_union_le _ _
    _ ≤ (2 * (q * p) + 1) * (bitLength (q * N + r + q * p) + 1)
        + (2 * (a * p) + 1) * (bitLength (a * N + b + a * p) + 1) := by
          exact Nat.add_le_add
            (affineEndpointCrossingUnion_card_le q r N (q * p) hq)
            (affineEndpointCrossingUnion_card_le a b N (a * p) ha)

/--
Bi-affine bit-length delta is invariant under a fixed period shift if
neither affine form crosses a dyadic endpoint.
-/
theorem biAffineDelta_period_eq_of_no_crosses
    (a b q r p u : ℕ)
    (hTarget : a * u + b ≠ 0) (hSource : q * u + r ≠ 0)
    (hTargetNo : ∀ k, ¬ affineCrossesDyadicEndpoint a b u (a * p) k)
    (hSourceNo : ∀ k, ¬ affineCrossesDyadicEndpoint q r u (q * p) k) :
    biAffineDelta a b q r (u + p) = biAffineDelta a b q r u := by
  have hTargetCrossNo :
      ∀ k, ¬ crossesDyadicEndpoint (a * u + b) (a * p) k := by
    intro k hcross
    exact hTargetNo k (by
      simpa [crossesDyadicEndpoint, affineCrossesDyadicEndpoint] using hcross)
  have hSourceCrossNo :
      ∀ k, ¬ crossesDyadicEndpoint (q * u + r) (q * p) k := by
    intro k hcross
    exact hSourceNo k (by
      simpa [crossesDyadicEndpoint, affineCrossesDyadicEndpoint] using hcross)
  have hTargetEq :
      bitLength (a * u + b + a * p) = bitLength (a * u + b) :=
    bitLength_add_eq_of_no_dyadic_cross hTarget hTargetCrossNo
  have hSourceEq :
      bitLength (q * u + r + q * p) = bitLength (q * u + r) :=
    bitLength_add_eq_of_no_dyadic_cross hSource hSourceCrossNo
  have hTargetExpr : a * (u + p) + b = a * u + b + a * p := by
    rw [Nat.mul_add]
    omega
  have hSourceExpr : q * (u + p) + r = q * u + r + q * p := by
    rw [Nat.mul_add]
    omega
  unfold biAffineDelta
  rw [hTargetExpr, hSourceExpr, hTargetEq, hSourceEq]

theorem biAffineDelta_period_eq_of_not_mem_badSet
    (a b q r N p u : ℕ) (huN : u < N)
    (hTarget : a * u + b ≠ 0) (hSource : q * u + r ≠ 0)
    (hnot : u ∉ biAffineDeltaBadSet a b q r N p) :
    biAffineDelta a b q r (u + p) = biAffineDelta a b q r u := by
  have hnotSource : u ∉ affineEndpointCrossingUnion q r N (q * p) := by
    intro hmem
    exact hnot (by
      unfold biAffineDeltaBadSet
      exact Finset.mem_union.mpr (Or.inl hmem))
  have hnotTarget : u ∉ affineEndpointCrossingUnion a b N (a * p) := by
    intro hmem
    exact hnot (by
      unfold biAffineDeltaBadSet
      exact Finset.mem_union.mpr (Or.inr hmem))
  exact biAffineDelta_period_eq_of_no_crosses a b q r p u hTarget hSource
    (not_affineCrosses_of_not_mem_affineEndpointCrossingUnion huN hnotTarget)
    (not_affineCrosses_of_not_mem_affineEndpointCrossingUnion huN hnotSource)

/--
Reparameterizing a bi-affine branch by `u = M*v+s` gives the refined
bi-affine branch

`source_t = (q*M)*v + (q*s+r)`,
`target_t = (a*M)*v + (a*s+b)`.

This is the arithmetic bridge used by the destination-refined branch
rows generated in Phase 10.
-/
theorem biAffineDelta_refine
    (a b q r M s v : ℕ) :
    biAffineDelta a b q r (M * v + s)
      = biAffineDelta (a * M) (a * s + b) (q * M) (q * s + r) v := by
  have hTarget : a * (M * v + s) + b = (a * M) * v + (a * s + b) := by
    ring
  have hSource : q * (M * v + s) + r = (q * M) * v + (q * s + r) := by
    ring
  unfold biAffineDelta
  rw [hTarget, hSource]

/--
Finite weighted boundary estimate for one bi-affine return branch.

For a branch written as `source_t = q*u+r`, `target_t = a*u+b`, the
period-shift discrepancy of the dyadic weights `2^-delta` is controlled
by the weighted mass of the explicitly counted source/target dyadic
crossing set.  This is still a finite arithmetic reduction: Collatz
specific work must identify the correct branches and show that the
corresponding boundary masses vanish in the required block average.
-/
theorem biAffineDelta_dyadicWeight_period_boundary_le
    (a b q r N p : ℕ) (μ : Fin N → ℝ)
    (hμ : ∀ i, 0 ≤ μ i)
    (hTarget : ∀ i : Fin N, a * (i : ℕ) + b ≠ 0)
    (hSource : ∀ i : Fin N, q * (i : ℕ) + r ≠ 0) :
    (∑ i, μ i *
        |FiniteSplit.dyadicWeight (biAffineDelta a b q r ((i : ℕ) + p))
          - FiniteSplit.dyadicWeight (biAffineDelta a b q r (i : ℕ))|)
      ≤ FiniteSplit.weightedSubmass μ
          (fun i : Fin N => (i : ℕ) ∈ biAffineDeltaBadSet a b q r N p) := by
  classical
  exact FiniteSplit.weighted_dyadic_delta_boundary_le μ
    (fun i : Fin N => biAffineDelta a b q r ((i : ℕ) + p))
    (fun i : Fin N => biAffineDelta a b q r (i : ℕ))
    (fun i : Fin N => (i : ℕ) ∈ biAffineDeltaBadSet a b q r N p)
    hμ
    (fun i hnot =>
      biAffineDelta_period_eq_of_not_mem_badSet a b q r N p (i : ℕ)
        i.isLt (hTarget i) (hSource i) hnot)

/--
Exact dyadic scale invariance of bit length.  This is the elementary
building block for the Phase-10 affine bit-length average target.
-/
theorem bitLength_two_mul (n : ℕ) (hn : n ≠ 0) :
    bitLength (2 * n) = bitLength n + 1 := by
  have h2n : 2 * n ≠ 0 := by omega
  have hlog : Nat.log 2 (2 * n) = Nat.log 2 n + 1 := by
    simpa [Nat.mul_comm] using Nat.log_mul_base (b := 2) (n := n) Nat.one_lt_two hn
  unfold bitLength
  simp only [h2n, hn, ↓reduceIte]
  rw [hlog]

theorem bitLength_mul_two (n : ℕ) (hn : n ≠ 0) :
    bitLength (n * 2) = bitLength n + 1 := by
  simpa [Nat.mul_comm] using bitLength_two_mul n hn

end BitLength

namespace LabelSplit

/--
Minimal finite counters for one Phase-10 label-split branch diagnostic.

These fields deliberately encode only the finite bookkeeping condition used
by script 126.  `branchResolved` below does **not** assert an infinite
first-return theorem; it says that this declared branch row has passed the
current finite split diagnostic:

* no prefix-integrality obstruction;
* final target is visible at the low target level;
* no final competing phantom label is visible;
* every intermediate target-visible class is accounted for as high-lift,
  with no low-only target `b=1` class;
* no intermediate competing class intersects a later target-visible class
  before the final step;
* the final high-lift target branch has an arithmetic continuation.
-/
structure BranchCounters where
  prefixIntegralityFailures : Nat
  finalTargetLowFailures : Nat
  finalCompetingFailures : Nat
  intermediateTargetVisible : Nat
  intermediateTargetHighLiftCovered : Nat
  intermediateTargetLowOnlyVisible : Nat
  intermediateCompetingLaterTarget : Nat
  highLiftContinuationSupported : Nat
  highLiftContinuationIntegralityFailures : Nat
  highLiftContinuationNoDropFailures : Nat
  deriving Repr, DecidableEq

/-- Finite label-split resolution predicate for one declared branch row. -/
def branchResolved (c : BranchCounters) : Prop :=
  c.prefixIntegralityFailures = 0
    ∧ c.finalTargetLowFailures = 0
    ∧ c.finalCompetingFailures = 0
    ∧ c.intermediateTargetHighLiftCovered = c.intermediateTargetVisible
    ∧ c.intermediateTargetLowOnlyVisible = 0
    ∧ c.intermediateCompetingLaterTarget = 0
    ∧ c.highLiftContinuationSupported = 1
    ∧ c.highLiftContinuationIntegralityFailures = 0
    ∧ c.highLiftContinuationNoDropFailures = 0

/--
Boolean-as-natural certificate bit for `branchResolved`.

This mirrors the script-126 column `label_split_resolution_certificate`.
-/
noncomputable def branchCertificate (c : BranchCounters) : Nat := by
  classical
  exact if branchResolved c then 1 else 0

theorem branchCertificate_eq_one_iff (c : BranchCounters) :
    branchCertificate c = 1 ↔ branchResolved c := by
  unfold branchCertificate
  by_cases h : branchResolved c <;> simp [h]

theorem branchResolved_of_certificate_eq_one
    {c : BranchCounters} (h : branchCertificate c = 1) :
    branchResolved c :=
  (branchCertificate_eq_one_iff c).mp h

/--
Finite summary counters for a table of declared branch rows.

`certificateRows = branchRows` means every declared row in the finite table
carried a row-level `branchCertificate = 1` in the generating artifact.
It does not assert that the finite table is an infinite residue partition.
-/
structure SummaryCounters where
  branchRows : Nat
  certificateRows : Nat
  deriving Repr, DecidableEq

/-- All declared rows in a finite summary passed the split certificate. -/
def summaryResolved (s : SummaryCounters) : Prop :=
  s.certificateRows = s.branchRows

/-- Failure bit for finite summary-level split resolution. -/
noncomputable def summaryFailure (s : SummaryCounters) : Nat := by
  classical
  exact if summaryResolved s then 0 else 1

theorem summaryFailure_eq_zero_iff (s : SummaryCounters) :
    summaryFailure s = 0 ↔ summaryResolved s := by
  unfold summaryFailure
  by_cases h : summaryResolved s <;> simp [h]

theorem summaryResolved_of_failure_eq_zero
    {s : SummaryCounters} (h : summaryFailure s = 0) :
    summaryResolved s :=
  (summaryFailure_eq_zero_iff s).mp h

/--
Abstract cover of a source space by declared branch labels.

This is the conditional bridge needed after the finite diagnostics: if a
source point is covered by some declared branch label, and every covering
branch has `branchResolved` counters, then the source point is resolved in
the finite label-split sense.  The structure does not assert that such a
cover has been constructed for the Collatz/A0 infinite source space.
-/
structure BranchCover (σ β : Type*) where
  Covers : β → σ → Prop
  covers : ∀ x : σ, ∃ b : β, Covers b x

/--
Optional uniqueness upgrade for a cover.

The current Phase-10 finite summaries use disjoint branch rows after
splitting.  Keeping uniqueness separate avoids smuggling it into the
minimal cover lemma.
-/
structure BranchPartition (σ β : Type*) where
  Covers : β → σ → Prop
  covers : ∀ x : σ, ∃ b : β, Covers b x
  unique : ∀ {x : σ} {b₁ b₂ : β}, Covers b₁ x → Covers b₂ x → b₁ = b₂

def BranchPartition.toCover {σ β : Type*}
    (P : BranchPartition σ β) : BranchCover σ β :=
  { Covers := P.Covers, covers := P.covers }

/-- A source point is resolved when it lies in a resolved branch. -/
def sourceResolved {σ β : Type*}
    (P : BranchCover σ β) (counters : β → BranchCounters) (x : σ) : Prop :=
  ∃ b : β, P.Covers b x ∧ branchResolved (counters b)

/-- Every covering branch for every source point is resolved. -/
def coverResolved {σ β : Type*}
    (P : BranchCover σ β) (counters : β → BranchCounters) : Prop :=
  ∀ ⦃b : β⦄ ⦃x : σ⦄, P.Covers b x → branchResolved (counters b)

theorem sourceResolved_of_coverResolved {σ β : Type*}
    (P : BranchCover σ β) (counters : β → BranchCounters)
    (h : coverResolved P counters) (x : σ) :
    sourceResolved P counters x := by
  rcases P.covers x with ⟨b, hb⟩
  exact ⟨b, hb, h hb⟩

theorem coverResolved_of_all_branches_resolved {σ β : Type*}
    (P : BranchCover σ β) (counters : β → BranchCounters)
    (h : ∀ b : β, branchResolved (counters b)) :
    coverResolved P counters := by
  intro b _x _hb
  exact h b

theorem sourceResolved_of_all_branches_resolved {σ β : Type*}
    (P : BranchCover σ β) (counters : β → BranchCounters)
    (h : ∀ b : β, branchResolved (counters b)) (x : σ) :
    sourceResolved P counters x :=
  sourceResolved_of_coverResolved P counters
    (coverResolved_of_all_branches_resolved P counters h) x

theorem partition_sourceResolved_of_all_branches_resolved {σ β : Type*}
    (P : BranchPartition σ β) (counters : β → BranchCounters)
    (h : ∀ b : β, branchResolved (counters b)) (x : σ) :
    sourceResolved P.toCover counters x :=
  sourceResolved_of_all_branches_resolved P.toCover counters h x

/--
Finite return-sample partition summary.

`coveredReturnSamples` is the sum of the declared branch-row sample counts.
`returnPartitionResolved` says that this sum equals the finite return sample
count and that the generator reported no coverage failure.  This is only a
finite accounting statement for the declared sample/prefix universe.
-/
structure ReturnPartitionSummary where
  returnSamples : Nat
  coveredReturnSamples : Nat
  coverageFailures : Nat
  deriving Repr, DecidableEq

def returnPartitionResolved (s : ReturnPartitionSummary) : Prop :=
  s.coveredReturnSamples = s.returnSamples ∧ s.coverageFailures = 0

noncomputable def returnPartitionFailure (s : ReturnPartitionSummary) : Nat := by
  classical
  exact if returnPartitionResolved s then 0 else 1

theorem returnPartitionFailure_eq_zero_iff (s : ReturnPartitionSummary) :
    returnPartitionFailure s = 0 ↔ returnPartitionResolved s := by
  unfold returnPartitionFailure
  by_cases h : returnPartitionResolved s <;> simp [h]

theorem returnPartitionResolved_of_failure_eq_zero
    {s : ReturnPartitionSummary} (h : returnPartitionFailure s = 0) :
    returnPartitionResolved s :=
  (returnPartitionFailure_eq_zero_iff s).mp h

/--
Finite outcome decomposition summary for a declared prefix universe.

The intended reading is:

* `coveredReturnSamples`: return samples covered by declared branch rows;
* `dropSamples`: samples that have already dropped below their source and
  are terminal for the finite first-return search;
* `valuationTailSamples` and `stepTailSamples`: explicit unresolved tails.

This is a finite accounting device.  It does not prove that the unresolved
tail vanishes in any limiting regime.
-/
structure OutcomeSummary where
  totalSamples : Nat
  returnSamples : Nat
  coveredReturnSamples : Nat
  dropSamples : Nat
  valuationTailSamples : Nat
  stepTailSamples : Nat
  returnCoverageFailures : Nat
  deriving Repr, DecidableEq

def tailSamples (s : OutcomeSummary) : Nat :=
  s.valuationTailSamples + s.stepTailSamples

def outcomeAccountedSamples (s : OutcomeSummary) : Nat :=
  s.coveredReturnSamples + s.dropSamples + tailSamples s

def outcomeDecompositionResolved (s : OutcomeSummary) : Prop :=
  s.coveredReturnSamples = s.returnSamples
    ∧ s.returnCoverageFailures = 0
    ∧ outcomeAccountedSamples s = s.totalSamples

noncomputable def outcomeDecompositionFailure (s : OutcomeSummary) : Nat := by
  classical
  exact if outcomeDecompositionResolved s then 0 else 1

theorem outcomeDecompositionFailure_eq_zero_iff (s : OutcomeSummary) :
    outcomeDecompositionFailure s = 0 ↔ outcomeDecompositionResolved s := by
  unfold outcomeDecompositionFailure
  by_cases h : outcomeDecompositionResolved s <;> simp [h]

theorem outcomeDecompositionResolved_of_failure_eq_zero
    {s : OutcomeSummary} (h : outcomeDecompositionFailure s = 0) :
    outcomeDecompositionResolved s :=
  (outcomeDecompositionFailure_eq_zero_iff s).mp h

end LabelSplit

namespace TailCount

/-- Number of high-`v2` source times in the two-prefix source model. -/
def tailCount (L R q : ℕ) : ℕ :=
  (L - 1) / (2 ^ q) + (R - 1) / (2 ^ q)

/-- Total number of positive source times in the two-prefix source model. -/
def totalCount (L R : ℕ) : ℕ :=
  L + R - 2

/--
Arithmetic core of the script-111 high-`v2` source-tail estimate.

If the two source prefixes have lengths `L` and `R` and `t=0` is excluded,
then the number of positive source times in the union-average tail
`v2(t) >= q` is

  `(L - 1) / 2^q + (R - 1) / 2^q`.

This lemma states the dyadic upper bound in integer form:
multiplying that count by `2^q` is at most the total positive source count
`L + R - 2`.  It is the formal version of

  `mu({v2 >= q}) <= 2^-q`.
-/
theorem dyadic_tail_count_mul_le
    (L R q : ℕ) (hL : 0 < L) (hR : 0 < R) :
    tailCount L R q * (2 ^ q) ≤ totalCount L R := by
  have hLeft : (L - 1) / (2 ^ q) * (2 ^ q) ≤ L - 1 := by
    exact Nat.div_mul_le_self (L - 1) (2 ^ q)
  have hRight : (R - 1) / (2 ^ q) * (2 ^ q) ≤ R - 1 := by
    exact Nat.div_mul_le_self (R - 1) (2 ^ q)
  unfold tailCount totalCount
  rw [Nat.add_mul]
  have hSum :
      (L - 1) / (2 ^ q) * (2 ^ q)
        + (R - 1) / (2 ^ q) * (2 ^ q)
        ≤ (L - 1) + (R - 1) :=
    Nat.add_le_add hLeft hRight
  have hSub : (L - 1) + (R - 1) = L + R - 2 := by
    omega
  exact hSub ▸ hSum

/--
Real mass form of the high-`v2` source-tail estimate.

When the two-prefix source model has positive total source count, the
proportion of source times with `v2(t) >= q` is at most `2^{-q}`.  This is
the theorem-level form used by the A0 weak double-limit split.
-/
theorem dyadic_tail_mass_le
    (L R q : ℕ) (hL : 0 < L) (hR : 0 < R)
    (hTotal : 0 < totalCount L R) :
    (tailCount L R q : ℝ) / (totalCount L R : ℝ)
      ≤ (1 : ℝ) / ((2 ^ q : ℕ) : ℝ) := by
  have hcore := dyadic_tail_count_mul_le L R q hL hR
  have hcoreR :
      (tailCount L R q : ℝ) * ((2 ^ q : ℕ) : ℝ)
        ≤ (totalCount L R : ℝ) := by
    exact_mod_cast hcore
  have hpow_pos : (0 : ℝ) < ((2 ^ q : ℕ) : ℝ) := by
    have hpowNat : 0 < 2 ^ q := by positivity
    exact_mod_cast hpowNat
  have htot_pos : (0 : ℝ) < (totalCount L R : ℝ) := by
    exact_mod_cast hTotal
  field_simp [hpow_pos.ne', htot_pos.ne']
  nlinarith [hcoreR, hpow_pos, htot_pos]

end TailCount

end WeakBridge
end CollatzShadowing
