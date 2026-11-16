/-
Arbitrarily many consecutive increasing first returns to the marked section.
This refines the existing cancellation macros with the exact return times;
it does not supply a decreasing exit from those macros.

AI-assisted development: Codex with Piero Borgatta, 2026-11-13.
-/
import CollatzShadowing.SectionReturn

namespace CollatzShadowing.ReturnBlocks

open MarkedSection

/-- Endpoints of the first `r` marked return blocks. -/
def point (r t j : ℕ) : ℕ := 18 * (t * 8 ^ (r - j) * 9 ^ j) - 5

/-- The sole intermediate point when `j < r`. -/
def middle (r t j : ℕ) : ℕ := 216 * (t * 8 ^ (r - j - 1) * 9 ^ j) - 7

private theorem section_eighteen_sub_five {u : ℕ} (hu : 0 < u) :
    «section» (18 * u - 5) := by
  apply Or.inl
  omega

private theorem not_section_seventy_two_sub_seven (u : ℕ) :
    ¬ «section» (216 * u - 7) := by
  unfold MarkedSection.«section»
  omega

/-- Every endpoint through the final block belongs to the first port. -/
theorem point_mem_section (r t j : ℕ) (ht : 0 < t) : «section» (point r t j) := by
  unfold point
  apply section_eighteen_sub_five
  positivity

/-- The intermediate residue `65 mod 72` excludes all six ports. -/
theorem middle_not_mem_section (r t j : ℕ) : ¬ «section» (middle r t j) :=
  not_section_seventy_two_sub_seven _

private theorem point_as_block {r t j : ℕ} (hj : j < r) :
    point r t j = 8 * (18 * (t * 8 ^ (r - j - 1) * 9 ^ j)) - 5 := by
  have hexp : r - j = (r - j - 1) + 1 := by omega
  unfold point
  conv_lhs => rw [hexp, pow_succ]
  congr 1
  ring

private theorem next_point_as_block {r t j : ℕ} :
    point r t (j + 1) = 9 * (18 * (t * 8 ^ (r - j - 1) * 9 ^ j)) - 5 := by
  have hexp : r - (j + 1) = r - j - 1 := by omega
  unfold point
  rw [hexp, pow_succ]
  congr 1
  ring

private theorem middle_as_block (r t j : ℕ) :
    middle r t j = 12 * (18 * (t * 8 ^ (r - j - 1) * 9 ^ j)) - 7 := by
  unfold middle
  congr 1
  ring

/-- Exact exponents and values for each of the arbitrarily many blocks. -/
theorem block_steps {r t j : ℕ} (ht : 0 < t) (hj : j < r) :
    syracuseExponent (point r t j) = 1 ∧
    S (point r t j) = middle r t j ∧
    syracuseExponent (middle r t j) = 2 ∧
    S (middle r t j) = point r t (j + 1) := by
  let q := t * 8 ^ (r - j - 1) * 9 ^ j
  have hq : 0 < q := by dsimp [q]; positivity
  have hv : 2 ≤ 18 * q := by omega
  have heven : Even (18 * q) := ⟨9 * q, by omega⟩
  have h := cancellationTower_block hv heven
  simpa only [point_as_block hj, middle_as_block, next_point_as_block, q] using h

/-- Each return increases by the displayed positive amount. -/
theorem point_increment {r t j : ℕ} (ht : 0 < t) (hj : j < r) :
    point r t (j + 1) = point r t j + 18 * (t * 8 ^ (r - j - 1) * 9 ^ j) := by
  have hq : 0 < t * 8 ^ (r - j - 1) * 9 ^ j := by positivity
  rw [point_as_block hj, next_point_as_block]
  omega

theorem point_lt_next {r t j : ℕ} (ht : 0 < t) (hj : j < r) :
    point r t j < point r t (j + 1) := by
  rw [point_increment ht hj]
  have : 0 < 18 * (t * 8 ^ (r - j - 1) * 9 ^ j) := by positivity
  omega

/-- A two-step marked return is the first positive marked return. -/
theorem first_return {r t j : ℕ} (ht : 0 < t) (hj : j < r) :
    «section» (point r t j) ∧
    S^[2] (point r t j) = point r t (j + 1) ∧
    «section» (point r t (j + 1)) ∧
    point r t j < point r t (j + 1) ∧
    ∀ k : ℕ, 0 < k → k < 2 → ¬ «section» (S^[k] (point r t j)) := by
  rcases block_steps ht hj with ⟨_, hs, _, hm⟩
  refine ⟨point_mem_section r t j ht, ?_, point_mem_section r t (j + 1) ht,
    point_lt_next ht hj, ?_⟩
  · simpa [Function.iterate_succ_apply', hs] using hm
  · intro k hk hk2
    have : k = 1 := by omega
    subst k
    simpa only [Function.iterate_one, hs] using middle_not_mem_section r t j

/-- The endpoints are actual iterates of the initial endpoint. -/
theorem iterate_point {r t : ℕ} (ht : 0 < t) {j : ℕ} (hj : j ≤ r) :
    S^[2 * j] (point r t 0) = point r t j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjr : j < r := by omega
      have hprev := ih (by omega)
      have hnext := (first_return ht hjr).2.1
      rw [show 2 * (j + 1) = 2 + 2 * j by omega, Function.iterate_add_apply, hprev]
      exact hnext

/-- For every requested number of returns, one positive orbit has that many
consecutive first marked returns, and all of them strictly increase. -/
theorem arbitrarily_many_increasing_first_returns (r : ℕ) :
    ∃ n : ℕ, 0 < n ∧ «section» n ∧
      ∀ j : ℕ, j < r →
        «section» (S^[2 * j] n) ∧
        «section» (S^[2 * (j + 1)] n) ∧
        S^[2 * j] n < S^[2 * (j + 1)] n ∧
        ∀ k : ℕ, 0 < k → k < 2 → ¬ «section» (S^[2 * j + k] n) := by
  refine ⟨point r 1 0, ?_, point_mem_section r 1 0 (by omega), ?_⟩
  · unfold point
    have : 1 ≤ 8 ^ r := Nat.one_le_pow r 8 (by norm_num)
    simp only [Nat.sub_zero, pow_zero, Nat.one_mul, Nat.mul_one]
    omega
  · intro j hj
    have hp := iterate_point (r := r) (t := 1) (by omega) (j := j) (by omega)
    have hn := iterate_point (r := r) (t := 1) (by omega) (j := j + 1) (by omega)
    obtain ⟨hstart, _, hend, hlt, hinter⟩ := first_return (t := 1) (by omega) hj
    refine ⟨by simpa only [hp] using hstart, by simpa only [hn] using hend,
      by simpa only [hp, hn] using hlt, ?_⟩
    intro k hk hk2
    rw [show 2 * j + k = k + 2 * j by omega, Function.iterate_add_apply, hp]
    exact hinter k hk hk2

end CollatzShadowing.ReturnBlocks
