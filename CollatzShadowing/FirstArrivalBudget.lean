/-
First-arrival injectivity and exact shortcut clocks for Syracuse words.

The finite parity-packing estimate is connected to actual first-arrival
words. No reciprocal-budget hypothesis remains in the final height theorem.
Existence of a same-profile image is still required; no mass is constructed.

AI-assisted development: Codex with Piero Borgatta, 2026-11-15.
-/

import CollatzShadowing.SectionCoverage
import CollatzShadowing.WordProductEnvelope
import CollatzShadowing.FiniteOrbitTransfer
import CollatzShadowing.OrbitReciprocal
import CollatzShadowing.SiblingBasins

namespace CollatzShadowing.FirstArrivalBudget

open WeightedVisits ShortcutCoverage
open scoped BigOperators

/-- A trajectory through its first arrival has no repeated state, including
its endpoint. This is a deterministic statement for any map. -/
theorem first_arrival_injective {α : Type*} (f : α → α) (x y : α) (L : ℕ)
    (harrival : f^[L] x = y) (hfirst : ∀ i < L, f^[i] x ≠ y) :
    ∀ i ≤ L, ∀ j ≤ L, f^[i] x = f^[j] x → i = j := by
  have no_lt : ∀ i ≤ L, ∀ j ≤ L,
      f^[i] x = f^[j] x → i < j → False := by
    intro i hi j hj hij hlt
    have h := congrArg (f^[L - j]) hij
    simp only [← Function.iterate_add_apply] at h
    have hjend : L - j + j = L := by omega
    rw [hjend, harrival] at h
    exact hfirst (L - j + i) (by omega) h
  intro i hi j hj hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact no_lt i hi j hj hij hlt
  · exact no_lt j hj i hi hij.symm hgt

/-- Odd inputs remove at least one factor of two. -/
theorem exponent_pos_of_odd {n : ℕ} (hn : Odd n) :
    0 < syracuseExponent n := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hd : 2 ^ 1 ∣ 3 * n + 1 := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨3 * k + 2, ?_⟩
    omega
  have hle := (MarkedSection.pow_two_dvd_iff n 1).mp hd
  omega

theorem orbit_odd {x : ℕ} (hx : Odd x) (k : ℕ) : Odd (S^[k] x) := by
  cases k with
  | zero => simpa using hx
  | succ k => exact syracuse_iterate_succ_odd k x

/-- Exact elapsed shortcut time of an accelerated orbit point. -/
theorem shortcut_clock {x : ℕ} (hx : Odd x) (k : ℕ) :
    T^[exponentSum x k] x = S^[k] x := by
  induction k with
  | zero => simp [exponentSum]
  | succ k ih =>
      rw [exponentSum, Nat.add_comm, Function.iterate_add_apply, ih,
        SectionCoverage.shortcut_episode_endpoint (orbit_odd hx k),
        Function.iterate_succ_apply']

/-- Accelerated orbit times form a strictly increasing shortcut clock. -/
theorem clock_strictMono {x : ℕ} (hx : Odd x) : StrictMono (exponentSum x) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [exponentSum]
  exact Nat.lt_add_of_pos_right (exponent_pos_of_odd (orbit_odd hx k))

/-- Every strictly interior shortcut state of an odd episode is even. -/
theorem episode_internal_even {x j : ℕ} (hx : Odd x) (hj : 0 < j)
    (hjlt : j < syracuseExponent x) : Even (T^[j] x) := by
  have hnum := pow_mul_syracuseStepWithExponent_eq_of_exponent
    (n := x) (a := syracuseExponent x) rfl
  have hstep : syracuseStepWithExponent (syracuseExponent x) x = S x := by
    simp [syracuseStepWithExponent, S, syracuseNumerator]
  rw [hstep] at hnum
  have hsplit : 2 ^ syracuseExponent x = 2 ^ j * 2 ^ (syracuseExponent x - j) := by
    rw [← pow_add]
    congr 1
    omega
  have heq : T^[j] x = 2 ^ (syracuseExponent x - j) * S x := by
    rw [SectionCoverage.shortcut_episode hx hj (Nat.le_of_lt hjlt), ← hnum, hsplit]
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ j)]
  rw [heq]
  apply even_iff_two_dvd.mpr
  exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega : syracuseExponent x - j ≠ 0)) _

/-- Every odd shortcut hit is exactly an accelerated orbit point, with
the exact elapsed shortcut time recorded by the exponent sum. -/
theorem odd_shortcut_hit {n : ℕ} (hn : Odd n) (t : ℕ) :
    ∀ x : ℕ, Odd x → T^[t] x = n →
      ∃ k : ℕ, S^[k] x = n ∧ exponentSum x k = t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro x hx hhit
      by_cases ht : t = 0
      · subst t
        exact ⟨0, by simpa using hhit, by simp [exponentSum]⟩
      have htpos : 0 < t := by omega
      have ha := exponent_pos_of_odd hx
      by_cases hsmall : t < syracuseExponent x
      · have he := episode_internal_even hx htpos hsmall
        rw [hhit] at he
        exact False.elim ((Nat.not_even_iff_odd.mpr hn) he)
      · have hle : syracuseExponent x ≤ t := by omega
        have hrem : t - syracuseExponent x < t := by omega
        have hdecomp : t = (t - syracuseExponent x) + syracuseExponent x := by omega
        have htail : T^[t - syracuseExponent x] (S x) = n := by
          rw [hdecomp, Function.iterate_add_apply,
            SectionCoverage.shortcut_episode_endpoint hx] at hhit
          exact hhit
        obtain ⟨k, hk, hclock⟩ := ih _ hrem (S x) (syracuse_odd x) htail
        refine ⟨k + 1, ?_, ?_⟩
        · simpa only [Function.iterate_succ_apply] using hk
        · rw [exponentSum_succ_first, hclock]
          omega

/-- A first accelerated arrival at an odd target is also a first shortcut
arrival at the corresponding exact clock time. -/
theorem accelerated_first_is_shortcut_first {x n k : ℕ}
    (hx : Odd x) (hn : Odd n)
    (hfirst : ∀ i < k, S^[i] x ≠ n) :
    ∀ t < exponentSum x k, T^[t] x ≠ n := by
  intro t ht hhit
  obtain ⟨i, hi, hclock⟩ := odd_shortcut_hit hn t x hx hhit
  have hik : i < k := by
    by_contra hnot
    have hle : k ≤ i := by omega
    have h := (clock_strictMono hx).monotone hle
    omega
  exact hfirst i hik hi

/-- A Syracuse reciprocal sum is bounded by the reciprocal sum of its full
shortcut segment whenever that shortcut segment is injective. -/
theorem accelerated_sum_le_shortcut_sum {x k : ℕ}
    (hx : Odd x)
    (hinj : ∀ i < exponentSum x k + 1, ∀ j < exponentSum x k + 1,
      T^[i] x = T^[j] x → i = j) :
    (∑ i ∈ Finset.range k, (1 : ℝ) / (S^[i] x : ℝ)) ≤
      ∑ n ∈ FiniteOrbitTransfer.segment T x (exponentSum x k + 1), (1 : ℝ) / n := by
  let A := (Finset.range k).image (fun i => S^[i] x)
  have hsub : A ⊆ FiniteOrbitTransfer.segment T x (exponentSum x k + 1) := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_image.mpr
    refine ⟨exponentSum x i, Finset.mem_range.mpr ?_, shortcut_clock hx i⟩
    have hclock := (clock_strictMono hx).monotone (Nat.le_of_lt (Finset.mem_range.mp hi))
    omega
  have hiA : Set.InjOn (fun i => S^[i] x) (↑(Finset.range k) : Set ℕ) := by
    intro i hi j hj hij
    have hci : exponentSum x i < exponentSum x k + 1 := by
      have h := (clock_strictMono hx).monotone (Nat.le_of_lt (Finset.mem_range.mp hi))
      omega
    have hcj : exponentSum x j < exponentSum x k + 1 := by
      have h := (clock_strictMono hx).monotone (Nat.le_of_lt (Finset.mem_range.mp hj))
      omega
    apply (clock_strictMono hx).injective
    apply hinj _ hci _ hcj
    simpa only [shortcut_clock hx] using hij
  calc
    _ = ∑ n ∈ A, (1 : ℝ) / n := by
      rw [Finset.sum_image hiA]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro n hn hnot
      positivity)

/-- Every positive odd first-arrival Syracuse segment has reciprocal sum
strictly below 81, independently of its length, height and endpoint. -/
theorem first_arrival_reciprocal_sum_lt_eighty_one {x n k : ℕ}
    (hxpos : 0 < x) (hx : Odd x) (hn : Odd n)
    (harrival : S^[k] x = n) (hfirst : ∀ i < k, S^[i] x ≠ n) :
    (∑ i ∈ Finset.range k, (1 : ℝ) / (S^[i] x : ℝ)) < 81 := by
  have hTarrival : T^[exponentSum x k] x = n := by
    rw [shortcut_clock hx, harrival]
  have hTfirst := accelerated_first_is_shortcut_first hx hn hfirst
  have hinj := first_arrival_injective T x n (exponentSum x k) hTarrival hTfirst
  have hinj' : ∀ i < exponentSum x k + 1, ∀ j < exponentSum x k + 1,
      T^[i] x = T^[j] x → i = j := by
    intro i hi j hj
    exact hinj i (by omega) j (by omega)
  exact (accelerated_sum_le_shortcut_sum hx hinj').trans_lt
    (OrbitReciprocal.finite_orbit_reciprocal_sum_real_lt_eighty_one
      x (exponentSum x k + 1) hxpos hinj')

/-- Universal height for an existing same-profile image of a first-arrival
word to a target y at most 21 times n. No outgoing mass is asserted. -/
theorem first_arrival_same_profile_height {w w' : List ℕ} {u v n y : ℕ}
    (hu : 0 < u) (huodd : Odd u) (hn : 0 < n) (hnodd : Odd n)
    (hw : SyracuseWordMatchesFrom w u) (he : evalSyracuseWord w u = n)
    (hfirst : ∀ i < w.length, S^[i] u ≠ n)
    (hw' : SyracuseWordMatchesFrom w' v) (he' : evalSyracuseWord w' v = y)
    (hk : w'.length = w.length) (hA : w'.sum = w.sum)
    (hyn : y ≤ 21 * n) :
    (v : ℝ) ≤ 21 * Real.exp 27 * u := by
  have harrival : S^[w.length] u = n := by
    rw [← evalSyracuseWord_eq_iterate_of_matches w u hw, he]
  have hbudget := first_arrival_reciprocal_sum_lt_eighty_one hu huodd hnodd
    harrival hfirst
  exact WordProductEnvelope.same_profile_height_81 hu hn hw he hw' he' hk hA
    hbudget.le hyn

/-- The actual canonical sibling satisfies the same universal height bound.
Both exact words must exist; this theorem does not produce a matching. -/
theorem canonical_first_arrival_profile_height {w w' : List ℕ} {u v n : ℕ}
    (hu : 0 < u) (huodd : Odd u) (hn : 0 < n) (hnodd : Odd n)
    (hw : SyracuseWordMatchesFrom w u) (he : evalSyracuseWord w u = n)
    (hfirst : ∀ i < w.length, S^[i] u ≠ n)
    (hw' : SyracuseWordMatchesFrom w' v)
    (he' : evalSyracuseWord w' v = SiblingBasins.canonicalSibling n)
    (hk : w'.length = w.length) (hA : w'.sum = w.sum) :
    (v : ℝ) ≤ 21 * Real.exp 27 * u := by
  apply first_arrival_same_profile_height hu huodd hn hnodd hw he hfirst hw' he' hk hA
  have h := SiblingBasins.canonicalSibling_le n
  omega

/-- The first-arrival height bound also allows different lengths and totals
when the homogeneous slopes have a bounded ratio. -/
theorem first_arrival_comparable_slope_height {w w' : List ℕ} {u v n y : ℕ} {C : ℝ}
    (hu : 0 < u) (huodd : Odd u) (hn : 0 < n) (hnodd : Odd n) (hC : 0 ≤ C)
    (hw : SyracuseWordMatchesFrom w u) (he : evalSyracuseWord w u = n)
    (hfirst : ∀ i < w.length, S^[i] u ≠ n)
    (hw' : SyracuseWordMatchesFrom w' v) (he' : evalSyracuseWord w' v = y)
    (hslope : (2 : ℝ) ^ w'.sum * (3 : ℝ) ^ w.length ≤
      C * (2 : ℝ) ^ w.sum * (3 : ℝ) ^ w'.length)
    (hyn : y ≤ 21 * n) :
    (v : ℝ) ≤ 21 * C * Real.exp 27 * u := by
  have harrival : S^[w.length] u = n := by
    rw [← evalSyracuseWord_eq_iterate_of_matches w u hw, he]
  have hbudget := first_arrival_reciprocal_sum_lt_eighty_one hu huodd hnodd
    harrival hfirst
  have h := WordProductEnvelope.comparable_slope_height hu hn hC hw he hw' he'
    (le_of_lt hbudget) hslope
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : (y : ℝ) / n ≤ 21 := (div_le_iff₀ hn').mpr (by exact_mod_cast hyn)
  norm_num at h
  calc
    (v : ℝ) ≤ C * ((y : ℝ) / n) * Real.exp 27 * u := h
    _ ≤ C * 21 * Real.exp 27 * u :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hC)
          (Real.exp_nonneg 27)) (by positivity)
    _ = 21 * C * Real.exp 27 * u := by ring

end CollatzShadowing.FirstArrivalBudget
