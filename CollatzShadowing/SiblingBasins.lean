/-
Finite disjoint-basin bounds for siblings attached to an injective orbit.
No density estimate, relative Harnack inequality, or termination result is
assumed or proved. The natural-number specialization concerns Syracuse
predecessors; a bridge from ordinary predecessors needs separate treatment.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-09-26.
-/

import CollatzShadowing.TwoSeed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CollatzShadowing
namespace SiblingBasins

open scoped BigOperators

variable {α : Type*}

/-- The target itself is included, through the zero iterate. -/
def basin (f : α → α) (target : α) : Set α :=
  {z | ∃ k : ℕ, f^[k] z = target}

section Abstract

variable (f : α → α) (x : α) (y : ℕ → α)
    (hinj : Function.Injective (fun i : ℕ => f^[i] x))
    (hne : ∀ i : ℕ, y i ≠ f^[i] x)
    (hnext : ∀ i : ℕ, f (y i) = f^[i + 1] x)

include hinj hne hnext

/-- A selected sibling is not any point of the injective forward orbit. -/
theorem sibling_ne_orbit (i j : ℕ) : y i ≠ f^[j] x := by
  intro heq
  have hidx : i + 1 = j + 1 := hinj (by
    change f^[i + 1] x = f^[j + 1] x
    rw [← hnext i, heq]
    exact (Function.iterate_succ_apply' f j x).symm)
  have hij : i = j := by omega
  subst j
  exact hne i heq

omit hinj hne in
/-- After its first step, a sibling follows the prescribed forward orbit. -/
theorem iterate_sibling_succ (i k : ℕ) :
    f^[k + 1] (y i) = f^[k + i + 1] x := by
  rw [Function.iterate_succ_apply, hnext i, ← Function.iterate_add_apply]
  simp only [Nat.add_assoc]

/-- No sibling has a positive return to itself. -/
theorem sibling_no_positive_return (i : ℕ) :
    ∀ k : ℕ, 0 < k → f^[k] (y i) ≠ y i := by
  intro k hk heq
  cases k with
  | zero => omega
  | succ k =>
      apply sibling_ne_orbit f x y hinj hne hnext i (k + i + 1)
      exact heq.symm.trans (iterate_sibling_succ f x y hnext i k)

/-- Reaching another sibling forces the two indices to be equal. -/
theorem sibling_index_eq_of_reaches {i j k : ℕ}
    (hreach : f^[k] (y i) = y j) : i = j := by
  cases k with
  | zero =>
      have heq : y i = y j := hreach
      have hidx : i + 1 = j + 1 := hinj (by
        change f^[i + 1] x = f^[j + 1] x
        rw [← hnext i, ← hnext j, heq])
      omega
  | succ k =>
      exact False.elim ((sibling_ne_orbit f x y hinj hne hnext j (k + i + 1))
        (hreach.symm.trans (iterate_sibling_succ f x y hnext i k)))

/-- Basins attached to different siblings are disjoint, including time zero. -/
theorem basins_pairwise_disjoint :
    Pairwise (fun i j : ℕ => Disjoint (basin f (y i)) (basin f (y j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  rcases le_total a b with hab | hba
  · apply hij
    apply sibling_index_eq_of_reaches f x y hinj hne hnext
      (i := i) (j := j) (k := b - a)
    rw [← ha, ← Function.iterate_add_apply, Nat.sub_add_cancel hab]
    exact hb
  · apply hij
    symm
    apply sibling_index_eq_of_reaches f x y hinj hne hnext
      (i := j) (j := i) (k := a - b)
    rw [← hb, ← Function.iterate_add_apply, Nat.sub_add_cancel hba]
    exact ha

end Abstract

/-- A finite source restriction, with no bound on the visiting time. -/
noncomputable def predecessorsWithin (f : α → α) (target : α) (A : Finset α) : Finset α := by
  classical
  exact A.filter (fun z => z ∈ basin f target)

section Finite

variable (f : α → α) (x : α) (y : ℕ → α)
    (hinj : Function.Injective (fun i : ℕ => f^[i] x))
    (hne : ∀ i : ℕ, y i ≠ f^[i] x)
    (hnext : ∀ i : ℕ, f (y i) = f^[i + 1] x)

include hinj hne hnext

/-- Nonnegative natural weights may account for multiplicities of a source.
This is a finite packing bound, with no asymptotic hypothesis. -/
theorem sum_weight_predecessors_le (I : Finset ℕ) (A : Finset α) (w : α → ℕ) :
    (∑ i ∈ I, ∑ z ∈ predecessorsWithin f (y i) A, w z) ≤ ∑ z ∈ A, w z := by
  classical
  have hd : (↑I : Set ℕ).PairwiseDisjoint (fun i => predecessorsWithin f (y i) A) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    have hi : z ∈ basin f (y i) := (Finset.mem_filter.mp hzi).2
    have hj : z ∈ basin f (y j) := (Finset.mem_filter.mp hzj).2
    exact Set.disjoint_left.mp (basins_pairwise_disjoint f x y hinj hne hnext hij) hi hj
  have hsub : I.biUnion (fun i => predecessorsWithin f (y i) A) ⊆ A := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨i, _, hzi⟩
    exact (Finset.mem_filter.mp hzi).1
  calc
    _ = ∑ z ∈ I.biUnion (fun i => predecessorsWithin f (y i) A), w z :=
      (Finset.sum_biUnion hd).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- Distinct sibling basins cannot use more sources than the supplied set. -/
theorem sum_card_predecessors_le (I : Finset ℕ) (A : Finset α) :
    (∑ i ∈ I, (predecessorsWithin f (y i) A).card) ≤ A.card := by
  simpa using sum_weight_predecessors_le f x y hinj hne hnext I A (fun _ => 1)

end Finite

/-- Choose a nearby sibling which is not divisible by three. -/
def canonicalSibling (n : ℕ) : ℕ :=
  if n % 3 = 1 then TwoSeed.lift n else TwoSeed.lift (TwoSeed.lift n)

theorem canonicalSibling_step (n : ℕ) : S (canonicalSibling n) = S n := by
  unfold canonicalSibling
  split_ifs <;> simp only [TwoSeed.lift_step]

theorem lt_canonicalSibling (n : ℕ) : n < canonicalSibling n := by
  unfold canonicalSibling
  split_ifs
  · exact TwoSeed.lt_lift n
  · exact (TwoSeed.lt_lift n).trans (TwoSeed.lt_lift (TwoSeed.lift n))

theorem canonicalSibling_le (n : ℕ) : canonicalSibling n ≤ 16 * n + 5 := by
  unfold canonicalSibling TwoSeed.lift
  split_ifs <;> omega

theorem canonicalSibling_odd (n : ℕ) : Odd (canonicalSibling n) := by
  unfold canonicalSibling
  split_ifs <;> exact TwoSeed.lift_odd _

theorem canonicalSibling_not_dvd_three {n : ℕ} (hthree : ¬ 3 ∣ n) :
    ¬ 3 ∣ canonicalSibling n := by
  have hnmod : n % 3 ≠ 0 := by
    intro h
    exact hthree (Nat.dvd_of_mod_eq_zero h)
  intro hdiv
  have hy := Nat.mod_eq_zero_of_dvd hdiv
  unfold canonicalSibling TwoSeed.lift at hy
  split_ifs at hy <;> omega

/-- The explicit arithmetic facts needed by the sibling construction.
Positivity and oddness of the source are not needed for these facts. -/
theorem canonicalSibling_spec {n : ℕ} (hthree : ¬ 3 ∣ n) :
    S (canonicalSibling n) = S n ∧ n < canonicalSibling n ∧
    canonicalSibling n ≤ 16 * n + 5 ∧ Odd (canonicalSibling n) ∧
    ¬ 3 ∣ canonicalSibling n :=
  ⟨canonicalSibling_step n, lt_canonicalSibling n, canonicalSibling_le n,
    canonicalSibling_odd n, canonicalSibling_not_dvd_three hthree⟩

/-- Finite weighted packing for canonical siblings on an injective Syracuse
orbit. This counts Syracuse basins, not ordinary Collatz basins. -/
theorem canonical_sum_weight_predecessors_le (x : ℕ)
    (hinj : Function.Injective (fun i : ℕ => S^[i] x))
    (I : Finset ℕ) (A : Finset ℕ) (w : ℕ → ℕ) :
    (∑ i ∈ I, ∑ z ∈ predecessorsWithin S (canonicalSibling (S^[i] x)) A, w z) ≤
      ∑ z ∈ A, w z := by
  apply sum_weight_predecessors_le S x (fun i => canonicalSibling (S^[i] x)) hinj
  · intro i
    exact (Nat.ne_of_lt (lt_canonicalSibling (S^[i] x))).symm
  · intro i
    rw [canonicalSibling_step, Function.iterate_succ_apply']

end SiblingBasins
end CollatzShadowing
