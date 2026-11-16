/-
Nonrecurrent root pools formed by siblings attached to an injective orbit.

This connects the independently integrated root-pool charge mechanism to
the project's actual sibling geometry. It supplies an upper charge bound;
no lower mass estimate, relative basin-density comparison, or convergence
statement is assumed or proved.

AI-assisted development: Codex with Piero Borgatta, 2026-11-13.
-/

import CollatzShadowing.RootPoolBudget
import CollatzShadowing.SiblingBasins

namespace CollatzShadowing.SiblingPool

open scoped BigOperators
open RootPoolBudget

variable {α : Type*}

/-- Any subpool of a nonrecurrent pool is nonrecurrent. -/
theorem nonrecurrentPool_mono {f : α → α} {P Q : Set α}
    (hP : NonrecurrentPool f P) (hQP : Q ⊆ P) : NonrecurrentPool f Q := by
  intro r hr k hk hhit
  exact hP r (hQP hr) k hk (hQP hhit)

/-- All selected siblings of one injective spine form one nonrecurrent
pool, including exclusion of positive returns to the same sibling. -/
theorem sibling_range_nonrecurrent (f : α → α) (x : α) (y : ℕ → α)
    (hinj : Function.Injective (fun i : ℕ => f^[i] x))
    (hne : ∀ i : ℕ, y i ≠ f^[i] x)
    (hnext : ∀ i : ℕ, f (y i) = f^[i + 1] x) :
    NonrecurrentPool f (Set.range y) := by
  rintro r ⟨i, rfl⟩ k hk ⟨j, hhit⟩
  have hij : i = j := SiblingBasins.sibling_index_eq_of_reaches
    f x y hinj hne hnext hhit.symm
  subst j
  exact SiblingBasins.sibling_no_positive_return
    f x y hinj hne hnext i k hk hhit.symm

/-- Any specified collection of those siblings retains the pool property. -/
theorem sibling_subpool_nonrecurrent (f : α → α) (x : α) (y : ℕ → α)
    (hinj : Function.Injective (fun i : ℕ => f^[i] x))
    (hne : ∀ i : ℕ, y i ≠ f^[i] x)
    (hnext : ∀ i : ℕ, f (y i) = f^[i + 1] x)
    (P : Set α) (hP : P ⊆ Set.range y) : NonrecurrentPool f P :=
  nonrecurrentPool_mono (sibling_range_nonrecurrent f x y hinj hne hnext) hP

/-- The project's canonical Syracuse siblings form an actual root pool.
No positivity, parity, or density hypothesis on the spine is needed for
this geometric implication from orbit injectivity. -/
theorem canonical_range_nonrecurrent (x : ℕ)
    (hinj : Function.Injective (fun i : ℕ => S^[i] x)) :
    NonrecurrentPool S
      (Set.range (fun i : ℕ => SiblingBasins.canonicalSibling (S^[i] x))) := by
  apply sibling_range_nonrecurrent S x _ hinj
  · intro i
    exact (Nat.ne_of_lt (SiblingBasins.lt_canonicalSibling (S^[i] x))).symm
  · intro i
    rw [SiblingBasins.canonicalSibling_step, Function.iterate_succ_apply']

/-- A finite block of canonical siblings is nonrecurrent as a whole. -/
theorem canonical_finite_nonrecurrent (x : ℕ)
    (hinj : Function.Injective (fun i : ℕ => S^[i] x)) (I : Finset ℕ) :
    NonrecurrentPool S
      (↑(I.image (fun i => SiblingBasins.canonicalSibling (S^[i] x))) : Set ℕ) := by
  apply nonrecurrentPool_mono (canonical_range_nonrecurrent x hinj)
  intro r hr
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hr
  exact ⟨i, rfl⟩

/-- Distinct exact paths ending at the canonical sibling pool spend one
reciprocal charge at their common positive source. -/
theorem canonical_word_charge_le (x : ℕ)
    (hinj : Function.Injective (fun i : ℕ => S^[i] x))
    {z : ℕ} (hz : 0 < z) (W : Finset (List ℕ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w z)
    (hroot : ∀ w ∈ W, ∃ i : ℕ,
      evalSyracuseWord w z = SiblingBasins.canonicalSibling (S^[i] x)) :
    ∑ w ∈ W, reciprocalWeight w z ≤ 1 / (z : ℚ) := by
  apply sum_reciprocalWeight_pool_le (canonical_range_nonrecurrent x hinj) hz W hmatch
  intro w hw
  obtain ⟨i, hi⟩ := hroot w hw
  exact ⟨i, hi.symm⟩

/-- The same bound is independent of the size of a chosen finite block. -/
theorem canonical_finite_word_charge_le (x : ℕ)
    (hinj : Function.Injective (fun i : ℕ => S^[i] x)) (I : Finset ℕ)
    {z : ℕ} (hz : 0 < z) (W : Finset (List ℕ))
    (hmatch : ∀ w ∈ W, SyracuseWordMatchesFrom w z)
    (hroot : ∀ w ∈ W, evalSyracuseWord w z ∈
      I.image (fun i => SiblingBasins.canonicalSibling (S^[i] x))) :
    ∑ w ∈ W, reciprocalWeight w z ≤ 1 / (z : ℚ) :=
  sum_reciprocalWeight_pool_le (canonical_finite_nonrecurrent x hinj I) hz W hmatch hroot

/-- Labels can repeat a physical word only within an explicit coefficient
load M per word. The bound remains independent of the sibling block size. -/
theorem canonical_labeled_word_charge_le {ι : Type*} (x : ℕ)
    (hinj : Function.Injective (fun i : ℕ => S^[i] x)) (I : Finset ℕ)
    {z : ℕ} (hz : 0 < z) (J : Finset ι)
    (word : ι → List ℕ) (coefficient : ι → ℚ)
    {M : ℚ} (hM : 0 ≤ M)
    (hmatch : ∀ j ∈ J, SyracuseWordMatchesFrom (word j) z)
    (hroot : ∀ j ∈ J, evalSyracuseWord (word j) z ∈
      I.image (fun i => SiblingBasins.canonicalSibling (S^[i] x)))
    (hload : ∀ w ∈ J.image word,
      (∑ j ∈ J with word j = w, coefficient j) ≤ M) :
    ∑ j ∈ J, coefficient j * reciprocalWeight (word j) z ≤ M / (z : ℚ) := by
  classical
  exact sum_labeled_reciprocalWeight_pool_le
    (canonical_finite_nonrecurrent x hinj I) hz J word coefficient hM hmatch hroot hload

end CollatzShadowing.SiblingPool
