/-
An iterate-injectivity estimate on finite sets transfers to an injective
finite orbit segment after deleting at most N terminal points.

This is the finite adapter used in the November sparsity investigation.
The numerical window estimate is an explicit hypothesis; neither that
estimate nor a reciprocal-sum bound is proved by this module.

AI-assisted development: Codex with Piero Borgatta, 2026-11-13.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Tactic

namespace CollatzShadowing.FiniteOrbitTransfer

variable {α : Type*} [DecidableEq α]

/-- The values at times 0 through length-1, including an empty segment. -/
def segment (f : α → α) (x : α) (length : ℕ) : Finset α :=
  (Finset.range length).image (fun i => f^[i] x)

/-- On a segment without repeated values, the N-th iterate is injective
on all but its last N values. No condition on the later orbit is used. -/
theorem iterate_injOn_prefix (f : α → α) (x : α) (length N : ℕ)
    (hinj : ∀ i < length, ∀ j < length, f^[i] x = f^[j] x → i = j) :
    Set.InjOn (f^[N]) (↑(segment f x (length - N)) : Set α) := by
  intro a ha b hb hab
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  have hi' : i < length - N := Finset.mem_range.mp hi
  have hj' : j < length - N := Finset.mem_range.mp hj
  have hshift : N + i = N + j := hinj (N + i) (by omega) (N + j) (by omega)
    (by simpa only [Function.iterate_add_apply] using hab)
  have hij : i = j := by omega
  rw [hij]

/-- Removing the terminal N points costs at most N members of any window. -/
theorem window_card_le_prefix_add (f : α → α) (x : α) (length N : ℕ)
    (window : Finset α) :
    ((segment f x length).filter (fun a => a ∈ window)).card ≤
      ((segment f x (length - N)).filter (fun a => a ∈ window)).card + N := by
  let tail : Finset α := (Finset.Ico (length - N) length).image (fun i => f^[i] x)
  have htail : tail.card ≤ N := by
    have h := Finset.card_image_le
      (s := Finset.Ico (length - N) length) (f := fun i => f^[i] x)
    have hlen : length - (length - N) ≤ N := by omega
    exact h.trans (by simpa using hlen)
  have hsub : (segment f x length).filter (fun a => a ∈ window) ⊆
      ((segment f x (length - N)).filter (fun a => a ∈ window)) ∪ tail := by
    intro a ha
    obtain ⟨ha, hw⟩ := Finset.mem_filter.mp ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hi' : i < length := Finset.mem_range.mp hi
    by_cases hip : i < length - N
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hip, rfl⟩, hw⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨i, Finset.mem_Ico.mpr ⟨by omega, hi'⟩, rfl⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left htail _))

/-- A window bound needing only N-step injectivity applies to a finite
injective trajectory with an explicit N-point terminal error. -/
theorem window_bound_of_iterate_injective_estimate
    (f : α → α) (x : α) (length N C : ℕ) (window : Finset α)
    (hinj : ∀ i < length, ∀ j < length, f^[i] x = f^[j] x → i = j)
    (hwindow : ∀ A : Finset α, A ⊆ window →
      Set.InjOn (f^[N]) (↑A : Set α) → A.card ≤ C) :
    ((segment f x length).filter (fun a => a ∈ window)).card ≤ C + N := by
  have hp : Set.InjOn (f^[N])
      (↑((segment f x (length - N)).filter (fun a => a ∈ window)) : Set α) := by
    apply (iterate_injOn_prefix f x length N hinj).mono
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hbound := hwindow ((segment f x (length - N)).filter (fun a => a ∈ window))
    (by intro a ha; exact (Finset.mem_filter.mp ha).2) hp
  exact (window_card_le_prefix_add f x length N window).trans (Nat.add_le_add_right hbound N)

end CollatzShadowing.FiniteOrbitTransfer
