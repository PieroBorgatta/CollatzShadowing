/-
Finite phase-state API for Phase 8.4 of `TODO.md`.

This file introduces the finite state space used by the truncated
transfer operator. Later Phase-8 files will define the actual
`full/core/tail` matrices over this type.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-11.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Nat.ModEq
import CollatzShadowing.Basic

namespace CollatzShadowing

/-!
## Refined phase state

For a valuation cap `V`, the paper's refined phase state is

`(ν₂(t) ∧ V, odd(t) mod 4, h mod 4)`.

Here `ν₂(t) ∧ V` is represented as `min (ν₂ t) V`, with type
`Fin (V + 1)`. The residue coordinates are `Fin 4`.
-/

/-- Finite phase-state type at valuation cap `V`. -/
abbrev PhaseState (V : ℕ) :=
  Fin (V + 1) × Fin 4 × Fin 4

instance (V : ℕ) : Fintype (PhaseState V) := inferInstance
instance (V : ℕ) : DecidableEq (PhaseState V) := inferInstance

/-- Truncated 2-adic valuation `min (ν₂ t) V`, as an element of `Fin (V+1)`. -/
def cappedNu2 (V t : ℕ) : Fin (V + 1) :=
  ⟨min (ν₂ t) V, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Odd part proxy used for phase-state residue bookkeeping. -/
def oddPart (t : ℕ) : ℕ :=
  t / 2 ^ ν₂ t

/-- Residue modulo `4`, represented as `Fin 4`. -/
def mod4Fin (n : ℕ) : Fin 4 :=
  ⟨n % 4, Nat.mod_lt n (by decide)⟩

/-- The refined finite phase state associated to `(t, h)`. -/
def phaseState (V t h : ℕ) : PhaseState V :=
  (cappedNu2 V t, mod4Fin (oddPart t), mod4Fin h)

@[simp] theorem phaseState_fst (V t h : ℕ) :
    (phaseState V t h).1 = cappedNu2 V t :=
  rfl

@[simp] theorem phaseState_oddResidue (V t h : ℕ) :
    (phaseState V t h).2.1 = mod4Fin (oddPart t) :=
  rfl

@[simp] theorem phaseState_hResidue (V t h : ℕ) :
    (phaseState V t h).2.2 = mod4Fin h :=
  rfl

example : Fintype (PhaseState 10) := inferInstance

example (t h : ℕ) : (phaseState 10 t h).1.val ≤ 10 :=
  Nat.min_le_right _ _

/-!
## Finite transfer matrices

The empirical `full/core/tail` construction will later fill these
matrices with certified entries. At this layer we fix the types and the
algebraic certificate shape expected by Phase 8.5.
-/

/-- Transfer matrices on the finite phase-state space at cap `V`. -/
abbrev TransferMatrix (V : ℕ) :=
  Matrix (PhaseState V) (PhaseState V) NNReal

/-- Row-substochasticity for a finite non-negative transfer matrix. -/
def RowSubstochastic {V : ℕ} (M : TransferMatrix V) : Prop :=
  ∀ i, ∑ j, M i j ≤ 1

/--
Exact non-negative rational data for one imported matrix entry.

Phase-7 empirical probabilities have the form `count / source_events`;
this structure records that shape before it is converted to `NNReal`.
-/
structure ProbabilityEntry where
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator

/-- Interpret an exact imported probability entry as an `NNReal`. -/
noncomputable def ProbabilityEntry.toNNReal (p : ProbabilityEntry) : NNReal :=
  (p.numerator : NNReal) / (p.denominator : NNReal)

/-- Core part of a matrix under a decidable entry partition. -/
def splitCore {V : ℕ}
    (full : TransferMatrix V)
    (isCore : PhaseState V → PhaseState V → Prop)
    [DecidableRel isCore] : TransferMatrix V :=
  fun i j => if isCore i j then full i j else 0

/-- Tail part of a matrix under a decidable entry partition. -/
def splitTail {V : ℕ}
    (full : TransferMatrix V)
    (isCore : PhaseState V → PhaseState V → Prop)
    [DecidableRel isCore] : TransferMatrix V :=
  fun i j => if isCore i j then 0 else full i j

/-- The entry partition gives the desired decomposition by construction. -/
theorem split_full_eq_core_add_tail {V : ℕ}
    (full : TransferMatrix V)
    (isCore : PhaseState V → PhaseState V → Prop)
    [DecidableRel isCore] :
    full = splitCore full isCore + splitTail full isCore := by
  ext i j
  by_cases h : isCore i j <;> simp [splitCore, splitTail, h]

/-- The core split is pointwise bounded by the full matrix. -/
theorem splitCore_le_full {V : ℕ}
    (full : TransferMatrix V)
    (isCore : PhaseState V → PhaseState V → Prop)
    [DecidableRel isCore]
    (i j : PhaseState V) :
    splitCore full isCore i j ≤ full i j := by
  by_cases h : isCore i j <;> simp [splitCore, h]

/-- The tail split is pointwise bounded by the full matrix. -/
theorem splitTail_le_full {V : ℕ}
    (full : TransferMatrix V)
    (isCore : PhaseState V → PhaseState V → Prop)
    [DecidableRel isCore]
    (i j : PhaseState V) :
    splitTail full isCore i j ≤ full i j := by
  by_cases h : isCore i j <;> simp [splitTail, h]

/-- Core rows are substochastic whenever full rows are substochastic. -/
theorem splitCore_rowSubstochastic {V : ℕ}
    (full : TransferMatrix V)
    (isCore : PhaseState V → PhaseState V → Prop)
    [DecidableRel isCore]
    (hFull : RowSubstochastic full) :
    RowSubstochastic (splitCore full isCore) := by
  intro i
  exact (Finset.sum_le_sum fun j _ => splitCore_le_full full isCore i j).trans (hFull i)

/-- Tail rows are substochastic whenever full rows are substochastic. -/
theorem splitTail_rowSubstochastic {V : ℕ}
    (full : TransferMatrix V)
    (isCore : PhaseState V → PhaseState V → Prop)
    [DecidableRel isCore]
    (hFull : RowSubstochastic full) :
    RowSubstochastic (splitTail full isCore) := by
  intro i
  exact (Finset.sum_le_sum fun j _ => splitTail_le_full full isCore i j).trans (hFull i)

/--
The `full = core + tail` operator decomposition, together with
row-substochastic certificates for each displayed matrix.
-/
structure OperatorDecomposition (V : ℕ) where
  full : TransferMatrix V
  core : TransferMatrix V
  tail : TransferMatrix V
  full_eq_core_add_tail : full = core + tail
  full_rowSubstochastic : RowSubstochastic full
  core_rowSubstochastic : RowSubstochastic core
  tail_rowSubstochastic : RowSubstochastic tail

/--
Build an operator decomposition from a full matrix and a decidable
core/tail partition of its entries.
-/
def decompositionOfPartition {V : ℕ}
    (full : TransferMatrix V)
    (isCore : PhaseState V → PhaseState V → Prop)
    [DecidableRel isCore]
    (hFull : RowSubstochastic full)
    (hCore : RowSubstochastic (splitCore full isCore))
    (hTail : RowSubstochastic (splitTail full isCore)) :
    OperatorDecomposition V where
  full := full
  core := splitCore full isCore
  tail := splitTail full isCore
  full_eq_core_add_tail := split_full_eq_core_add_tail full isCore
  full_rowSubstochastic := hFull
  core_rowSubstochastic := hCore
  tail_rowSubstochastic := hTail

/--
Build an operator decomposition from a full matrix and a decidable
core/tail partition. Only the full matrix needs a row-substochastic
certificate; the split matrices inherit one by pointwise domination.
-/
def decompositionOfPartitionFromFull {V : ℕ}
    (full : TransferMatrix V)
    (isCore : PhaseState V → PhaseState V → Prop)
    [DecidableRel isCore]
    (hFull : RowSubstochastic full) :
    OperatorDecomposition V :=
  decompositionOfPartition full isCore hFull
    (splitCore_rowSubstochastic full isCore hFull)
    (splitTail_rowSubstochastic full isCore hFull)

/-- The zero decomposition, used as a baseline typechecking certificate. -/
def zeroOperatorDecomposition (V : ℕ) : OperatorDecomposition V where
  full := 0
  core := 0
  tail := 0
  full_eq_core_add_tail := by
    ext i j
    simp
  full_rowSubstochastic := by
    intro i
    simp
  core_rowSubstochastic := by
    intro i
    simp
  tail_rowSubstochastic := by
    intro i
    simp

example : (zeroOperatorDecomposition 10).full = 0 :=
  rfl

end CollatzShadowing
