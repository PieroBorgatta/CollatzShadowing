/-
Mathlib API scratchpad for Phase 8.1 of `TODO.md`.

This file records the Lean-side choices behind
`CollatzShadowing/EPISODE_INVENTORY.md`. It is intentionally small:
the production episode graph and operator modules will be introduced
in later Phase-8 tasks.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-10.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Stochastic

namespace CollatzShadowing

/-!
## Directed episode relations

Mathlib's `SimpleGraph` and `Graph` APIs are undirected. For the
episode graph, the Phase-8 starting point is therefore a local directed
edge relation together with Mathlib's relation-transitive-closure API.
-/

/-- A directed episode graph represented by its edge relation. -/
abbrev EpisodeRel (α : Type*) :=
  α → α → Prop

/-- Reachability in a directed episode relation. -/
def Reachable {α : Type*} (E : EpisodeRel α) (u v : α) : Prop :=
  Relation.ReflTransGen E u v

/-- Strong-component equivalence, expressed as mutual reachability. -/
def SameSCC {α : Type*} (E : EpisodeRel α) (u v : α) : Prop :=
  Reachable E u v ∧ Reachable E v u

/-- A bounded toy node universe for checking finite-type plumbing. -/
abbrev InventoryEpisodeNode :=
  Fin 17 × Fin 8 × Fin 4

instance : Fintype InventoryEpisodeNode := inferInstance
instance : DecidableEq InventoryEpisodeNode := inferInstance

/-- Identity-edge toy graph used only to check reachability notation. -/
def toyEpisodeEdge (u v : InventoryEpisodeNode) : Prop :=
  u = v

example (u : InventoryEpisodeNode) : Reachable toyEpisodeEdge u u :=
  Relation.ReflTransGen.refl

example (u : InventoryEpisodeNode) : SameSCC toyEpisodeEdge u u :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

/-!
## Non-negative finite transfer matrices

For first certificates, entries in `ℝ≥0` make non-negativity part of
the type. Row-substochasticity and Collatz-Wielandt-style vector
certificates can be stated directly over finite matrices.
-/

/-- Small toy phase-state universe for matrix API checks. -/
abbrev InventoryPhaseState :=
  Fin 4

/-- Row-substochasticity for a non-negative matrix. -/
def rowSubstochastic (M : Matrix InventoryPhaseState InventoryPhaseState NNReal) : Prop :=
  ∀ i, ∑ j, M i j ≤ 1

example : rowSubstochastic (0 : Matrix InventoryPhaseState InventoryPhaseState NNReal) := by
  intro i
  simp

/--
A finite Collatz-Wielandt-style certificate: a positive vector `v`
whose image under `M` is pointwise bounded by `alpha • v`.
-/
def cwCertificate
    (M : Matrix InventoryPhaseState InventoryPhaseState NNReal)
    (v : InventoryPhaseState → NNReal)
    (alpha : NNReal) : Prop :=
  (∀ i, 0 < v i) ∧ ∀ i, Matrix.mulVec M v i ≤ alpha * v i

example :
    cwCertificate (0 : Matrix InventoryPhaseState InventoryPhaseState NNReal) (fun _ => 1) 0 := by
  constructor
  · intro i
    norm_num
  · intro i
    simp [Matrix.mulVec]

/-- Mathlib's built-in row-stochastic API is available over ordered rings such as `ℝ`. -/
example {M : Matrix InventoryPhaseState InventoryPhaseState ℝ} :
    M ∈ Matrix.rowStochastic ℝ InventoryPhaseState ↔
      (∀ i j, 0 ≤ M i j) ∧ ∀ i, ∑ j, M i j = 1 :=
  Matrix.mem_rowStochastic_iff_sum

end CollatzShadowing
