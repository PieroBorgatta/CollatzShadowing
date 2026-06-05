# Phase 8.1 episode-graph/operator API inventory

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-10.

This note records the Mathlib API choices for Phase 8 of `TODO.md`.
The companion Lean scratch file is `CollatzShadowing/EpisodeInventory.lean`.

## Directed graph model

Mathlib's standard graph APIs found in this checkout are not a direct
fit for the episode graph:

- `Mathlib.Combinatorics.SimpleGraph.Basic` defines `SimpleGraph` as an
  irreflexive symmetric relation, hence an undirected graph.
- `Mathlib.Combinatorics.Graph.Basic` is also an undirected multigraph
  interface.
- No production `SimpleDigraph` API was found in the current Mathlib
  checkout. `Mathlib.Tactic.Order.Graph.Tarjan` exists, but it belongs
  to tactic internals and should not be a dependency for the paper
  formalization.

Recommended Phase-8 choice: define the episode graph locally as a
directed relation.

```lean
abbrev EpisodeRel (α : Type*) := α → α → Prop
def Reachable (E : EpisodeRel α) (u v : α) : Prop :=
  Relation.ReflTransGen E u v
def SameSCC (E : EpisodeRel α) (u v : α) : Prop :=
  Reachable E u v ∧ Reachable E v u
```

This gives a small, stable target for `EpisodeGraph.lean`. Finite SCC
computation can later be implemented by enumeration over `Finset.univ`
or imported from external certificates, while the mathematical SCC
notion remains mutual reachability.

## Finite episode nodes

The paper-level node is morally `(k, c, b)`. For decidable finite
cutoffs, use bounded products such as:

```lean
abbrev EpisodeNode := Fin Kmax × Fin Cmax × Fin Bmax
```

Products of `Fin` automatically provide `Fintype` and `DecidableEq`.
If Phase 8 needs a filtered universe, prefer a subtype over the product
with an explicit predicate, then derive finite enumeration from the
ambient product.

## Matrix and non-negativity API

Relevant imports checked by `EpisodeInventory.lean`:

- `Mathlib.Data.Matrix.Basic`
- `Mathlib.Data.Matrix.Mul`
- `Mathlib.Data.NNReal.Basic`
- `Mathlib.LinearAlgebra.Matrix.Stochastic`

The useful declarations include:

- `Matrix.mulVec`
- `Matrix.rowStochastic`
- `Matrix.mem_rowStochastic_iff_sum`

For Phase 8, `Matrix PhaseState PhaseState NNReal` is the most convenient
first representation: non-negativity is encoded in the entry type
(`NNReal` is Mathlib's non-negative real type, often written
mathematically as `ℝ≥0`).
Substochastic rows can be stated locally as:

```lean
def rowSubstochastic (M : Matrix PhaseState PhaseState NNReal) : Prop :=
  ∀ i, ∑ j, M i j ≤ 1
```

This is likely simpler than starting with real matrices plus a separate
pointwise non-negativity hypothesis.

## Spectrum and Collatz-Wielandt

Mathlib has general spectrum API and matrix spectrum bridges, e.g.
`Mathlib.Analysis.Matrix.Spectrum`, plus Hermitian spectral theory.
Those files are not a ready-made Perron-Frobenius or
Collatz-Wielandt theorem for arbitrary finite non-negative matrices.

Recommended formalization route:

1. First define certificate predicates over `ℝ≥0` matrices:

   ```lean
   def cwCertificate
       (M : Matrix PhaseState PhaseState NNReal)
       (v : PhaseState → NNReal)
       (alpha : NNReal) : Prop :=
     (∀ i, 0 < v i) ∧ ∀ i, Matrix.mulVec M v i ≤ alpha * v i
   ```

2. Use exact rational or `NNReal` data generated from the Phase-7
   empirical certificates to close finite certificate goals.

3. Only after the finite certificate layer is stable, connect this
   predicate to a spectral-radius statement if the v3 paper really needs
   the formal theorem in spectral language.

This avoids blocking Phase 8 on a full Perron-Frobenius development.

## Phase-8 implications

- Task 8.2 should update the wording from `SimpleDigraph` to the local
  directed-relation model unless a future Mathlib update adds a stable
  directed graph API.
- Task 8.3 should formalize SCCs as mutual `Relation.ReflTransGen`
  reachability first. A computational SCC algorithm can be a later
  certificate importer rather than the foundational definition.
- Tasks 8.5-8.7 should initially target row-substochastic finite
  matrices and Collatz-Wielandt-style certificates over `NNReal`, then
  bridge to spectrum only if needed.

## Implemented Phase-8 Production API

The inventory recommendations above have now been realized as follows:

- `EpisodeGraph.lean` uses `EpisodeRel α := α → α → Prop` with
  `Relation.ReflTransGen` reachability, finite truncated nodes, finite
  walks, hub-based SCC certificates, and critical-SCC certificate
  packaging.
- `Operator.lean` defines `PhaseState V`, `TransferMatrix V`,
  `RowSubstochastic`, `splitCore`, `splitTail`, and
  `OperatorDecomposition`.
- `Generated/T10CriticalSymbolic.lean` imports the exact empirical
  `T = 10` critical-symbolic `TransferMatrix`, proves
  `t10CriticalSymbolicFull_rowSubstochastic`, and packages the baseline
  decomposition `t10CriticalSymbolicBaselineDecomposition` with
  `core = full` and `tail = 0`.
- `Generated/T10J32HighBitTail.lean` imports the exact empirical
  `T = 10, j = 32` majority-signature `core` and `tail` matrices over
  `TransferMatrix 13`, defines `full` as their sum, proves generated
  row-substochasticity certificates by per-row supports, and packages
  `t10j32HighBitTailDecomposition`.
- `Bound.lean` defines the generic finite certificate layer:
  `FiniteCWBasis`, `FiniteCWCertificate`, `ClearedCWRowBound`,
  `EvaluatedCWRowBound`, and the additive `core + tail` certificate
  theorems, plus the weighted diagonal-conjugacy bridge from finite
  CW certificates to Mathlib `spectralRadius`.
- `Generated/K16S16KExactCWSummary.lean` imports the exact empirical
  `K,b` JSON certificate as a 37-state `NNReal` matrix and proves
  `k16s16KFiniteCWCertificate`.
- `Generated/K16S16KDeterministicCW.lean` imports the deterministic
  finite residue-cell `K,b` JSON certificate as a separate 37-state
  `NNReal` matrix and proves
  `k16s16KDeterministicFiniteCWCertificate` plus the induced
  `k16s16KDeterministicGeneratedSpectralRadiusBound` with alpha
  `3/4`.
- `Generated/K16S16KLB5DeterministicCW.lean` and
  `Generated/K16S16KLB6DeterministicCW.lean` import the deterministic
  `lift_bits = 5` and `lift_bits = 6` sensitivity certificates.  They
  prove `k16s16KLB5DeterministicGeneratedSpectralRadiusBound` and
  `k16s16KLB6DeterministicGeneratedSpectralRadiusBound`, respectively.
  These are Lean-checked sensitivity bounds, not convergence statements.

`Generated/K16S16KBridge.lean` applies the spectral bridge to the
37-state generated certificate as `k16s16KSpectralRadiusBound`.
