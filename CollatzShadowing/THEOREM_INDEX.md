# Theorem index — `CollatzShadowing`

Curated declaration → file map for the hand-written modules (the ~300
theorems/lemmas; generated certificate witnesses are summarized at the end).
Each headline result notes the paper statement it formalizes. The project is
`sorry`-/`admit`-/`axiom`-free.

---

## Shadowing core

### `Basic.lean`
- `S` — accelerated Syracuse map on `ℕ`; `nu2Nat`, `ν₂`, `ν₂Z2` valuations.

### `Phantom.lean`
- `PhantomWord` — nonempty list of positive exponents; `length`, `A`.
- `affineFoldStep`, `Cw`, `Aw`, `Aw_eq_A` — the `(C_w, A_w)` fold (paper eq. 3.1).
- `qwRat`, `qwZ2` — rational / 2-adic fixed point `q_w = C_w/(2^A − 3^L)`.
- `B`, `aAt`, `B_closed_form` — periodic partial sums.

### `Syracuse2Adic.lean`
- `Syracuse2adic : ℤ₂ → ℤ₂` — total 2-adic extension of `S`.
- `Syracuse2adic_natCast` — bridge to the integer-level `S`.

### `Auxiliary.lean`
- `nu2Z2_three_mul` — `ν₂(3·n) = ν₂(n)` on `ℤ₂`.
- `qwOddDen` — every phantom has odd `q_w` denominator.
- `affine_difference` — `Sʲ(n) − Sʲ(q_w) = (3ʲ/2^{Bⱼ})(n − q_w)`.
- `nu2_stable_under_proximity` — ultrametric stability of `ν₂`.
- `B_bound_iff`, `B_mul_period`, `qw_orbit_matches`.

### `Shadowing.lean` — **paper Lemma 3.1**
- `exact_shadowing` — exact congruential shadowing.
- `exact_shadowing_periods` — periodic specialization (bound `b·A`).

### `NoInfinite.lean` — **paper Cor. 3.4 + v4 expanding-cycle result**
- `PhantomWord.Expansive`, `qwRat_neg_of_expansive`, `qwZ2_ne_natCast_of_expansive`.
- `no_infinite_period_congruence_expansive` — **Cor. 3.4** (no infinite periodic shadowing).
- `no_positive_endpoint_eventually_periodic_expansive_congruence` — **new in v4**: no positive integer endpoint stays in an expanding phantom's congruence classes for all periods (post-prefix form; generalizes Cor. 3.4 to the eventually-periodic case).

---

## Finite operator / Collatz–Wielandt layer

### `Operator.lean`
- `PhaseState V := Fin (V+1) × Fin 4 × Fin 4`, `phaseState`.
- `TransferMatrix`, `ProbabilityEntry`, `RowSubstochastic`.
- `OperatorDecomposition` — packages `full = core + tail` + row certificates.

### `Bound.lean` — **generic weighted Collatz–Wielandt bound**
- `FiniteCWCertificate`, `ClearedCWRowBound`, `FiniteMatrixBoundCertificate`.
- `spectralRadius_le_of_finiteCWCertificate` — passes a positive weighted CW certificate to Mathlib's real `spectralRadius`.
- `FiniteCWCertificate.add`, `OperatorDecomposition.spectralRadius_le_full` — the `core + tail` spectral corollary.

### `EpisodeGraph.lean`
- `EpisodeNode`, `TruncatedEpisodeGraph`, `SCC`, `Walk`, `reachable_of_walk`.
- `HubSCCCertificate`, `CriticalSCCCertificate` — finite SCC import format.

---

## Phase-10 finite bridges

### `WeakBridge.lean` — A0 weak bridge (finite, elementary)
- `weighted_action_diff_le` — weighted row-`L¹` drift bounds the `ℓ∞ → L¹(μ)` action error.
- `FiniteSplit.weighted_sum_le_low_plus_tail`, `weighted_dyadic_delta_boundary_le`.
- `BitLength.bitLength`, `bitLength_two_mul`; dyadic-boundary crossing counts `affineEndpointCrossingUnion_card_le` (`O(c·log N)`); `biAffineDelta_dyadicWeight_period_boundary_le`.
- `TailCount.dyadic_tail_count_mul_le`, `dyadic_tail_mass_le` — **exact** high-`ν₂` source-tail mass `≤ 2⁻ᴿ`.
- `LabelSplit.{BranchCounters, branchResolved, BranchCover, sourceResolved_of_all_branches_resolved}` — abstract finite label-split schema.

### `CollatzBridge.lean` — descent bridge + first-barrier (conditional)
**Proved (elementary):**
- `collatzStep`, `ClassicalCollatzConjecture`, `AcceleratedCollatzConjecture`, `UniformStrictDescentHypothesis`.
- `syracuse_pos`, `syracuse_odd`, `syracuse_lt_self_of_two_le_exponent`.
- `acceleratedCollatz_of_uniformStrictDescent` — descent hypothesis ⇒ accelerated Collatz.
- `acceleratedToClassicalBridge`, `classicalCollatz_of_uniformStrictDescent_provedBridge` — ⇒ classical Collatz.
- `SyracuseWordMatchesFrom`, `evalSyracuseWord_mul_pow_sum_eq_affine_of_matches` — exact affine word identity.
- `syracuseWordFormalFixedPoint`, `…_neg_of_expanding`; `a0SemanticDropCommonPrefix_matches_source_cylinder` (parametric prefix on `103+256t`).
- `AffineNatDropBranch.targetN_lt_sourceN_of_coeffDrop` (drop certificate); `AffineTBranch.not_nextLocalInteger_lt_sourceLocalInteger_of_coeffNondecreasing` (negative lemma: same-coordinate return branches cannot descend).

**Open hypotheses, isolated as named `Prop`s (NOT proved — by design):**
- `A0FirstBarrierExistsAll`, `A0FirstBarrierThresholdAutomatic`.
- `A0EndpointSuffixExitAll_of_firstBarrier` — *conditional* cylinder descent given the above.
- `GlobalDescentCover`, `classicalCollatz_of_globalDescentCover` — *conditional* global bridge.

---

## `Generated/` — machine-generated finite certificates

Verified by Lean; emitted by `../../scripts/phantom_taxonomy/` generators.

- `K16S16KDeterministicCW` — `k16s16KDeterministicGeneratedSpectralRadiusBound` (deterministic `(K,b)` bound `< 3/4`, `K₀=16`).
- `T10J32HighBitTailCW` — `t10j32HighBitTailSpectralRadiusBound_97_2000` (single-node `ρ ≤ 97/2000`); plus `…CWData`, `…CWRows00–13`.
- `K16S16KExactCWSummary`, `K16S16KSCC`, `K16S16KBridge` — 37-state empirical `(K,b)` CW + SCC + bridge.
- `T10CriticalSymbolic`, `T10J32HighBitTail` — exact `T=10` transfer-matrix imports.
- `A0ReturnBranches` — generated A0 return-branch data.

These contribute the bulk of the line/declaration count but are **generated**,
not hand-authored. See [`../../notes/PROJECT_STATISTICS.md`](https://github.com/PieroBorgatta/Collatz/blob/main/notes/PROJECT_STATISTICS.md)
for the hand-written vs generated split.
