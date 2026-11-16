# Theorem index — `CollatzShadowing`

Curated declaration → file map for the AI-authored proof modules (including
the later arithmetic and trace developments; generated certificate witnesses
are summarized at the end).
Each headline result notes the paper statement it formalizes. The sources
have no `sorry`, `admit`, or project-declared `axiom`; finite proofs using
`native_decide` trust the native compiler. See [STATUS](../STATUS.md) for
the axioms audit and pinned-toolchain caveat.

---

## 16 November 2026 arithmetic follow-up

The four modules below add 28 public theorem declarations. The full build
passes (3404 jobs); the strict transitive audit covers all 68 compiled
declarations, including five encoded-private helpers. These are finite
statements: no kernel lower bound, asymptotic recoding theorem or Collatz
conclusion is imported. Catalogue parameter bounds are existential. A
truncated collision defect is an upper bound on the complete defect; lower
allocations are certificates only when they extend to the full law.
See the [integration receipt](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15_three_hours/verification/integration_receipt.json).

### `FiniteHorizonBudget.lean`

- `step_shifted_growth` — [FiniteHorizonBudget.lean:20](FiniteHorizonBudget.lean#L20).
- `iterate_shifted_growth` — [FiniteHorizonBudget.lean:36](FiniteHorizonBudget.lean#L36).
- `source_lower_of_horizon` — [FiniteHorizonBudget.lean:54](FiniteHorizonBudget.lean#L54).
- `reciprocal_square_tail` — [FiniteHorizonBudget.lean:100](FiniteHorizonBudget.lean#L100).
- `tilted_tail_catalogue` — [FiniteHorizonBudget.lean:130](FiniteHorizonBudget.lean#L130).
- `tilted_horizon_catalogue` — [FiniteHorizonBudget.lean:170](FiniteHorizonBudget.lean#L170).
- `tilted_fixed_depth_tail` — [FiniteHorizonBudget.lean:184](FiniteHorizonBudget.lean#L184).
- `tilted_nonreturn_horizon` — [FiniteHorizonBudget.lean:201](FiniteHorizonBudget.lean#L201).

### `QuadraticOccupation.lean`

- `visitConstant_nonneg` — [QuadraticOccupation.lean:29](QuadraticOccupation.lean#L29).
- `squareLoss_pos` — [QuadraticOccupation.lean:33](QuadraticOccupation.lean#L33).
- `potential_sq_sub_succ` — [QuadraticOccupation.lean:41](QuadraticOccupation.lean#L41).
- `sum_squareLoss_range` — [QuadraticOccupation.lean:51](QuadraticOccupation.lean#L51).
- `sum_squareLoss_finset_le` — [QuadraticOccupation.lean:61](QuadraticOccupation.lean#L61).
- `sum_weight_sq_visits_le` — [QuadraticOccupation.lean:72](QuadraticOccupation.lean#L72).
- `sum_wordWeight_sq_fiber_le` — [QuadraticOccupation.lean:94](QuadraticOccupation.lean#L94).
- `tilted_catalogue_le` — [QuadraticOccupation.lean:117](QuadraticOccupation.lean#L117).

### `BoundedSlopeCatalogue.lean`

- `subcatalogue_card_le` — [BoundedSlopeCatalogue.lean:44](BoundedSlopeCatalogue.lean#L44).
- `catalogue_finite` — [BoundedSlopeCatalogue.lean:66](BoundedSlopeCatalogue.lean#L66).
- `catalogue_ncard_le` — [BoundedSlopeCatalogue.lean:88](BoundedSlopeCatalogue.lean#L88).
- `catalogue_parameter_bounds` — [BoundedSlopeCatalogue.lean:99](BoundedSlopeCatalogue.lean#L99).
- `catalogue_source_bound` — [BoundedSlopeCatalogue.lean:111](BoundedSlopeCatalogue.lean#L111).

### `SpineDispersion.lean`

- `collision_defect_le_selected` — [SpineDispersion.lean:26](SpineDispersion.lean#L26).
- `collision_defect_nonneg` — [SpineDispersion.lean:33](SpineDispersion.lean#L33).
- `collision_defect_ge_of_two_branches` — [SpineDispersion.lean:48](SpineDispersion.lean#L48).
- `collision_defect_ge_lower_allocations` — [SpineDispersion.lean:95](SpineDispersion.lean#L95).
- `ratio_square_defect_le` — [SpineDispersion.lean:123](SpineDispersion.lean#L123).
- `ratio_square_prefix_budget` — [SpineDispersion.lean:151](SpineDispersion.lean#L151).
- `collision_spine_budget` — [SpineDispersion.lean:173](SpineDispersion.lean#L173).

## 15 November 2026 integration

The 56 public theorem declarations below include the universal finite-injective
reciprocal budget and its first-arrival height application. The seven modules
have passed the full build and a strict transitive audit of all 136 compiled
declarations, including encoded-private helpers. Relative mass, Evertse's
asymptotic application and external density identities are not imported. See
the [integration receipt](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15/verification/integration_receipt.json).

### `OrbitReciprocal.lean`

- `iterate_affine_lt` — [OrbitReciprocal.lean:21](OrbitReciprocal.lean#L21).
- `iterate_lt_two_mul_three_pow` — [OrbitReciprocal.lean:42](OrbitReciprocal.lean#L42).
- `last_bit_complement` — [OrbitReciprocal.lean:50](OrbitReciprocal.lean#L50).
- `parity_moment_pair` — [OrbitReciprocal.lean:61](OrbitReciprocal.lean#L61).
- `parity_moment` — [OrbitReciprocal.lean:81](OrbitReciprocal.lean#L81).
- `dyadic_fiber_card_le` — [OrbitReciprocal.lean:100](OrbitReciprocal.lean#L100).
- `dyadic_light_card_le` — [OrbitReciprocal.lean:141](OrbitReciprocal.lean#L141).
- `heavy_residue_card_bound` — [OrbitReciprocal.lean:155](OrbitReciprocal.lean#L155).
- `dyadic_heavy_card_bound` — [OrbitReciprocal.lean:182](OrbitReciprocal.lean#L182).
- `dyadic_card_bound` — [OrbitReciprocal.lean:208](OrbitReciprocal.lean#L208).
- `finite_orbit_dyadic_card_bound` — [OrbitReciprocal.lean:245](OrbitReciprocal.lean#L245).
- `heavyEnvelope_sum_le` — [OrbitReciprocal.lean:311](OrbitReciprocal.lean#L311).
- `lightEnvelope_sum_le` — [OrbitReciprocal.lean:322](OrbitReciprocal.lean#L322).
- `terminal_budget_sum_le` — [OrbitReciprocal.lean:344](OrbitReciprocal.lean#L344).
- `reciprocal_sum_le_band_sum` — [OrbitReciprocal.lean:352](OrbitReciprocal.lean#L352).
- `segment_pos` — [OrbitReciprocal.lean:392](OrbitReciprocal.lean#L392).
- `finite_orbit_reciprocal_sum_le` — [OrbitReciprocal.lean:420](OrbitReciprocal.lean#L420).
- `finite_orbit_reciprocal_sum_lt_eighty_one` — [OrbitReciprocal.lean:469](OrbitReciprocal.lean#L469).
- `finite_orbit_reciprocal_sum_real_lt_eighty_one` — [OrbitReciprocal.lean:475](OrbitReciprocal.lean#L475).

### `WordProductEnvelope.lean`

- `inflation_succ` — [WordProductEnvelope.lean:25](WordProductEnvelope.lean#L25).
- `inflation_eq_product` — [WordProductEnvelope.lean:39](WordProductEnvelope.lean#L39).
- `inflation_le_exp_of_reciprocal_budget` — [WordProductEnvelope.lean:47](WordProductEnvelope.lean#L47).
- `exact_word_inflation` — [WordProductEnvelope.lean:74](WordProductEnvelope.lean#L74).
- `same_profile_height` — [WordProductEnvelope.lean:82](WordProductEnvelope.lean#L82).
- `same_profile_height_81` — [WordProductEnvelope.lean:113](WordProductEnvelope.lean#L113).
- `comparable_slope_height` — [WordProductEnvelope.lean:133](WordProductEnvelope.lean#L133).

### `FirstArrivalBudget.lean`

- `first_arrival_injective` — [FirstArrivalBudget.lean:24](FirstArrivalBudget.lean#L24).
- `exponent_pos_of_odd` — [FirstArrivalBudget.lean:42](FirstArrivalBudget.lean#L42).
- `orbit_odd` — [FirstArrivalBudget.lean:53](FirstArrivalBudget.lean#L53).
- `shortcut_clock` — [FirstArrivalBudget.lean:59](FirstArrivalBudget.lean#L59).
- `clock_strictMono` — [FirstArrivalBudget.lean:69](FirstArrivalBudget.lean#L69).
- `episode_internal_even` — [FirstArrivalBudget.lean:76](FirstArrivalBudget.lean#L76).
- `odd_shortcut_hit` — [FirstArrivalBudget.lean:96](FirstArrivalBudget.lean#L96).
- `accelerated_first_is_shortcut_first` — [FirstArrivalBudget.lean:126](FirstArrivalBudget.lean#L126).
- `accelerated_sum_le_shortcut_sum` — [FirstArrivalBudget.lean:141](FirstArrivalBudget.lean#L141).
- `first_arrival_reciprocal_sum_lt_eighty_one` — [FirstArrivalBudget.lean:175](FirstArrivalBudget.lean#L175).
- `first_arrival_same_profile_height` — [FirstArrivalBudget.lean:193](FirstArrivalBudget.lean#L193).
- `canonical_first_arrival_profile_height` — [FirstArrivalBudget.lean:210](FirstArrivalBudget.lean#L210).
- `first_arrival_comparable_slope_height` — [FirstArrivalBudget.lean:224](FirstArrivalBudget.lean#L224).

### `TwoEditSparsity.lean`

- `positive_residual_identity` — [TwoEditSparsity.lean:18](TwoEditSparsity.lean#L18).
- `positive_residual_dvd` — [TwoEditSparsity.lean:30](TwoEditSparsity.lean#L30).
- `negative_residual_identity` — [TwoEditSparsity.lean:43](TwoEditSparsity.lean#L43).
- `negative_residual_dvd` — [TwoEditSparsity.lean:53](TwoEditSparsity.lean#L53).
- `exact_word_exponent_budget` — [TwoEditSparsity.lean:66](TwoEditSparsity.lean#L66).

### `TraceDensityBridge.lean`

- `density_of_trace_comparison` — [TraceDensityBridge.lean:21](TraceDensityBridge.lean#L21).
- `trace_of_density_comparison` — [TraceDensityBridge.lean:62](TraceDensityBridge.lean#L62).
- `density_of_trace_floor_and_upper` — [TraceDensityBridge.lean:102](TraceDensityBridge.lean#L102).
- `summed_density_of_normalized_trace_comparison` — [TraceDensityBridge.lean:123](TraceDensityBridge.lean#L123).

### `CycleMinimumProduct.lean`

- `path_minimum_product_bound` — [CycleMinimumProduct.lean:19](CycleMinimumProduct.lean#L19).
- `cycle_minimum_product_bound` — [CycleMinimumProduct.lean:58](CycleMinimumProduct.lean#L58).
- `cycle_log_gap_le` — [CycleMinimumProduct.lean:68](CycleMinimumProduct.lean#L68).

### `IntegerAtomTilt.lean`

- `sum_reciprocal_sq_finset_le_two` — [IntegerAtomTilt.lean:42](IntegerAtomTilt.lean#L42).
- `wordWeight_le_target` — [IntegerAtomTilt.lean:58](IntegerAtomTilt.lean#L58).
- `tilted_catalogue_le_of_source_injective` — [IntegerAtomTilt.lean:73](IntegerAtomTilt.lean#L73).
- `tilted_integer_atom_le` — [IntegerAtomTilt.lean:110](IntegerAtomTilt.lean#L110).
- `tilted_nonreturn_catalogue_le` — [IntegerAtomTilt.lean:126](IntegerAtomTilt.lean#L126).

---

## 13 November 2026 integration

These 69 public declarations were integrated on 13 November. At that date the numerical finite-orbit sparsity and height bounds were paper deductions; the 15 November modules above now supply the explicit universal result. `FiniteOrbitTransfer` itself still supplies only the finite adapter. See the [sprint report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-13/REPORT_IT.md).

### `RootPoolBudget.lean`

- `normalizedWeight_nonneg` — [RootPoolBudget.lean:31](RootPoolBudget.lean#L31).
- `normalizedWeight_eq_loss` — [RootPoolBudget.lean:37](RootPoolBudget.lean#L37).
- `sum_normalizedWeight_le` — [RootPoolBudget.lean:46](RootPoolBudget.lean#L46).
- `sum_selected_le` — [RootPoolBudget.lean:63](RootPoolBudget.lean#L63).
- `sum_labeled_normalizedWeight_le` — [RootPoolBudget.lean:73](RootPoolBudget.lean#L73).
- `normalized_source_fiber_bound` — [RootPoolBudget.lean:109](RootPoolBudget.lean#L109).
- `distinct_sources_of_normalized_mass` — [RootPoolBudget.lean:136](RootPoolBudget.lean#L136).
- `pool_visit_time_unique` — [RootPoolBudget.lean:164](RootPoolBudget.lean#L164).
- `word_eq_of_pool` — [RootPoolBudget.lean:178](RootPoolBudget.lean#L178).
- `reciprocalWeight_le_initial` — [RootPoolBudget.lean:194](RootPoolBudget.lean#L194).
- `sum_reciprocalWeight_pool_le` — [RootPoolBudget.lean:208](RootPoolBudget.lean#L208).
- `sum_labeled_reciprocalWeight_pool_le` — [RootPoolBudget.lean:231](RootPoolBudget.lean#L231).

### `SiblingPool.lean`

- `nonrecurrentPool_mono` — [SiblingPool.lean:23](SiblingPool.lean#L23).
- `sibling_range_nonrecurrent` — [SiblingPool.lean:30](SiblingPool.lean#L30).
- `sibling_subpool_nonrecurrent` — [SiblingPool.lean:43](SiblingPool.lean#L43).
- `canonical_range_nonrecurrent` — [SiblingPool.lean:53](SiblingPool.lean#L53).
- `canonical_finite_nonrecurrent` — [SiblingPool.lean:64](SiblingPool.lean#L64).
- `canonical_word_charge_le` — [SiblingPool.lean:75](SiblingPool.lean#L75).
- `canonical_finite_word_charge_le` — [SiblingPool.lean:88](SiblingPool.lean#L88).
- `canonical_labeled_word_charge_le` — [SiblingPool.lean:99](SiblingPool.lean#L99).

### `CapacityAllocation.lean`

- `capped_cell_bound` — [CapacityAllocation.lean:26](CapacityAllocation.lean#L26).
- `mass_le_threshold_cost` — [CapacityAllocation.lean:39](CapacityAllocation.lean#L39).
- `threshold_lower_bound` — [CapacityAllocation.lean:52](CapacityAllocation.lean#L52).
- `threshold_cell_identity` — [CapacityAllocation.lean:70](CapacityAllocation.lean#L70).
- `threshold_allocation_exact` — [CapacityAllocation.lean:84](CapacityAllocation.lean#L84).
- `threshold_certificate_le_competitor` — [CapacityAllocation.lean:108](CapacityAllocation.lean#L108).
- `threshold_at_score_upper_bound` — [CapacityAllocation.lean:120](CapacityAllocation.lean#L120).

### `JointAtomDictionary.lean`

- `admissible_iff_residue` — [JointAtomDictionary.lean:34](JointAtomDictionary.lean#L34).
- `inverseSource_affine` — [JointAtomDictionary.lean:43](JointAtomDictionary.lean#L43).
- `inverseSource_pos` — [JointAtomDictionary.lean:50](JointAtomDictionary.lean#L50).
- `source_odd_of_matches` — [JointAtomDictionary.lean:59](JointAtomDictionary.lean#L59).
- `inverseSource_spec` — [JointAtomDictionary.lean:75](JointAtomDictionary.lean#L75).
- `admissible_of_exact` — [JointAtomDictionary.lean:86](JointAtomDictionary.lean#L86).
- `admissible_iff_exact` — [JointAtomDictionary.lean:102](JointAtomDictionary.lean#L102).
- `inverseSource_le_iff` — [JointAtomDictionary.lean:114](JointAtomDictionary.lean#L114).
- `inverseSource_injective_at_length` — [JointAtomDictionary.lean:122](JointAtomDictionary.lean#L122).
- `card_admissible_image` — [JointAtomDictionary.lean:136](JointAtomDictionary.lean#L136).

### `AffinePositivity.lean`

- `integer_source_pos` — [AffinePositivity.lean:18](AffinePositivity.lean#L18).
- `height_of_ternary_congruence` — [AffinePositivity.lean:67](AffinePositivity.lean#L67).
- `admissible_iff_ternary_congruence` — [AffinePositivity.lean:83](AffinePositivity.lean#L83).
- `exact_source_iff_ternary_congruence` — [AffinePositivity.lean:96](AffinePositivity.lean#L96).
- `card_ternary_atom_image` — [AffinePositivity.lean:106](AffinePositivity.lean#L106).

### `RelativeMassFlow.lean`

- `total_flow_le_capacity` — [RelativeMassFlow.lean:21](RelativeMassFlow.lean#L21).
- `relative_mass_le_image_capacity` — [RelativeMassFlow.lean:32](RelativeMassFlow.lean#L32).
- `card_images_lower_bound` — [RelativeMassFlow.lean:40](RelativeMassFlow.lean#L40).
- `scaled_card_images_lower_bound` — [RelativeMassFlow.lean:51](RelativeMassFlow.lean#L51).
- `sum_card_disjoint_le` — [RelativeMassFlow.lean:65](RelativeMassFlow.lean#L65).
- `disjoint_block_flow_budget` — [RelativeMassFlow.lean:81](RelativeMassFlow.lean#L81).

### `ReturnBlocks.lean`

- `point_mem_section` — [ReturnBlocks.lean:31](ReturnBlocks.lean#L31).
- `middle_not_mem_section` — [ReturnBlocks.lean:37](ReturnBlocks.lean#L37).
- `block_steps` — [ReturnBlocks.lean:63](ReturnBlocks.lean#L63).
- `point_increment` — [ReturnBlocks.lean:76](ReturnBlocks.lean#L76).
- `point_lt_next` — [ReturnBlocks.lean:82](ReturnBlocks.lean#L82).
- `first_return` — [ReturnBlocks.lean:89](ReturnBlocks.lean#L89).
- `iterate_point` — [ReturnBlocks.lean:105](ReturnBlocks.lean#L105).
- `arbitrarily_many_increasing_first_returns` — [ReturnBlocks.lean:118](ReturnBlocks.lean#L118).

### `WordSurgery.lean`

- `constant_append` — [WordSurgery.lean:14](WordSurgery.lean#L14).
- `interior_constant_shift` — [WordSurgery.lean:26](WordSurgery.lean#L26).
- `balanced_shift_terminal_congruence` — [WordSurgery.lean:37](WordSurgery.lean#L37).
- `terminal_depth_budget` — [WordSurgery.lean:75](WordSurgery.lean#L75).

### `CycleRotation.lean`

- `denominator_rotate` — [CycleRotation.lean:20](CycleRotation.lean#L20).
- `constant_rotate` — [CycleRotation.lean:25](CycleRotation.lean#L25).
- `dvd_constant_iff_dvd_rotated` — [CycleRotation.lean:36](CycleRotation.lean#L36).
- `denominator_dvd_constant_iff` — [CycleRotation.lean:57](CycleRotation.lean#L57).
- `denominator_mul_source` — [CycleRotation.lean:66](CycleRotation.lean#L66).
- `cycle_divisor_passes_rotated` — [CycleRotation.lean:73](CycleRotation.lean#L73).

### `FiniteOrbitTransfer.lean`

- `iterate_injOn_prefix` — [FiniteOrbitTransfer.lean:27](FiniteOrbitTransfer.lean#L27).
- `window_card_le_prefix_add` — [FiniteOrbitTransfer.lean:41](FiniteOrbitTransfer.lean#L41).
- `window_bound_of_iterate_injective_estimate` — [FiniteOrbitTransfer.lean:68](FiniteOrbitTransfer.lean#L68).

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
- `Syracuse2adic : ℤ₂ → ℤ₂` — total map defined using the unit factor of
  `3x+1`, with value `0` at `−1/3`. It is discontinuous there.
- `Syracuse2adic_natCast` — bridge to the integer-level `S` for positive
  odd naturals.

### `SyracuseSingularity.lean`
- `singularLift_numerator`, `singularLift_step_of_seed` — the lift
  `n ↦ 4n+1` adds two numerator-valuation bits while preserving the
  accelerated output.
- `singular_outputs_separated_at_every_precision` — for every `R`, two
  positive odd natural inputs satisfy `2^R ∣ (3n+1)` while their
  accelerated outputs are `1` and `7`. This is a finite-precision
  arithmetic statement, not a formal topological continuity theorem.

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

## Later arithmetic and trace results

### `A0InfiniteSubfamily.lean`
- `hasStrictDescent_a0_t_two_mod_sixteen`,
  `hasStrictDescent_a0_t_ten_mod_thirtytwo` — unconditional strict descent
  for two infinite residue subfamilies of the A0 source cylinder.
- `a0Endpoint_word_one_not_drop` and companion short-word lemmas — local
  negative checks, not a global exclusion.

### `PrecisionTax.lean`
- `syracuseWord_precisionTax_scaled_identity_of_matches` — exact affine
  transport of the numerator attached to an expansive fixed word.
- `syracuseWordPhantomPrecision_after_eval_add_sum` — one matched block
  consumes exactly `w.sum` bits of the associated 2-adic precision.
- `syracuseWordPhantomPrecision_after_iterate_add_mul_sum`,
  `syracuseWord_matched_block_precision_budget` — exact telescoping and
  finite repetition budget.
- `no_infinite_matched_expansive_word` — one expansive word with positive
  sum cannot match forever from a natural starting state.

### `PrecisionTemplates.lean`
- `syracuseWordPhantomPrecision_one_after_eval_add_one` and the
  `…one_two…` / `…two_one…` companions — concrete numerators `n+1`,
  `n+5`, `n+7` and exact loss for `[1]`, `[1,2]`, `[2,1]`.
- `no_infinite_matched_syracuseWord_one` and companion lemmas — local
  no-infinite-repetition instances.

### `SwitchingPrecision.lean`
- `switchingPhantom_scaled_identity`,
  `switchingPhantomPrecision_after_step_add_exponent` — precision transport
  across compatible label changes and odd rescaling.
- `arbitrary_phantom_shift_can_set_precision` — unconstrained relabeling
  can reset the counter to any prescribed height.

### `AffineTraceGraph.lean`
- `switchingFormalPoint_transport` — compatible affine labels transport
  their rational formal point along the prescribed branch.
- `no_common_rational_fixed_point_of_distinct_words` — distinct formal
  fixed points cannot be cycles of one scalar rational control state.

### `ThreeTraceObstruction.lean`
- `concrete_shortTrace_lasso` — exact natural-number segment with a repeated
  triple of short-template precision values.
- `threeTraceLassoSeed_invariant`, `threeTraceLassoSeed_shortTraceTriple`
  — unbounded family of natural approximants to the formal point `−19/11`.
- `hiddenTrace_lasso_tax` — the omitted compatible precision decreases by
  four bits per lasso.

### `CycleConstraints.lean`
- `syracuseWordCycleEquationInt`, `syracuseWordCycleEquationNat` —
  necessary cycle equation for a matched periodic word.
- `syracuseWordCycleContracting` — every nonempty positive cycle word is
  contracting.
- `syracuseWordCycleModularSieve` — divisors of the denominator divide the
  word constant.
- `three_mul_le_at_first_contracting_prefix` — finite prefix bound at a
  hypothetical cycle minimum.

### `FirstBarrier.lean`
- `syracuseWordAffine_mod_exactResidueModulus_of_matches` — exact
  extra-bit residue condition for an odd endpoint.
- `evalSyracuseWord_lt_of_exactResidue_above_barrier` — sufficient finite
  residue test for a strict drop.
- `evalSyracuseWord_lt_iff_source_above_barrier` — at the actual source,
  the threshold is equivalent to descent, so it supplies no independent
  global ranking argument.

### `ExactCylinders.lean` — v6 exact-word theorem (full build passed)
- `syracuseWordMatches_iff_exactResidue` — for every nonempty list `w`
  of positive exponents and every natural start `n`, the exact word
  matches iff `(3^w.length * n + C_w) % 2^(w.sum + 1) = 2^w.sum`.
- `repeatPhantomWord_matches_iff_exactResidue` — for a `PhantomWord w`
  and `k > 0`, all `k` blocks match iff the analogous residue equality
  holds modulo `2^(k * w.A + 1)`.
- These equivalences are Lean declarations. Invertibility of `3^L`
  gives one odd residue class; its natural density is `2^-(A+1)`
  (relative odd density `2^-A`). Those class and density corollaries
  are paper-level at present.

---

## Post-v6 marked section and cancellation towers

These working-tree modules follow the frozen Zenodo v6 snapshot. They do
not supply a global Collatz termination rank.

### `ShortcutCoverage.lean`
- `ShortcutCoverage.rank_decrease` — explicit coefficient/valuation rank
  decreases outside the stopping set `{1} ∪ {n : n % 27 = 20}`.
- `ShortcutCoverage.exists_iterate_target_linear_bound` — every positive
  shortcut orbit hits that set in at most `13*n+4` steps. Sufficiency of
  the residue is classical; this is a local arithmetic certificate.

### `MarkedSection.lean`
- `MarkedSection.section_iff_episodeHits20` — exact six-progression
  characterization of a marked odd-to-odd episode; its source is excluded
  and its endpoint included. The theorem assumes `¬ 3 ∣ n`, with no cap
  on the actual 2-adic exponent.

### `SectionCoverage.lean`
- `SectionCoverage.shortcut_episode`, `shortcut_episode_endpoint` — exact
  correspondence between the shortcut and accelerated maps.
- `SectionCoverage.exists_accelerated_hit` — unconditional arrival at 1
  or the marked section on every positive odd Syracuse orbit.

### `CancellationTower.lean`
- `cancellationTower_run`, `cancellationTower_iterate` — arbitrary-length
  `[1,2]` repetition from `8^r*u-5` to `9^r*u-5` for even `u≥2`.
- `cancellationTower_exit_one`, `_two`, `_three`, `_ternary` — the three
  exact terminal phases and retained ternary identities.
- `cancellationTower_noDrop_of_even_ge_thirty` — the complete macro from
  `(2^(k+1)-11)/3` has no strict descent for every even `k≥30`.
- `cancellationTowerSource_mod_eighteen` — the infinite subfamily
  `k=18*t+10` belongs to the first marked residue class.

### `SectionReturn.lean`
- `SectionReturn.recurrent_section_of_never_hits_one` — every orbit
  avoiding 1 visits the marked section at arbitrarily late times.
- `SectionReturn.descending_return_family` — exact one-step returns
  `661+1152*t → 31+54*t` with exponent 6 and strict descent.
- `SectionReturn.first_return_can_increase` — first return `31 → 121`.
- `SectionReturn.marked_sources_noDrop_for_any_horizon` — explicit
  marked sources defeat every fixed finite accelerated descent horizon.
- `SectionReturn.classicalCollatz_of_rankDescent` — a fixed natural rank
  with eventual descending marked returns (or a hit of 1) implies Collatz.
  **`RankDescent` is an open hypothesis**, not an established property.
- `SectionReturn.exists_rankDescent_iff_acceleratedCollatz` — existence
  of such a rank is equivalent to accelerated Collatz, making the
  boundary of the reduction explicit in the formal statement.

### `WeightedVisits.lean`
- `WeightedVisits.potential_sub_succ` — exact one-step loss of
  `weight/iterate` along the positive Syracuse orbit.
- `WeightedVisits.sum_loss_range` — telescoping identity over every
  finite initial segment.
- `WeightedVisits.sum_loss_finset_le` — the loss over any finite set
  of distinct times is at most `1/x`.
- `WeightedVisits.sum_weight_visits_le` — the sum of affine weights
  of visits from x>0 to R>0 is at most `R*(3*R+1)/x`, even if R is
  periodic. This is a weighted occupation bound, not orbit descent.

### `WeightedWords.lean`
- `WeightedVisits.matches_eq_of_length_eq` — exact words of the same
  length from the same source coincide.
- `WeightedVisits.word_sum_eq_exponentSum`, `wordWeight_eq_weight_of_matches`
  — word exponents and weights agree with the actual orbit data.
- `WeightedVisits.sum_wordWeight_fiber_le` — total affine weight of a
  finite set of distinct exact words from x to R is at most R*(3*R+1)/x.

### `WeightedCounting.lean`
- `WeightedCounting.sum_grouped_by_source` — group a finite weighted sum
  by distinct sources, allowing multiple representations.
- `WeightedCounting.weighted_sum_le_image_sum` — a fiber bound K/x gives
  the bound K/X times the sum over distinct sources x≥X>0.
- `WeightedCounting.card_image_lower_bound`, `card_image_selected_lower_bound`
  — mass at least η forces at least η*X/K distinct sources.
- `WeightedCounting.mazur_main_term_lower_bound` — the stated error
  budget and main-term inequality imply mass at least 3/(8*3^m).
  Both inequalities are hypotheses, not external analytic imports.

### `WeightedPredecessors.lean`
- `WeightedPredecessors.word_fiber_bound`, `selected_weighted_source_bound`
  — apply the grouped bounds to exact words with common endpoint R.
- `WeightedPredecessors.classical_hits_of_accelerated_hits` — expand a
  finite odd-input Syracuse path to the ordinary map with arbitrary target.
- `WeightedPredecessors.ordinary_predecessor_count_of_mass` — a path
  mass lower bound counts distinct ordinary predecessors below N.
- `WeightedPredecessors.conditional_predecessor_count` — a finite count
  at least 3*N/(256*R*(3*R+1)*3^m), assuming the exact paths, their source
  interval, and an analytic mass/error estimate. No no-return assumption
  is used; no unconditional positive-density conclusion is claimed.

### `TwoSeed.lean`
- `TwoSeed.noReturn_or_noReturn_of_same_image` — distinct points with the
  same image cannot both have positive returns (generic deterministic map).
- `TwoSeed.lift_exponent_and_step` — the lift `L(n)=4*n+1` adds two to
  the Syracuse exponent and preserves the next state.
- `TwoSeed.exists_nonreturn_seed` — one of `n` and `4*n+1` is a positive
  odd non-returning seed when n is positive and odd.
- `TwoSeed.lift_iterate_formula` — exact identity
  `3*L^[k](n)+1=4^k*(3*n+1)`.
- `TwoSeed.exists_nonreturn_seed_above` — one of two explicit adjacent
  lifts lies above any supplied height and has no positive return. Its
  upper bound is explicit; the proof does not decide which candidate works.

### `NonreturnCounting.lean`
- `NonreturnCounting.visit_time_eq_of_noReturn`, `matches_eq_of_target_eq`
  — uniqueness of visiting time and exact word at a non-returning target.
- `NonreturnCounting.wordWeight_le_target_div` — the individual affine
  weight is at most R/x, independently of non-return.
- `NonreturnCounting.sum_wordWeight_fiber_le`, `word_fiber_bound`
  — the finite word fiber has weight at most R/x under non-return.
- `NonreturnCounting.conditional_predecessor_count` — finite count at
  least 3*N/(256*R*3^m), assuming non-return, exact paths, and the stated
  analytic mass/error estimate. The analytic hypotheses remain open here.

## Post-v6 tower parameter transport

The declarations below share the namespace `CollatzShadowing.TowerParameter`.
They concern finite words with a variable positive parameter, not one infinite
positive orbit. See the [transport report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_transport_2026-09-24/RESULTS_IT.md).

### `TowerParameter.lean`

- `numerator_valuation`, `quotient_factorization` — exact division and LTE
  for `Q_v(q)=(9^(2^v*q)-1)/2^(v+3)`, with v≥1.
- `quotient_difference_valuation`, `quotient_modEq_iff` — preservation and
  reflection of all finite dyadic congruences.
- `quotient_residue_bijective`, `affine_residue_bijective` — residue
  permutations at every finite precision.

### `TowerSuffix.lean`

- `suffix_iff_affine_residue`, `finite_suffix_residue` — every nonempty
  exponent word with first exponent at least two and remaining exponents
  positive corresponds to one odd parameter class modulo `2^(sum word)`.
- `phaseC_tower_burst` — exact orbit from the original phase-C cancellation
  source to the endpoint after its following burst; `phaseB_exit_burst`
  gives the corresponding phase-B transport from its known exit.
- `tower_finite_suffix_arbitrarily_large` — every such word occurs after
  the phase-C tower for arbitrarily large positive odd parameters.
- `tower_arbitrarily_long_one_suffix` — the specific words `[2] ++ [1]^l`
  occur for every finite l. This does not assert no descent below the source.
- `finite_suffix_bounded_iff` — realization below a parameter bound is
  equivalent to the least positive residue fitting below that bound.

## Post-v6 prefix optimality and sibling basins (26 September 2026)

### `PrefixOptimality.lean`

- `iterate_lift` — exact shortcut arithmetic under an input lift by `2^k*t`,
  preserving the first k parity count and shifting the endpoint by `3^J*t`.
- `all_one_suffix_attained` — a positive actual input in the exposed class
  realizes the maximal upper suffix under the exact quadratic map.
- `prefixMaximum_exact`, `certificate_iff_zeros` — the attainable maximum is
  `K−2*J_Q(H)−Z_(f(Q))(M)`; the observed-zero threshold is necessary and sufficient.
- `counterexample_before_threshold` — an actual positive source violates
  every proposed bound below that maximum. No condition on additional
  tower ancestry or preserved high bits is imposed by this theorem.
- `exists_certifying_precision_iff` — existence of a certifying precision
  is equivalent to the bound at the actual source, not a new bound on it.

### `SiblingBasins.lean`

- `basins_pairwise_disjoint` — for an injective forward orbit of an arbitrary
  map, distinct side branches with the same next orbit states have disjoint
  predecessor basins.
- `sum_weight_predecessors_le`, `sum_card_predecessors_le` — a finite source
  set supplies at most its total natural weight/cardinality across these basins.
- `canonicalSibling_spec` — the selected Syracuse sibling shares the next
  state, is larger but at most `16*n+5`, odd and not divisible by three.
- `canonical_sum_weight_predecessors_le` — specialization of the finite
  weighted budget to the selected siblings. Neither a density comparison nor
  its proposed no-divergence consequence is formalized by this statement.

### `LastExponentTransport.lean`

- `matches_and_endpoint_of_affine` — an odd exact affine endpoint certifies
  the actual valuation word and its endpoint.
- `last_constant_unchanged`, `last_exponent_transport` — changing only the
  final exponent preserves the affine constant and constructs a new source
  from an explicitly supplied nonnegative congruence correction.
- `correction_positive`, `transport_height_cost`, `last_exponent_height_cost`
  — increasing the target forces the cross-multiplied strict bound
  `n*u' > (n+3^k)*u`.
- `not_bounded_height` — the arithmetic cost excludes any proposed source
  dilation factor once the stated depth inequality holds. The asymptotic
  density-zero consequence and the separate equal-depth obstruction are
  paper-level arguments, not claims of this module.

## `Generated/` — machine-generated finite certificates

Verified by Lean; emitted by `../../scripts/phantom_taxonomy/` generators.

- `K16S16KDeterministicCW` — `k16s16KDeterministicGeneratedSpectralRadiusBound` (deterministic `(K,b)` bound `ρ ≤ 3/4`, `K₀=16`).
- `K16S16KLB5DeterministicCW`, `K16S16KLB6DeterministicCW` — finite
  variants with the same explicit `ρ ≤ 3/4` certificate form.
- `T10J32HighBitTailCW` — `t10j32HighBitTailSpectralRadiusBound_97_2000` (single-node `ρ ≤ 97/2000`); plus `…CWData`, `…CWRows00–13`.
- `K16S16KExactCWSummary`, `K16S16KSCC`, `K16S16KBridge` — 37-state empirical `(K,b)` CW + SCC + bridge.
- `T10CriticalSymbolic`, `T10J32HighBitTail` — exact `T=10` transfer-matrix imports.
- `A0ReturnBranches` — generated A0 return-branch data.

These contribute the bulk of the line/declaration count but are **generated**,
not hand-authored. See [`../../notes/PROJECT_STATISTICS.md`](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/PROJECT_STATISTICS.md)
for the hand-written vs generated split.

### `SignedTransport.lean`

Paper reference: `notes/post_v6_signed_mass_2026-09-26/PROOF_IT.md`, §§2–4.
- `SignedTransport.affine_comparison`: cross-multiplied expansion for a common affine offset.
- `SignedTransport.odd_ne_two_pow_mul`: distinct odd targets cannot coincide under a nonnegative binary lift.
- `SignedTransport.congruent_shift_requires_large`: a congruent binary lift must reach the ternary modulus in at least one representative.
- `SignedTransport.positive_shift_expands`: expansion bound for actual words differing at their final exponent.
- `SignedTransport.negative_shift_compresses`: corresponding compression bound.
- `SignedTransport.lift_comparison`: preservation under a common dyadic factor.
The distinct-image o(X) theorem and arbitrary output-lift counting remain paper arguments.
