# Current mathematical status

**Version 7 published, 16 November 2026:** the English
[manuscript](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/paper/collatz_spectral_reduction_v7.pdf) and
[release evidence](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/v7_release_2026-11-16) bind the present
canonical package of 90 Lean files, including 26 generated modules.
A fresh pinned incremental build completed 3404 jobs; strict audits
passed for the selected groups of 69 roots, 136 declarations and 68
declarations. The paper distinguishes checked finite estimates from
conditional external inputs and paper-only paired-path arguments.
Lean 4.29.1 predates later published kernel soundness fixes; no
independent current-checker replay is claimed. The PDF and reproducible
source archive are published at
[doi:10.5281/zenodo.24284425](https://doi.org/10.5281/zenodo.24284425), and
both public downloads match the local release bytes. The existing v1–v6
publications and their checksums remain unchanged.

Updated 2026-11-16. The published v1–v7 Zenodo PDFs are frozen snapshots.
Published [v6](https://doi.org/10.5281/zenodo.22936057) includes the erratum
to v4; subsequent working-tree developments are separate from its frozen
supplementary archive. This working tree targets pinned Lean v4.29.1 and Mathlib
v4.29.1; portability to later toolchains has not been checked.

**Second conceptual hour, 16 November:** a
[paired-word construction](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_ideas_2026-11-16_second_hour/REPORT_IT.md)
intertwines `12 → 21` and `212 → 113` by the translation `x ↦ x−2`.
Mixed concatenations retain an actual nearby companion; an attributed
terminal gate gives a different last parent, with explicit unit repairs.
A minimum divergent unit seed cannot stay in this infinite block language:
its first gap must be one, and the companion would give a smaller divergent
unit seed. No coverage of all exits is proved. An explicit exit family
shows that bounded observed gaps alone do not bound the pair carry;
subsequent forced contractions must be accounted for. This is a paper
deduction using classical paired-word mechanisms, not a new Lean proof or
a universal novelty claim.

The same hour obtains the finite prefix-free witness upper
`ΣΓ ≤ bP₀(8/α+1)`, allowing a possible entry into a cycle. It uses the
external atom floor only on nonperiodic seeds. New literature was read
through papers149–154; linear chosen resets and linear modular routing
were already available. None supplies the missing source-specific exit
coverage or a nonsummable lateral allocation. No computation, build,
GPU work or formal declaration was added in either conceptual hour.

**Conceptual audit, 16 November:** no new computation or formal declaration
was added. Ancestor decay already supplied by Valbuena and
[paper12](https://rstation.ai/problems/collatz/papers/12) gives nonatomicity
of the canonical inverse law and `K₂^m(g²)(n)→0` at every fixed unit root,
including periodic roots. The earlier warning that the unweighted Green
budget alone does not prove this remains valid; the additional literature
input closes that qualitative interface. A uniform critical clock for
moving roots remains open.

The [minimal research contract](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_ideas_2026-11-16_one_hour/ROOT_MINIMAL_PROGRAM_IT.md)
uses a direct positive telescope and actual off-spine word certificates;
it can omit natural-density and clock-CLT inputs, Q, F and trace caps from
that implication. Harmonicity, the unit floor and the nonperiodic linear
upper give one sufficient set of external analytic inputs. The
[final dependency reduction](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_ideas_2026-11-16_one_hour/ROOT_ATOM_FLOOR_CORE_IT.md)
obtains the global budget from the atom floor and a lower logarithmic
density already in paper12, without natural-density existence or the
canonical trace theorem. An optional Abel extraction supplies a positive
superharmonic function instead of identifying a canonical harmonic trace.
Variable clock and finite prefix-free witness families are allowed; no
required editor has been constructed. The [critical value audit](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_ideas_2026-11-16_one_hour/agents/H02_VALUE_AUDIT_IT.md)
and [sparse-support obstruction](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_ideas_2026-11-16_one_hour/agents/H01_SPARSE_SUPPORT_IT.md)
distinguish this simplification from an advance on the missing lower bound.

**Research follow-up, 16 November:** four modules add 28 public theorem
declarations. The full incremental build passes (3404 jobs); a strict
transitive audit of all 68 compiled declarations, including five
encoded-private helpers, permits only `propext`, `Classical.choice` and
`Quot.sound`. The [receipt](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15_three_hours/verification/integration_receipt.json)
binds the same frozen source snapshot throughout both phases.
Six further finite replay suites pass with identical normal and optimized
output. A separate Ubuntu CI run also passes; all twelve output files and
the strict audit log are byte-identical to the local evidence, as recorded
in the [CI receipt](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15_three_hours/verification/checkpoint_ci_receipt.json).

- `FiniteHorizonBudget` proves shifted-height growth, source localization
  and a reciprocal-square tail budget `2/R`, with fixed-depth and
  nonreturning finite-horizon applications.
- `QuadraticOccupation` proves squared-potential dissipation and a shared
  finite catalogue bound `2*n^2*(3*n+1)^2/(6*n+1)`, allowing repeated sources
  and cyclic targets. Green finiteness was already known in the external
  literature; this is a local formalization with explicit constant.
- `BoundedSlopeCatalogue` proves finiteness of the complete bounded-slope
  word set, an explicit cardinality/source bound, and only existential
  bounds on word length and total exponent. A cardinality bound is not a
  computable bound on hitting time.
- `SpineDispersion` proves finite collision upper budgets and lower
  certificates from distinct branch allocations. A truncated catalogue's
  defect is an **upper** bound on the full defect. Branch lower allocations
  transfer to an infinite kernel only because the inequality holds for
  every finite extension, followed by a justified limit. Normalized sample
  frequencies are not certified probabilities of that kernel.

The [bounded-slope suffix obstruction](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15_three_hours/agents/U11_BOUNDED_SLOPE_IT.md),
the [periodic-dictionary obstruction](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15_three_hours/agents/U05_PERIODIC_DICTIONARY_IT.md),
the [finite-crossing cap/Doob identity](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15_three_hours/agents/U15_FINITE_CAP_IT.md),
the [exact cutoff and ladder renewal](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15_three_hours/agents/U15_LADDER_RENEWAL_IT.md)
and the [collision/branch-surplus criteria](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15_three_hours/agents/U12_TWO_SEEDS_IT.md)
are paper deductions with separately stated analytic inputs. Their required
lower bound remains unproved. The exact cutoff is the maximal gain F;
its attainment is a consequence of the finite catalogue, not a new global
Green-finiteness claim. The cited linear upper bound for the trace applies
to nonperiodic targets; the external periodic bound has an additional
return factor. Cap identities themselves do not require that linear upper
bound. No external density project, asymptotic
mass estimate or general cycle exclusion is imported into Lean.

A [standalone maximal-gain prototype](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/research/research_sprint_2026-11-15_three_hours/u06_max_envelope/COMPOSITION_RESULTS_IT.md)
separately checks nine named results: maximum attainment, source bounds,
composition and calibration of optimal prefixes. Its 22 declarations pass
a strict audit with the same three standard axioms and an independent
semantic review. It is outside the main-library module and source counts;
the extension contains an exact frozen copy of its six-theorem core.
The cap, renewal and asymptotic statements above remain paper proofs.
The [final novelty review](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15_three_hours/agents/U14_MINIMUM_ASYMPTOTIC_NOVELTY_IT.md)
identifies an existing uniform high-state packing/product estimate behind
the constant-one minimum-ancestor comparison. That comparison is treated
as an attributed corollary. The literature also supplies a stronger power
tail with an unevaluated constant; it is an external alternative to the
explicit local tail, with no additional Lean import.

**Research integration, 15 November:** seven new modules add 56 public theorem
declarations. The integrated library build passes (3400 jobs). A transitive
audit covers all 136 declarations in these modules, including 14 encoded-private
helpers, using only `propext`, `Classical.choice`, and `Quot.sound`.
The [integration receipt](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15/verification/integration_receipt.json)
binds the checked sources and logs; ten finite replay suites also pass with
identical normal and optimized output.

- `OrbitReciprocal` proves the universal finite-injective-shortcut reciprocal
  budget `133547/1655 < 81` by exact parity moments and finite geometric sums.
  No external sparse-window or entropy theorem is assumed.
- `FirstArrivalBudget` and `WordProductEnvelope` connect actual odd Syracuse
  first arrivals to shortcut first arrivals and prove height `21*exp(27)*u`
  for every existing same-profile image at the canonical sibling. Different
  profiles are also allowed under an explicit bounded homogeneous-slope ratio.
  Existence and a positive mass of images are not conclusions.
- `IntegerAtomTilt` bounds tilted integer-atom mass by `2*n^2`, including
  one shared budget across all depths at a nonreturning target. Its cutoff
  and Cesaro applications are paper deductions, with no new analytic axiom.
- `TwoEditSparsity` proves the full residual identities/divisibility and an
  elementary exponent budget. The subpolynomial sparsity argument using
  Evertse and its terminal-block extension remain paper proofs.
- `TraceDensityBridge` is conditional algebra; no external density or trace
  theorem has been imported. `CycleMinimumProduct` proves classical integer
  minimum-product and logarithmic-gap constraints without a Rhin input or a
  computational verification premise.

See the [two-hour research report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15/REPORT_IT.md),
the [height derivation](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15/ROOT_HEIGHT_IT.md),
and [research protocol](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-15/PROTOCOL_IT.md).
H, its outgoing-mass obligation, and the general cycle problem remain open.

**Research sprint, 13 November:** ten new modules add 69 public theorem
declarations, with no new proof placeholders, native decisions or declared
axioms. The integrated main build passes (3393 jobs, exit 0), with only
nonblocking linter notices. A strict audit of all 69 new public roots
passes using only `propext`, `Classical.choice`, and `Quot.sound`.
The [verification dossier](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/research_sprint_2026-11-13/REPORT_IT.md)
records the dependency-audit result and source hashes.

- `RootPoolBudget` and `SiblingPool` formalize shared dissipative charges
  and the stronger reciprocal charge for an entire nonrecurrent pool,
  including canonical siblings. The pool mechanism is attributed to
  Shaik's pinned sources and proved independently in this toolchain.
- `CapacityAllocation` supplies a finite threshold certificate; its lower
  mass is an explicit input. `RelativeMassFlow` records relative-mass,
  image-load and finite disjoint-block obligations without proving H.
- `JointAtomDictionary` and `AffinePositivity` connect exact positive odd
  predecessors to full ternary congruences, prove automatic positivity,
  and count same-length catalogues without source duplication.
- `ReturnBlocks` proves arbitrarily many increasing first returns;
  `WordSurgery` and `CycleRotation` supply exact arithmetic constraints.
- `FiniteOrbitTransfer` proves that deleting at most N terminal points
  lets an N-step injectivity estimate apply to an injective finite orbit.
  The numerical sparse-window estimate is still an explicit hypothesis
  in that module. At that date the universal reciprocal/product and height
  bounds were paper deductions; the 15 November modules above now prove a
  stronger explicit bound and its first-arrival application in Lean.

The same sprint corrects the historical Cauchy and Haar-sampling sketches.
A clock-only convergence estimate is proved on paper for one explicit
macro branch; it does not close Gate 10.B. The finite profile-matching
experiment and the relative mass fraction eta are distinguished from
asymptotic conclusions. No new analytic density dependency was imported,
no new tower level was computed, and no v7 was published.

**Signed-transport follow-up, 26 September (H.2):** the full multivalued
relation changing only the final exponent has o(X) distinct output images
within DX from odd sources within X, even with arbitrary output dyadic
lifts. Targets are distinct positive odd integers, D is fixed, and source
words use first arrival (automatic for non-returning targets). This is a
paper theorem, with six supporting arithmetic lemmas in `SignedTransport`.
The integrated build passes (3380 jobs, exit 0). A nonblocking linter
warning notes an unused oddness hypothesis; there are no compilation errors.
All six roots pass the strict dependency audit using only the standard
axioms; exact Python output matches with and without optimization.
It closes this particular mass-transfer method, not H. See the
[signed-mass report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_signed_mass_2026-09-26/RESULTS_IT.md).

**Basin-transport follow-up, 26 September:** an exact last-exponent
transport and its strict height cost are now formalized. A separate paper
argument shows that its nonnegative-shift version retains density zero
inside every fixed dilation of the source cutoff. Another paper theorem
obstructs pointwise transport at equal depth. Neither result refutes H:
mass comparisons may change depth or discard controlled source sets.
See the [transport report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_basin_transport_2026-09-26/RESULTS_IT.md).
The integrated build passed (3379 jobs, exit 0); all seven new declarations
passed the strict standard-axiom audit. Both exact Python replays match
their saved JSON byte for byte, including under Python optimization.

**Research decision, 26 September:** the finite-filter campaign on the exact
tower is closed. The [new review package](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_reset_2026-09-26/RESULTS_IT.md)
separates the formal prefix-optimality result, a finite sibling-basin budget,
and an unproved relative density comparison proposed for further review.
That comparison is not supplied by the existing predecessor-density theorem;
if established together with positive basin density, it would exclude
nonperiodic orbits, not nontrivial cycles. No Collatz proof is claimed.

**Verification, 26 September:** the integrated main-library build passed
(3378 jobs, exit 0). Strict dependency audits passed for 10 prefix and 14
sibling-basin declarations, using only `propext`, `Classical.choice` and
`Quot.sound`. Seven Python tests pass with and without optimization; the
four-cutoff census was reproduced exactly for integer fields. These checks
reuse pinned Mathlib artifacts and are not an independent-kernel replay or
a rebuild of the separate external analytic package. Logs and hashes are
in the review package.

## Proved in Lean

- Increasing the final exponent of an exact Syracuse word gives an actual
  transported source when its explicit congruence quotient exists; for an
  increased target, `n*u' > (n+3^k)*u` (`LastExponentTransport`). No
  density estimate or discrete-logarithm existence theorem is imported into
  this statement.
- An exact attainable maximum for the shortcut parity defect over a dyadic
  source class, with positive integer witnesses and a necessary-and-sufficient
  observed-zero criterion (`PrefixOptimality`). This does not estimate the
  actual exact-tower word or preserve additional ancestry constraints.
- Pairwise disjoint predecessor basins for selected siblings of an injective
  orbit, a finite budget for natural source weights, and an explicit Syracuse
  sibling at height at most `16*n+5` (`SiblingBasins`). The finite source sets
  use noncomputable membership with unbounded visiting time; no general
  basin-decision algorithm or asymptotic density comparison is proved.
- Exact congruential shadowing and exclusion of positive integer orbits
  that remain forever on one expanding periodic phantom word.
- Finite Collatz–Wielandt bounds for explicitly generated matrices,
  including `ρ ≤ 3/4` for the deterministic `(K,b)` certificate. These are
  finite matrix statements and do not establish an infinite-operator gap.
- Exact loss of `w.sum` bits of 2-adic precision each time one fixed
  expansive word `w` matches a positive integer orbit; hence a finite
  budget for consecutive repetitions of that word.
- The full library build on 24 September 2026 checks
  `syracuseWordMatches_iff_exactResidue`: a nonempty positive-exponent
  word matches iff its affine numerator equals `2^A` modulo
  `2^(A+1)`. `repeatPhantomWord_matches_iff_exactResidue` gives modulus
  `2^(kA+1)` for `k > 0` repetitions. The unique odd residue class and
  natural density are paper-level deductions, not formalized here.
- Necessary equation, contractivity, and prefix constraints for a
  hypothetical positive cycle. These do not exclude every nontrivial cycle.
- Two explicit infinite residue subfamilies of the A0 source cylinder
  have strict descent. A finite-word threshold test and a trace-switching
  identity are also proved, together with counterexamples to several
  proposed global rankings.
- For every `R`, two positive odd inputs have `2^R ∣ (3n+1)` but distinct
  accelerated outputs `1` and `7`
  (`singular_outputs_separated_at_every_precision`). This is the exact
  finite-precision arithmetic witness near `−1/3`; topology itself is
  not formalized in that theorem.
- A uniform strict-descent hypothesis implies accelerated and classical
  Collatz by strong induction. The hypothesis is not proved here.
- Post-v6 shortcut coverage: an explicit residue/valuation rank proves
  that every positive shortcut orbit reaches 1 or `20 mod 27` within
  `13*n+4` steps. The sufficient residue is classical; the rank is a
  concrete certificate integrated here.
- An exact six-progression characterization of marked Syracuse episodes,
  unconditional arrival at 1 or this section, and arbitrarily late section
  visits on any orbit that never reaches 1.
- Universal cancellation-tower formulas, all three terminal phases, and
  absence of descent through the complete macro for every even `k≥30`.
  The subfamily `k=18*t+10` belongs to the first section port. In particular,
  marked sources defeat every fixed finite accelerated descent horizon.
- Exact descending marked returns `661+1152*t → 31+54*t` for every t,
  and an increasing first marked return `31 → 121`.
- A telescoping identity for affine orbit weights and the bound
  `sum_{k in H} 3^k/2^(A_k) ≤ R*(3*R+1)/x` for every finite set H of
  visits from x>0 to R>0 (`WeightedVisits.sum_weight_visits_le`).
  No assumption about periodicity or convergence is used. The formal
  theorem is indexed by distinct times. `WeightedWords` now proves the
  corresponding bound for distinct exact exponent words.
- Finite weighted counting without source injectivity: grouping words
  with the same source gives `sum selectedWeight ≤ K/X * card sources`
  for sources at least X>0 and K=R*(3*R+1). Exact odd-source paths also
  give ordinary Collatz predecessors. The final finite theorem yields
  `card predecessors below N ≥ 3*N/(256*K*3^m)` from an explicitly
  assumed analytic mass estimate and error budget; it does not prove
  those assumptions or a positive-density theorem.

- A bounded pair of Syracuse seeds: `L(n)=4*n+1` preserves the next state,
  and one of n and L(n) has no positive return. Above each height X, one of
  `L^[X+1](n)` and `L^[X+2](n)` works, with an explicit common upper bound.
  This uses the standard injectivity of a map on its periodic points;
  it does not decide which candidate works or exclude cycles of the successor.
- At a target R with no positive return, visiting time and exact word are
  unique for each source. The word fiber bound sharpens to R/x, giving a
  conditional predecessor count at least 3*N/(256*R*3^m). The analytic
  mass inequality and error budget remain explicit assumptions.

## Still open in this development

The main missing statement is `UniformStrictDescentHypothesis`: every
positive odd integer other than `1` must have an accelerated iterate below
itself. The named `A0FirstBarrierExistsAll` and
`A0FirstBarrierThresholdAutomatic` hypotheses are also open; both are
needed for the current A0 exit theorem, which covers only that family.
A global descent cover has not been constructed.

The post-v6 section has **unconditional coverage**, but no global return
rank. `SectionReturn.RankDescent R` requires a hit of 1 or an actual later
marked state with smaller R. Its existence is formally equivalent to
accelerated Collatz (`exists_rankDescent_iff_acceleratedCollatz`). This is
an exact interface for the open obligation, not a weakening of it.

The weighted counting direction has a formal local bridge from exact words
to distinct ordinary predecessors. A separate hash-pinned Lean 4.30.0-rc2
[overlay](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/research/weighted_predecessors_adapter/README.md) now contains
both the external path adapter and a two-seed route to uniform constants.
The external modular replay and both final theorem dependency audits passed
in [CI 36005012141](https://github.com/PieroBorgatta/Collatz/actions/runs/36005012141):
395 local modules, with 394 matching compiled receipts reused and one module
compiled in the final run. Both roots use only the three standard axioms. The
two-seed audit traversed 43,248 reachable declarations and excluded the old
unbounded seed choosers; the weighted audit excluded its forbidden route in
the local module closure. Targeted semantic audits of the seed and mixing
wrappers do not replace independent review of the full analytical argument.
The earlier interrupted local and aggregate attempts remain historical
failures to complete those separate checks, not additional successful replays.

The subsequent optimization is also verified in
[CI 36009718722](https://github.com/PieroBorgatta/Collatz/actions/runs/36009718722):
399 local modules and three dependency audits. Four new external modules add
40 public theorems and two private lemmas. Compact congruent seeds reduce the
uniform root bound, and preserving sixth-power mixing allows the least positive
m with `88*T*C ≤ m^6`. Direct Lean comparisons prove a strictly larger density
coefficient and a strictly smaller cutoff than the preceding uniform two-seed
formulas. The main-library counts below do not include these external modules.
See the [optimization report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_optimization_2026-09-24/RESULTS_IT.md).

The integrated main-library build with `TwoSeed` and `NonreturnCounting`
passed (3371 jobs), as did CI run 36001432687. Sixteen headline declarations
were audited and use only `propext`, `Classical.choice`, and `Quot.sound`.
The new proof and comparison report is
[here](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_adapter_2026-09-24/RESULTS_IT.md). It distinguishes
these results from the paper-level comparison of coefficients and from the
external analytical chain. For aligned explicit candidates, the comparison
proves T<R² and a coefficient improvement by more than a factor of three;
this comparison has not been formalized in Lean and does not compare cutoffs.

The earlier conditional counting boundary is recorded in
[the counting report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_counting_2026-09-24/RESULTS_IT.md).
Post-tower parameter formulas and resonance distributions are paper-level
deductions with exact finite checks, not Lean theorems; see
[the further research note](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_parameter_2026-09-24/IDEAS_IT.md).

The integrated build including all three new counting modules passed
(3369 jobs). Fourteen headline declarations were audited and use only
`propext`, `Classical.choice`, and `Quot.sound`; none of those modules
uses `native_decide`. Build output and source hashes are recorded in the
counting report's verification manifest.

The general v6 defect/cancellation ledger remains a paper-level proposal.
Its concrete cancellation-tower family is now treated in
`CancellationTower.lean`; arbitrary switches remain uncontrolled. Equal-valuation
cancellation can raise destination precision even when the affine defect
has no 2-adic root; a proposed finite-cylinder checker must treat those
critical cases explicitly.

The post-v6 development, finite synthesis prototype, and verification
record are in [the continuation report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_section_2026-09-24/RESULTS_IT.md).
The integrated library build passed (3365 jobs); thirteen new headline
theorems were audited and depend only on `propext`, `Classical.choice`,
and `Quot.sound`. None of the five new modules uses `native_decide`.

The total `Syracuse2adic` function agrees with the natural-number map on
positive odd inputs but is discontinuous at `−1/3`. Published v6
uses infinite positive-exponent coding only on orbits avoiding that
singular point. Its coding observation says that excluding **all**
non-eventually-periodic words from positive integers is equivalent to the
no-unbounded-orbit problem; it does not prohibit more specific pointwise
arguments.

See [the declaration index](CollatzShadowing/THEOREM_INDEX.md) for exact
Lean statements and [project statistics](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/PROJECT_STATISTICS.md)
for historical and current file counts.

The `CollatzShadowing` Lean sources have no `sorry`, `admit`, or
project-declared `axiom`. A `#print axioms` audit of selected structural
headline theorems found only standard Lean axioms. Several finite proofs
use `native_decide`; their generated axiom dependencies place the native
compiler in the trusted base, so the source scan is not a kernel-only
guarantee.

The pinned Lean 4.29.1 predates a documented
[kernel soundness fix in 4.32.2](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/)
and further [soundness fixes and defensive checks in
4.34.0](https://lean-lang.org/doc/reference/latest/releases/v4.34.0/).
Nothing here shows that this project uses those defects. For a new
publication-grade verification, recheck the development with Lean 4.34.0
and a matching Mathlib revision, then repeat the axioms audit. That
portability recheck has not yet been done.


## Post-v6 tower parameter transport (24 September 2026)

`TowerParameter.lean` proves the exact dyadic isometry of
`Q_v(q)=(9^(2^v*q)-1)/2^(v+3)`, including residue bijectivity at every
finite precision. `TowerSuffix.lean` transports exact finite words through
this map, connects phase C to the original cancellation source, and proves
that every admissible finite suffix occurs for arbitrarily large odd
parameters. It also supplies a least-residue criterion for bounded parameters.
The two modules add 19 public theorems and three private lemmas and are
imported by the main entrypoint. The aggregate build passed (3,374 jobs) in
[CI 36015103652](https://github.com/PieroBorgatta/Collatz/actions/runs/36015103652),
commit `e713dfdf64403a15e451ec11d3cf642ef2b11615`, on Lean 4.29.1. The strict
eleven-root audit traversed 13,782 declarations and 229,886 type/body edges,
including private helpers, and found only `propext`, `Classical.choice`,
`Quot.sound`. Pinned supporting compiled dependencies were reused; this
was not a cold rebuild of Mathlib or a replay with an independent kernel.

The obstruction is precise: no admissible finite suffix can be forbidden
uniformly over all odd parameters at fixed v. This does not rule out
height-dependent constraints or prove failure of a global rank. No new
return-descent theorem or infinite divergent orbit is claimed. See the
[transport report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_transport_2026-09-24/RESULTS_IT.md).

## Post-v6 descent and conditional transfer (25 September 2026)

`DescentCertificate.lean` formalizes a sufficient finite certificate:
for positive x,N and k<3N, the inequality
`3^(k+1)*x < 2^(exponentSum x k)*(3*N-k)` implies a visit below N
at some time j≤k. A budget version permits an upper horizon and a lower
bound on the actual exponent sum. The proof uses the exact dissipation
identity in `WeightedVisits`, including the effect of the affine correction.

`QuadraticTransfer.lean` supplies a rational version and a conditional
transfer from X to `X+c*X²`. For X≥N>0, c≥1, a positive lower weight w
with wX<N, an upper horizon ell≤N, and upper weight u satisfying
`c*u ≤ 96*w²`, it gives a visit below `96*N²+704*N+1287` by ell.
A corollary obtains the lower weight premise from an actual lower endpoint
below N. The upper relative-weight inequality remains an explicit hypothesis.

The two modules are imported by the main entrypoint. A dedicated
[nine-root dependency audit](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_induction_2026-09-25/DependencyAudit.lean)
allows only `propext`, `Classical.choice`, and `Quot.sound`; no native axiom
is allowed for these roots. The final verification evidence is recorded in
the [transfer report](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_induction_2026-09-25/RESULTS_IT.md).
The full build and this strict audit passed in
[CI 36118390826](https://github.com/PieroBorgatta/Collatz/actions/runs/36118390826)
on code commit `8be311667d6d20a729a39ba6dd711e122da74649`, with the three
standard axioms only for every new audited root.
This is not a complete formalization of the earlier shortcut parity-count
certificate producer, its Q_v specialization, or the application of Chim's
theorem. No uniform family descent or mathematical priority is claimed.

## Post-v6 binary carry experiment (26 September 2026)

The latest research remains outside the Lean declarations. The
[seven-ancestor filter](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_seven_ancestors_2026-09-26/RESULTS_IT.md)
is false at level 11, and the
[prefix-renewal analysis](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_renewal_2026-09-26/RESULTS_IT.md)
requires nearly the full upper precision in the observed large cases.

The [new carry experiment](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_binary_carries_2026-09-26/RESULTS_IT.md)
reconstructs exact tower prefixes by column-wise squaring from seed 3,
with five historical pairs checked against modular powers and direct
shortcut orbits. Squaring carries within an exposed prefix are redundant
with that prefix. All nine archived adversaries retain those exposed
carries. Current carry and fixed input/output windows do not close a
deterministic generator on general anchored odd roots; the paper proof
provides a collision for every finite window. This is not a memory
impossibility theorem for the exact tower alone.

A future boundary carry selects some completions in exhaustive diagnostic
levels 0 through 4 and rejects the nine archived witnesses. No uniform
estimate on parity weight or signed cumulative defects has been obtained.
The exact seed constraint selects the source, but a quantitative bound on
its orbit remains open. The new Python verification is local; a workflow
is prepared for replay. No new Lean declaration, aggregate build, CI run
or certified tower level is claimed for this phase.

## Post-v6 future carry constraint (26 September 2026)

The [continuation](https://github.com/PieroBorgatta/Collatz/blob/3964420b32db9318e7271343f7bed39e26a3a8b8/notes/post_v6_carry_constraint_2026-09-26/RESULTS_IT.md)
expresses the future squaring carry as an exact linear slab on the free
source bits when `K≤2H`. A fixed level-16 search then falsifies the proposed
extension of `Delta≤512` to sources with the complete actual lower word,
all actual high source bits and the actual future carry. The 281st of 988
fixed candidates has the required carry 31655 but `Delta=31168`, with
margins `1155→-28858`. The actual tower retains `Delta=-479` and upper
margin 2789. Neither Collatz nor a bound restricted to the exact tower
is refuted. The new arithmetic proofs are on paper, independently checked
on small domains and with complete finite witness replay. No new Lean
declaration, tower level, CI run or aggregate build is claimed.
