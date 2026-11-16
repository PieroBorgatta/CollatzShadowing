# CollatzShadowing

A standalone Lean 4 + Mathlib library for finite arithmetic in the
*Phantom Orbit Shadowing* research program. This v7 standalone snapshot
synchronizes the verified library from the canonical
[Collatz repository](https://github.com/PieroBorgatta/Collatz).

**This library does not prove the Collatz conjecture.** Pointwise descent,
the required relative branching lower bound, and general nontrivial-cycle
exclusion remain open. Conditional theorems retain their hypotheses.

## Snapshot and scope

- Lean **4.29.1** and Mathlib **4.29.1**, pinned without a toolchain change.
- **90 library Lean files**, including the entrypoint and 26 generated
  finite-certificate modules. The exact exported files and SHA-256 hashes
  are in [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json).
- Exact shadowing, cylinder and precision results; finite operator
  certificates; first-arrival, reciprocal and occupation budgets; finite
  bounded-slope catalogues and conditional transport interfaces.
- The accelerated 2-adic map's singularity at `-1/3` is treated explicitly.
  No global continuity claim from the historical v4 paper is retained.
- Paper-only paired-path constructions, external analytic projects and
  standalone maximal-gain prototypes are **not** part of this library's
  formally checked declaration count.

See [PROVENANCE.md](PROVENANCE.md) for synchronization, licensing and
verification scope, [STATUS.md](STATUS.md) for the full mathematical status,
and the [declaration index](CollatzShadowing/THEOREM_INDEX.md) for exact
theorem names. External links in the exported status document are pinned
to the canonical source commit.

## Build and audit

```sh
lake exe cache get
lake build
python3 tools/export_from_collatz.py --check
lake env lean verification/November13DependencyAudit.lean
lake env lean verification/November15DependencyAudit.lean
lake env lean verification/FiniteCatalogueDependencyAudit.lean
```

The source files contain no proof placeholders or project-declared
`axiom` commands. Some legacy finite certificates use `native_decide`;
those proofs include the native backend in their trusted base. The CI
allowlist names exactly the nine existing native axioms. The three
separate November audits require only `propext`, `Classical.choice` and
`Quot.sound` for their specified roots and transitive dependencies,
including encoded-private declarations in the two later audits.

API documentation generation and deployment are an optional manual CI
action (`build_docs: true` on `main`). Ordinary release pushes run the
formal checks without waiting for the separate, potentially lengthy
documentation build.

These checks do not verify the external atom-floor or density papers, nor
turn the source scan into an independent-kernel proof audit. The pinned
Lean version has not been migrated to a later toolchain. A publication
must retain that verification limitation.

## Representative results

| Result | Module |
|---|---|
| Exact congruential shadowing and expansive-cycle exclusion | `Shadowing`, `NoInfinite` |
| Exact finite valuation cylinders and singular outputs | `ExactCylinders`, `SyracuseSingularity` |
| Finite-injective shortcut reciprocal budget below 81 | `OrbitReciprocal` |
| First-arrival product and exact-word height control | `FirstArrivalBudget`, `WordProductEnvelope` |
| Integer-atom and reciprocal-square tail bounds | `IntegerAtomTilt`, `FiniteHorizonBudget` |
| Squared occupation with repeated sources and returns | `QuadraticOccupation` |
| Finite complete bounded-slope catalogues | `BoundedSlopeCatalogue` |
| Finite collision bounds and explicit lower-allocation interfaces | `SpineDispersion` |

Catalogue cardinality and source bounds do not give a computable bound on
every hitting time. Finite collision upper bounds do not supply the
branching lower bound required to exclude divergence.

## Citation and release policy

The paper and its supplementary release are maintained in the canonical
research repository. Zenodo concept DOI, covering all published versions:
[10.5281/zenodo.20021537](https://doi.org/10.5281/zenodo.20021537).
The previously published v6 is
[10.5281/zenodo.22936057](https://doi.org/10.5281/zenodo.22936057).

The v7 manuscript and supplementary source archive are published at
[10.5281/zenodo.24284425](https://doi.org/10.5281/zenodo.24284425),
version **7.0.0**.

The repository remains public. Development may be committed locally, but
public pushes are reserved for completed, reviewed research or release
milestones, or an explicit user instruction. Experimental work is not
pushed automatically after every session.

## Attribution and licensing

Piero Borgatta directs the AI-assisted research and formalization. The
[methodology disclosure](https://github.com/PieroBorgatta/Collatz/blob/main/METHODOLOGY.md)
describes the collaboration. Classical results, adapted constructions and
external inputs must not be presented as new theorems of this project.

The **current synchronized source snapshot is CC BY 4.0**, matching the
canonical repository; see [LICENSE](LICENSE). The original standalone MIT
notice is preserved as [LICENSE-MIT](LICENSE-MIT). Earlier MIT grants are
not revoked; historical versions remain available in Git history. The
scope of this update is explained in [PROVENANCE.md](PROVENANCE.md).
