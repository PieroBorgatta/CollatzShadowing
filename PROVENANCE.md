# Source provenance and verification scope

This repository is the standalone library distribution of
<https://github.com/PieroBorgatta/Collatz>. The canonical Lake project is
the `lean/` subdirectory. It is authoritative for the synchronized
mathematical source files.

The current source commit, original paths, destination paths, byte counts
and SHA-256 hashes are recorded in [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json).
Lean files, the entrypoint, toolchain and dependency configuration are
copied byte for byte. Documentation links that leave the canonical
`lean/` directory are rewritten to the recorded immutable Git commit;
the original and rewritten document hashes are both retained.

## Reproducing the export

```sh
python3 tools/export_from_collatz.py --source /absolute/path/to/Collatz
python3 tools/export_from_collatz.py --check
```

The exporter uses an explicit allowlist: the library, its root Lake
configuration, status and index documents, canonical license, and three
strict dependency audits. It rejects uncommitted changes to the exported
Lean proofs/audits. It records any uncommitted exported documents, rather
than silently pretending they belong to the recorded source commit.
It does not copy dependency caches, credentials, external projects,
research experiments, unpublished manuscript files or standalone prototypes.

The June 2026 standalone base was commit `cfd5b20`; the manifest and Git
history identify the exact full source revisions. The v7 synchronization
adds the post-v6 finite arithmetic library and the explicit accelerated-map
singularity correction.

## License scope

The earlier standalone repository was distributed under the MIT license.
That notice is retained in `LICENSE-MIT`; its previous grants and the
earlier MIT snapshots remain available and are not revoked.

This release imports the current canonical source and documentation under
its existing **CC BY 4.0** license. `LICENSE` and the package's SPDX value
therefore match the canonical snapshot. This does not silently designate
new post-v6 CC BY material as MIT or claim that historical MIT copies have
lost their permissions. Preserve the applicable notices and attribution
when reusing either version.

## Verification

The pins remain Lean 4.29.1 and Mathlib 4.29.1. The v7 local standalone
check starts with an empty standalone `.lake/build` directory and reuses
the canonical checkout's already built **dependency packages** only. The
standalone library output directory is separate; there is no shared output
directory with a concurrent canonical build. The build and the three
strict November audits have separate logs and receipts in `verification/`.
The [proof/configuration identity](verification/source_identity.json)
binds the 96 Lean, audit and Lake configuration files used for that
build. A later release commit may refresh documentation and its pinned
links without changing those verified proof/configuration bytes.

The audits have a stated root scope. They are not claims that every
historical declaration has a native-free trusted base: nine legacy finite
checks still use the named `native_decide` axioms allowed by CI. New
analytical results in papers and the paired-word discussion are not
imported by these Lean files. The snapshot is not a cold rebuild of
Mathlib or a replay with an independently implemented kernel, and it has
not been migrated to a more recent Lean toolchain.

As in the canonical library, named open propositions remain explicit
hypotheses. A successful build is not a proof of the Collatz conjecture.

The CI separates formal verification from API documentation deployment.
The latter is retained as an explicit manual `build_docs` input on `main`;
it is not automatically launched on every completed release push.
