# Release and research workflow

- Keep this repository public unless the user explicitly changes that decision.
- Do not push incremental research work automatically. Push only when an
  agreed research/release milestone is complete and verified, or when the
  user explicitly instructs a push.
- The canonical mathematical source is `PieroBorgatta/Collatz`, under
  `lean/`. Use `tools/export_from_collatz.py` to synchronize it and preserve
  source hashes, pinned dependencies, license notices and attribution.
- Preserve published versions and historical evidence. Separate
  Lean-checked results, paper deductions, experiments and open hypotheses.
- Never infer a Collatz proof, a uniform temporal cutoff, or mathematical
  novelty from a successful build or a finite certificate alone.
