# CollatzShadowing — a Lean 4 + Mathlib formalization

A self-contained Lean 4 (Lake) library formalizing the verified core of the
*Phantom Orbit Shadowing* program on the Collatz conjecture. The sources are
**`sorry`-, `admit`- and `axiom`-free**.

> This library does **not** prove the Collatz conjecture. It formalizes a
> shadowing lemma, a no-infinite-shadowing corollary, an expanding-cycle
> exclusion, finite Collatz–Wielandt spectral-radius certificates, and an
> elementary descent bridge — the rigorously verified part of the program.
> Full project, papers and methodology:
> [github.com/PieroBorgatta/Collatz](https://github.com/PieroBorgatta/Collatz).

## At a glance

- **14 AI-authored modules** (~7,800 lines, ~300 theorems/lemmas), written by
  AI assistants under the author's direction and machine-verified.
- **26 generator-emitted certificate modules** (~43,500 lines) under
  `CollatzShadowing/Generated/`.
- Toolchain: **Lean v4.29.1 + Mathlib v4.29.1** (pinned in `lean-toolchain`
  and `lakefile.toml`).
- Declaration → file map: [`CollatzShadowing/THEOREM_INDEX.md`](CollatzShadowing/THEOREM_INDEX.md).

## Build

```bash
lake exe cache get   # download the Mathlib precompiled cache (several GB)
lake build           # build the whole project
```

Check there are no proof placeholders (no output = clean):

```bash
grep -rnE 'sorry|admit|^[[:space:]]*axiom' CollatzShadowing --include='*.lean'
```

## Headline results

| Result | Declaration | Module |
|---|---|---|
| Exact congruential shadowing | `exact_shadowing`, `exact_shadowing_periods` | `Shadowing` |
| No infinite (periodic) shadowing | `no_infinite_period_congruence_expansive` | `NoInfinite` |
| No positive integer on an expanding cycle | `no_positive_endpoint_eventually_periodic_expansive_congruence` | `NoInfinite` |
| Generic weighted Collatz–Wielandt bound | `spectralRadius_le_of_finiteCWCertificate` | `Bound` |
| Single-node spectral bound `ρ ≤ 97/2000` | `t10j32HighBitTailSpectralRadiusBound_97_2000` | `Generated/T10J32HighBitTailCW` |
| Deterministic `(K,b)` bound `< 3/4` (`K₀=16`) | `k16s16KDeterministicGeneratedSpectralRadiusBound` | `Generated/K16S16KDeterministicCW` |
| Finite weak row-`L¹` bridge | `WeakBridge.weighted_action_diff_le` | `WeakBridge` |
| High-`ν₂` source-tail mass `≤ 2⁻ᴿ` | `WeakBridge.TailCount.dyadic_tail_count_mul_le` | `WeakBridge` |
| Descent ⇒ Collatz (elementary) | `classicalCollatz_of_uniformStrictDescent_provedBridge` | `CollatzBridge` |

## Modules

**Shadowing core** — `Basic` (`S`, `ν₂`), `Phantom` (`C_w`, `A_w`, `q_w`),
`Syracuse2Adic` (`S̃ : ℤ₂ → ℤ₂`), `Auxiliary`, `Shadowing`, `NoInfinite`.

**Finite operator / certificate layer** — `EpisodeGraph`, `Operator`
(`full = core + tail`), `Bound` (Collatz–Wielandt bound bridged to Mathlib's
`spectralRadius`).

**Phase-10 finite bridges** — `WeakBridge` (weighted row-`L¹` bound, exact
high-`ν₂` tail, `BitLength`/dyadic-boundary development, `LabelSplit` schema),
`CollatzBridge` (descent bridge; open hypotheses isolated as named `Prop`s).

**`Generated/`** — finite certificates emitted by AI-written Python generators
(in the [main repo](https://github.com/PieroBorgatta/Collatz)); verified by
Lean.

`Inventory` / `EpisodeInventory` are Mathlib-API scratch buffers.

## Citation

Frozen, citable snapshots are on Zenodo (concept DOI, always latest):
[10.5281/zenodo.20021537](https://doi.org/10.5281/zenodo.20021537).

## Methodology

Built by the author in cross-AI collaboration (Claude, Codex, Gemini), with
every formal claim funnelled through Lean: a proof counts only if `lake build`
succeeds with no `sorry`. See the
[methodology disclosure](https://github.com/PieroBorgatta/Collatz/blob/main/METHODOLOGY.md).

## License

[CC BY 4.0](LICENSE).
