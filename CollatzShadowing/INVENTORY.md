# Mathlib Infrastructure Inventory

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-04.

This file records the Mathlib API choices for formalizing the exact
congruential shadowing lemma from Section 3 of
`paper/collatz_spectral_reduction.tex`.

The project is pinned to Lean `4.29.1` and Mathlib `v4.29.1`.

## Tested Commands

Use the local elan installation from this machine:

```bash
/Volumes/AFUOCO/MAC/Applicazioni/elan/bin/lake build
/Volumes/AFUOCO/MAC/Applicazioni/elan/bin/lake env lean CollatzShadowing/Inventory.lean
```

The plain command `lake` may not be on the shell `PATH` in Codex.

## Imports

For Phase 1 API exploration:

```lean
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Multiplicity
import Mathlib.Tactic
```

For later theorem files, prefer narrower imports once the definitions
settle. `import Mathlib` is useful for scratch exploration but too broad
for stable project modules.

## 1.1 Valuations on Nat, Int, Rat

Core declarations:

```lean
#check padicValNat
-- padicValNat (p n : Nat) : Nat

#check padicValInt
-- padicValInt (p : Nat) (z : Int) : Nat

#check padicValRat
-- padicValRat (p : Nat) (q : Rat) : Int

#check padicNorm
-- padicNorm (p : Nat) (q : Rat) : Rat
```

Useful lemmas:

```lean
#check padicValNat.self
-- {p : Nat} -> 1 < p -> padicValNat p p = 1

#check padicValNat.eq_zero_of_not_dvd
-- not divisible by p implies valuation zero

#check padicValInt.of_nat
-- padicValInt p (n : Int) = padicValNat p n

#check padicValRat.of_nat
-- padicValRat p (n : Rat) = padicValNat p n

#check padicValRat.of_int
-- padicValRat p (z : Rat) = padicValInt p z

#check padicValRat.mul
-- valuation of a nonzero rational product

#check padicValRat.pow
-- valuation of a rational power
```

Divisibility bridges for natural numbers:

```lean
#check padicValNat.prime_pow
-- [Fact p.Prime] -> padicValNat p (p ^ n) = n

#check padicValNat_dvd_iff
-- [Fact p.Prime] -> p ^ a ∣ n iff a <= padicValNat p n
```

The general multiplicity API lives in:

```lean
import Mathlib.RingTheory.Multiplicity
```

Useful declarations:

```lean
#check multiplicity
#check emultiplicity
#check pow_dvd_of_le_multiplicity
#check pow_multiplicity_dvd
#check multiplicity_eq_of_dvd_of_not_dvd
```

For this project, `padicValNat`, `padicValInt`, and `padicValRat` are the
right primary API. Use `multiplicity` only if a proof naturally reduces
to generic prime-power divisibility.

## 1.2 Padic and PadicInt

Core types and notation:

```lean
#check Padic
-- Padic (p : Nat) [Fact p.Prime] : Type

#check PadicInt
-- PadicInt (p : Nat) [Fact p.Prime] : Type

#check (ℚ_[2])
-- Type, notation for Padic 2

#check (ℤ_[2])
-- Type, notation for PadicInt 2
```

Use the real Lean notation with Unicode in files:

```lean
example : ℚ_[2] = Padic 2 := rfl
example : ℤ_[2] = PadicInt 2 := rfl
```

Valuations:

```lean
#check Padic.valuation
-- {p : Nat} [Fact p.Prime] -> Q_[p] -> Int

#check PadicInt.valuation
-- {p : Nat} [Fact p.Prime] -> Z_[p] -> Nat
```

Important valuation lemmas:

```lean
#check Padic.valuation_ratCast
-- ((q : Q_[p]).valuation) = padicValRat p q

#check Padic.valuation_intCast
-- ((z : Q_[p]).valuation) = padicValInt p z

#check Padic.valuation_natCast
-- ((n : Q_[p]).valuation) = padicValNat p n

#check Padic.valuation_mul
-- valuation of a nonzero product in Q_[p]

#check Padic.valuation_inv
-- valuation of inverse in Q_[p]

#check Padic.valuation_pow
-- valuation of natural powers in Q_[p]

#check Padic.valuation_zpow
-- valuation of integer powers in Q_[p]

#check Padic.le_valuation_add
-- ultrametric lower bound for valuation of a sum
```

For `ℤ_[p]`:

```lean
#check PadicInt.valuation_coe
-- ((x : Q_[p]).valuation) = x.valuation

#check PadicInt.valuation_mul
-- valuation of a nonzero product in Z_[p]

#check PadicInt.valuation_pow
-- valuation of powers in Z_[p]

#check PadicInt.valuation_p
-- (p : Z_[p]).valuation = 1

#check PadicInt.valuation_p_pow_mul
-- ((p : Z_[p]) ^ n * c).valuation = n + c.valuation, if c != 0
```

Warning: `PadicInt.valuation 0 = 0` by convention. Therefore valuation
inequalities do not by themselves express divisibility of zero by every
power. For congruence, use ideal membership as the primary definition.

## 1.3 Coercions

Working coercions into `ℤ_[2]`:

```lean
example (n : Nat) : ℤ_[2] := (n : ℤ_[2])
example (z : Int) : ℤ_[2] := (z : ℤ_[2])
```

Working coercions into `ℚ_[2]`:

```lean
example (n : Nat) : ℚ_[2] := (n : ℚ_[2])
example (z : Int) : ℚ_[2] := (z : ℚ_[2])
example (q : Rat) : ℚ_[2] := (q : ℚ_[2])
```

Canonical embedding of `ℤ_[2]` into `ℚ_[2]`:

```lean
example (x : ℤ_[2]) : ℚ_[2] := (x : ℚ_[2])
```

Coercion lemmas:

```lean
#check PadicInt.coe_natCast
-- ((n : Z_[p]) : Q_[p]) = n

#check PadicInt.coe_intCast
-- ((z : Z_[p]) : Q_[p]) = z

#check Padic.coe_inj
-- rational casts into Q_[p] are injective

#check Padic.coe_add
#check Padic.coe_sub
#check Padic.coe_mul
#check Padic.coe_div
```

### Rational numbers that are 2-adic integers

Not every rational should be coerced directly into `ℤ_[2]`. The rational
is a 2-adic integer precisely when its denominator is not divisible by 2.
For the phantom fixed point

```text
q_w = C_w / (2^A - 3^L)
```

the denominator is odd, because `2^A` is even for positive `A` while
`3^L` is odd. So `q_w` belongs to `ℤ_[2]`.

Type-checked template:

```lean
noncomputable def ratToZ2 (q : Rat) (hden : ¬ (2 : Nat) ∣ q.den) : ℤ_[2] :=
  ⟨(q : ℚ_[2]), Padic.norm_rat_le_one hden⟩
```

Relevant lemma:

```lean
#check Padic.norm_rat_le_one
-- if p does not divide q.den, then norm (q : Q_[p]) <= 1
```

This is the preferred construction for `q_w : ℤ_[2]` in Phase 2.

## 1.4 Congruence n equiv q modulo 2^k

The paper writes:

```text
n equiv q_w (mod 2^(B_m + 1))
```

with `n : Nat` and `q_w : Rat`, interpreted inside `ℤ_2`.

Recommended Lean definition:

```lean
def PadicCongruentModPow2 (x y : ℤ_[2]) (k : Nat) : Prop :=
  x - y ∈ (Ideal.span {((2 : ℤ_[2]) ^ k)} : Ideal ℤ_[2])
```

Then the lemma hypothesis should look like:

```lean
PadicCongruentModPow2 (n : ℤ_[2]) qwZ2 (B m + 1)
```

where `qwZ2 : ℤ_[2]` is constructed from the rational `q_w` using the
odd-denominator proof above.

This formulation is robust because it handles `x = y` automatically.

Equivalent nonzero valuation form:

```lean
example (x y : ℤ_[2]) (k : Nat) (hxy : x - y ≠ 0) :
    (x - y ∈ (Ideal.span {((2 : ℤ_[2]) ^ k)} : Ideal ℤ_[2])) ↔
      k ≤ (x - y).valuation := by
  exact PadicInt.mem_span_pow_iff_le_valuation (x - y) hxy k
```

The zero case should remain on the ideal-membership side, because
`(0 : ℤ_[2]).valuation = 0`.

For comparison with finite residues and the Python scripts, Mathlib also
has:

```lean
#check Nat.ModEq
#check Int.ModEq
#check ZMod
```

But these are not the preferred primary representation for Lemma 3.1,
because the theorem naturally lives in `ℤ_[2]` and compares an integer
with a rational 2-adic integer.

## 1.5 Modeling Recommendations for Phase 2

Use the following Lean-side architecture:

1. In `Basic.lean`, define:

```lean
def nu2Nat (n : Nat) : Nat := padicValNat 2 n
def nu2Int (z : Int) : Nat := padicValInt 2 z
def nu2Rat (q : Rat) : Int := padicValRat 2 q
```

The accelerated Syracuse map on naturals can be:

```lean
def syracuseOddStep (n : Nat) : Nat :=
  (3 * n + 1) / 2 ^ padicValNat 2 (3 * n + 1)
```

Later proofs should assume `Odd n` or `n % 2 = 1` as needed.

2. In `Phantom.lean`, represent phantom words as a structure rather than
a bare subtype scattered through proofs:

```lean
structure PhantomWord where
  vals : List Nat
  nonempty : vals ≠ []
  positive : ∀ a ∈ vals, 0 < a
```

3. Define `A_w` as `w.vals.sum`, and define `C_w` by folding the pair
`(C_j, A_j)`:

```lean
def affineFoldStep (state : Nat × Nat) (a : Nat) : Nat × Nat :=
  (3 * state.1 + 2 ^ state.2, state.2 + a)
```

4. Define the rational fixed point first:

```lean
qRat = (C_w : Rat) / ((2 : Rat) ^ A_w - (3 : Rat) ^ L)
```

Then define the 2-adic integer representative via `ratToZ2`, with a proof
that the denominator is odd. For the paper's expansive phantoms, this is
the object used in the congruence hypothesis.

5. Define the shadowing congruence by ideal membership, not by valuation:

```lean
def PadicCongruentModPow2 (x y : ℤ_[2]) (k : Nat) : Prop :=
  x - y ∈ (Ideal.span {((2 : ℤ_[2]) ^ k)} : Ideal ℤ_[2])
```

6. Only introduce `PadicInt.valuation` lemmas after unfolding a nonzero
difference, or after splitting the zero case.

## Open Gaps

- A clean proof that the rational `q_w` has odd denominator in Mathlib's
normalized `Rat.den` form still needs to be written. Mathematically it
comes from `2^A - 3^L` being odd and nonzero, but Lean may require a few
integer/rational normalization lemmas.
- The exact statement of Lemma 3.1 may be easier if the phantom word is
modeled together with its periodic extension function
`aAt : Nat -> Nat`, instead of repeatedly using `List.get` with modular
indices.
- Division by `2^a` inside `ℤ_[2]` is not available as division by a unit,
because `2` is not a unit in `ℤ_[2]`. The affine Syracuse maps involving
division by powers of 2 should probably be stated in `ℚ_[2]`, while the
residue/congruence hypotheses live in `ℤ_[2]`.
- For Phase 3, the central proof step will likely use `Padic.valuation`
on `ℚ_[2]` for affine differences, then return to `ℤ_[2]` congruences via
ideal membership where needed.

## Verified Snippet

The following snippet typechecks under the current project pin:

```lean
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers

noncomputable def ratToZ2 (q : Rat) (hden : ¬ (2 : Nat) ∣ q.den) : ℤ_[2] :=
  ⟨(q : ℚ_[2]), Padic.norm_rat_le_one hden⟩

def PadicCongruentModPow2 (x y : ℤ_[2]) (k : Nat) : Prop :=
  x - y ∈ (Ideal.span {((2 : ℤ_[2]) ^ k)} : Ideal ℤ_[2])

example (x y : ℤ_[2]) (k : Nat) (hxy : x - y ≠ 0) :
    PadicCongruentModPow2 x y k ↔ k ≤ (x - y).valuation := by
  exact PadicInt.mem_span_pow_iff_le_valuation (x - y) hxy k
```

## Phase 11 Addition: Conditional Collatz Bridge

`CollatzShadowing/CollatzBridge.lean` records the current proof-theoretic
reduction toward Collatz.  It is intentionally conditional and does not
claim that the finite K16 certificates imply Collatz.

Core declarations:

```lean
def collatzStep (n : ℕ) : ℕ
def ClassicalCollatzConjecture : Prop
def acceleratedOrbitHitsOne (n : ℕ) : Prop
def AcceleratedCollatzConjecture : Prop
def UniformStrictDescentHypothesis : Prop
def AcceleratedToClassicalBridge : Prop
structure BranchDescentModel (σ β : Type*) [Fintype β]
structure GlobalDescentCover (σ β loss : Type*) [Fintype β] [Fintype loss]
inductive FiniteModelLossKind
inductive FiniteModelCoverClass
inductive CoverClassStatus
abbrev ProofToken (P : Prop) : Type
structure FiniteModelCoverSpec (σ β : Type*) [Fintype β]
structure FiniteModelSoundSpec (σ β : Type*) [Fintype β]
def HasStrictDescent (n : ℕ) : Prop
def DirectDropAt (k n : ℕ) : Prop
def syracuseStepWithExponent (a n : ℕ) : ℕ
def evalSyracuseWord : List ℕ → ℕ → ℕ
def SyracuseWordMatchesFrom : List ℕ → ℕ → Prop
theorem evalSyracuseWord_eq_iterate_of_matches
theorem directDropAt_of_word_matches_eval_lt
def evalSyracuseWordChain : List (List ℕ) → ℕ → ℕ
def syracuseWordChainLength : List (List ℕ) → ℕ
def SyracuseWordChainMatchesFrom : List (List ℕ) → ℕ → Prop
theorem evalSyracuseWordChain_eq_iterate_of_matches
theorem directDropAt_of_word_chain_matches_eval_lt
def DirectDropSound
def DirectDropAtSound
theorem directDropSound_of_directDropAtSound
def directDropWitnessOfSound
def BranchSound
def BranchDropAtSound
def BranchWordDropSound
def BranchTransitionChainDropSound
theorem branchSound_of_branchDropAtSound
theorem branchDropAtSound_of_branchWordDropSound
theorem branchSound_of_branchWordDropSound
theorem branchDropAtSound_of_branchTransitionChainDropSound
theorem branchSound_of_branchTransitionChainDropSound
def branchWitnessOfSound
def LossSound
def LossDropAtSound
def LossAbsent
theorem lossSound_of_lossDropAtSound
theorem lossSound_of_lossAbsent
def lossWitnessOfSound
def strictDescentWitnessOfHasStrictDescent
def strictDescentWitnessOfIterate
def strictDescentWitnessOfOneStep
```

The fully formalized theorem

```lean
theorem acceleratedCollatz_of_uniformStrictDescent :
  UniformStrictDescentHypothesis → AcceleratedCollatzConjecture
```

proves by strong induction that a strict-descent theorem for all
positive odd accelerated Syracuse orbits would imply accelerated
termination at `1`.

The elementary classical/accelerated bookkeeping is now proved in Lean.
The theorem

```lean
theorem acceleratedToClassicalBridge :
  AcceleratedToClassicalBridge
```

expands the initial even tail into repeated halvings, then expands each
accelerated Syracuse step into one odd `3n+1` step followed by the exact
number of halving steps.

The older conditional theorem

```lean
theorem classicalCollatz_of_uniformStrictDescent :
  AcceleratedToClassicalBridge →
  UniformStrictDescentHypothesis →
  ClassicalCollatzConjecture
```

is still available, but the proved bridge gives the stronger packaged
theorems

```lean
theorem classicalCollatz_of_uniformStrictDescent_provedBridge :
  UniformStrictDescentHypothesis →
  ClassicalCollatzConjecture

theorem classicalCollatz_of_branchDescentModel :
  (M : BranchDescentModel σ β) →
  WeakBridge.LabelSplit.coverResolved M.cover M.counters →
  ClassicalCollatzConjecture

theorem classicalCollatz_of_globalDescentCover :
  (C : GlobalDescentCover σ β loss) →
  C.branchesResolved →
  ClassicalCollatzConjecture

theorem classicalCollatz_of_finiteModelGlobalCover :
  (C : FiniteModelGlobalCover σ β) →
  C.branchesResolved →
  ClassicalCollatzConjecture

theorem classicalCollatz_of_finiteModelCoverSpec :
  (S : FiniteModelCoverSpec σ β) →
  S.toGlobalDescentCover.branchesResolved →
  ClassicalCollatzConjecture

theorem classicalCollatz_of_finiteModelSoundSpec :
  (S : FiniteModelSoundSpec σ β) →
  S.toCoverSpec.toGlobalDescentCover.branchesResolved →
  ClassicalCollatzConjecture

theorem hasStrictDescent_iff_nonempty_witness :
  HasStrictDescent n ↔ Nonempty (StrictDescentWitness n)

theorem hasStrictDescent_of_directDropAt :
  DirectDropAt k n → HasStrictDescent n
```

`GlobalDescentCover` is the audit version of the target: every positive
odd `n ≠ 1` must be covered by a direct strict-descent witness, a resolved
branch witness, or a declared loss label with its own strict-descent
witness.  A tail/outside/budget class that has no witness cannot be hidden
inside this structure.

The concrete current loss taxonomy is `FiniteModelLossKind`, with four
open classes: `outsideSCC`, `budgetExit`, `valuationTail`, and `stepTail`.
`finiteModelCoverClass_currentStatus` records that `directDrop` is already
a witness class, `resolvedBranch` is acceptable only through branch
semantics and resolved counters, and all four loss classes remain
`openLoss` until proved absent or converted into strict-descent witnesses.
`FiniteModelCoverSpec` is the witness-level working interface: it separates
the direct-drop predicate from the theorem that turns direct drops into
`StrictDescentWitness` values, and then converts to `FiniteModelGlobalCover`.
`FiniteModelSoundSpec` is the propositional interface: it asks for
`DirectDropSound`, `BranchSound`, and `LossSound`, then packages those proofs
through `directDropWitnessOfSound`, `branchWitnessOfSound`, and
`lossWitnessOfSound`.  The step-indexed helpers `DirectDropAtSound`,
`BranchDropAtSound`, and `LossDropAtSound` reduce these obligations to
explicit descent times; `LossAbsent` handles the vacuous case where declared
loss predicates are proved impossible.  `DirectDropAt` is the step-indexed
form expected from concrete direct-drop certificates.  The minimal word
semantics `evalSyracuseWord` / `SyracuseWordMatchesFrom` proves
`evalSyracuseWord_eq_iterate_of_matches`, `evalSyracuseWord_append`,
`SyracuseWordMatchesFrom_append`, and `directDropAt_of_word_matches_eval_lt`:
a matched nonempty exponent word whose evaluated endpoint is below its start
is a direct-drop witness.  The helper
`directDropAt_of_suffix_after_prefix_matches_eval_lt` packages the
common-prefix/suffix form now suggested by the semantic replay audit.
The affine word formula
`evalSyracuseWord_mul_pow_sum_eq_affine_of_matches` proves, under the same
match hypothesis,
`2^sum(w) * evalSyracuseWord w n = 3^length(w) * n + syracuseWordConst w`.
This yields the compact contraction criteria
`directDropAt_of_word_matches_affine_contracting` and
`directDropAt_of_suffix_after_prefix_affine_contracting`.
For the observed A0 semantic-drop common prefix, the named theorem
`a0SemanticDropCommonPrefix_affine_of_matches` proves
`128 * endpoint = 729*n + 817`; the scaled suffix criterion
`directDropAt_of_a0CommonPrefix_suffix_scaled_contracting` is the current
proof-facing target for compressed semantic drop imports.  The threshold
variant `directDropAt_of_a0CommonPrefix_suffix_threshold_contracting` reduces
that scaled inequality to a slope-gap inequality and an explicit lower bound
on `n`, matching the `suffix_threshold_max` audit counter in script `126`.
The finite checker `smallOddHasDirectDropWithin100Bool` verifies the remaining
small range behind the current threshold: every positive odd `n < 455`,
`n != 1`, has a direct accelerated drop within `100` steps.  The theorem
`hasStrictDescent_of_odd_lt_455` packages this as `HasStrictDescent`.  This is
only a finite exception check.  The theorem
`hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_455` combines the
small-case check with the suffix threshold criterion: for future generated
suffix certificates, it is enough to prove the common-prefix word match, a
nonempty suffix, the slope-gap inequality, and the threshold inequality at
`455`.  The row type `A0SemanticSuffixCertificate` and predicate
`A0SemanticSuffixCertificate.ValidAt455` package exactly this script-facing
suffix obligation; theorem
`A0SemanticSuffixCertificate.hasStrictDescent_of_validAt455` turns such a
valid row plus a matched common-prefix word into `HasStrictDescent`.
The coarser row type `A0SemanticSuffixPairCertificate` packages the
`(suffix_len, suffix_sum)` compression: theorem
`A0SemanticSuffixPairCertificate.hasStrictDescent_of_validAt455` certifies any
concrete suffix in a valid pair row once its length, sum, and
`syracuseWordConst` bound are supplied.  Its computable checker
`A0SemanticSuffixPairCertificate.allValidAt455Bool` and theorem
`validAt455_of_mem_of_allValidAt455Bool` are the intended bridge for a future
generated list of pair rows.
`BranchWordDropSound` packages this as the current branch-facing obligation:
for each resolved branch, provide a word match and endpoint descent; the
theorems `branchDropAtSound_of_branchWordDropSound` and
`branchSound_of_branchWordDropSound` feed that into `FiniteModelSoundSpec`.
For growing return branches, `evalSyracuseWordChain`,
`SyracuseWordChainMatchesFrom`, and `BranchTransitionChainDropSound` provide
the safer transition-chain interface: the chain may have intermediate
growth, but its final evaluated endpoint must be below the original source.
The theorems `branchDropAtSound_of_branchTransitionChainDropSound` and
`branchSound_of_branchTransitionChainDropSound` then feed such a chain into
the same global cover.
The same file now records the elementary negative test for affine return
rows.  `AffineTBranch` models a local row
`source_t = q*u+r`, `next_t = a*u+b`; if `a >= q` and `b >= r`, theorem
`AffineTBranch.not_nextLocalInteger_lt_sourceLocalInteger_of_coeffNondecreasing`
shows that the embedded integer `residue + modulus*next_t` cannot be below
`residue + modulus*source_t`.  This is useful precisely because the current
script-126 complete-prefix A0 return rows all pass this non-decreasing test:
they cannot be used as direct strict-descent branches in the same local
coordinate.
The complementary direct-drop arithmetic certificate is
`AffineNatDropBranch`: it compares source and endpoint integers
`sourceSlope*u + sourceIntercept` and `targetSlope*u + targetIntercept`.
The theorem `AffineNatDropBranch.targetN_lt_sourceN_of_coeffDrop` proves a
uniform drop from coefficientwise conditions `targetSlope <= sourceSlope`
and `targetIntercept < sourceIntercept`.  This is the local arithmetic shape
needed by future direct-drop branch imports.  The theorem
`directDropAt_of_word_matches_affineNatDrop` connects it to the Syracuse
semantics: a matched nonempty exponent word, source/endpoint affine
equalities, and the coefficientwise drop certificate produce `DirectDropAt`.
For high-valuation tails, `syracuse_lt_self_of_two_le_exponent` proves the
basic one-step fact: if `1 < n` and `2 <= syracuseExponent n`, then `S n < n`.
The wrapper `directDropAt_one_of_two_le_syracuseExponent` packages the same
fact as `DirectDropAt 1 n`.  This can redirect valuation-cap exits to direct
drops once the source model identifies the intermediate value and proves it
is not `1`.

The missing mathematical target is now:

```text
finite phantom-shadowing/CW layer
  -> GlobalDescentCover / BranchDescentModel + resolved global branch cover
  -> ClassicalCollatzConjecture
```

The finite CW spectral-radius certificates do not by themselves provide
this implication.

`CollatzShadowing/Generated/A0ReturnBranches.lean` contains the current A0
finite-prefix accounting import.  In particular,
`a0CompletePrefixSummariesV2Lt8_declared_tail_counts` extracts the declared
residual tail counts from the complete-prefix summary: `844` valuation-tail
samples, `16` step-tail samples, total `860`.  The theorem
`a0CompletePrefixSummariesV2Lt8_declared_tail_positive` records that this
finite summary is not loss-free; those tails must still be made sound or
proved absent in any future global `FiniteModelSoundSpec`.
The separate semantic replay summary
`a0SemanticReplaySummariesV2Lt8Cap100` records the same complete prefixes
with proof-facing terminal priority and cap `100`.  The theorem
`a0SemanticReplayV2Lt8Cap100_loss_free` proves the finite accounting:
`102488` drops plus `11752` returns equals `114240` total samples, with zero
valuation-tail and step-tail samples, and max drop/return steps `91/75`.
The theorem
`a0SemanticReplayV2Lt8Cap100_reclassifies_conservative_tails` compares this
against the conservative complete-prefix summary: total samples and return
samples are unchanged, while exactly the conservative `860` tail samples move
into the semantic drop count.  This remains finite and cap-specific; it is not
an infinite cover theorem.
The compact drop-word audit
`a0SemanticDropWordAuditSummariesV2Lt8Cap100` records only compression
counters for the semantic drops.  The theorem
`a0SemanticDropWordAuditV2Lt8Cap100_summary` verifies that all `102488`
semantic drop samples share the common prefix, that there are zero suffix
slope-failure words, and that the maximum observed suffix threshold is `455`.
It also records the anti-pattern for proof export: the finite audit has
`57392` phase-word groups and `52696` singleton groups, so raw row import is
not the intended route.  Script `126` now has an opt-in
`--semantic-replay-suffix-certificate` mode that emits one exact row per
observed suffix after the common prefix into the existing JSON stats payload;
read-only complete-prefix checks give zero suffix-certificate failures at
`T12`, `T13`, and `T14`.  The same generated Lean summary records `14348`
suffix-certificate rows across the three prefixes, equal to the distinct
suffix count, with maximum certificate threshold `455`.  It also records the
coarser `(suffix_len, suffix_sum)` pair compression: `882` pair rows across
the three prefixes, T14 max `351`, zero pair-certificate failures, and maximum
pair threshold `455`; the pair-failure counter is aligned with the Lean
`A0SemanticSuffixPairCertificate.ValidAt455` predicate.  A read-only inclusion
audit shows that the T14 pair rows contain the T12/T13 pair rows and dominate
their common-pair constants, so a future generated pair table should start
with the single T14 table rather than three separate prefix tables.  The file
`Generated/A0ReturnBranches.lean` includes one worst-threshold feasibility row
`a0SemanticSuffixPairCertificateT14ThresholdMax`; Lean verifies its
`ValidAt455` arithmetic exactly, and the one-row prototype list passes the
new list checker by `native_decide`.  The same file now imports the full T14
pair-compressed table `a0SemanticSuffixPairCertificatesT14` with `351` rows;
Lean verifies both its row count and all row-level `ValidAt455` checks by
`native_decide`, and `a0SemanticSuffixPairCertificatesT14_matches_summary`
ties the table count and threshold maximum back to the compact audit summary.
The theorem `hasStrictDescent_of_mem_a0SemanticSuffixPairCertificatesT14`
is the finite-table use rule: membership in the T14 pair table plus concrete
length/sum/constant checks and a common-prefix word match imply
`HasStrictDescent`.  `A0SemanticSuffixT14PairCover` packages such one-suffix
assignments, and `hasStrictDescent_of_a0SemanticSuffixT14PairCover` is the
local descent bridge for a future generated suffix-cover map.  The finite
accounting summary `a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100`
records that all observed T12/T13/T14 suffix rows and drop samples are covered
by the T14 pair table with zero finite coverage failures.  This remains a
finite-prefix statement.  Script `126` prints the analogous current-run
coverage audit, including source-level covered/uncovered sample counts, when
`--semantic-replay-suffix-certificate` is enabled.
`A0SemanticDropSourceT14PairCover` is the next proof-facing source-level
object: it combines source hypotheses, a suffix-pair cover, and the actual
common-prefix word match; `hasStrictDescent_of_a0SemanticDropSourceT14PairCover`
turns it into `HasStrictDescent`.  The finite source summary
`a0SemanticDropSourceT14CoverageSummariesV2Lt8Cap100` records zero observed
source-coverage failures through T14.
Read-only T15/T16 stability checks show that this T14 table is not a stable
future cover: new pair keys and larger constants/thresholds appear at both
T15 and T16, and T16 likewise fails to cover T17.  Accordingly,
`CollatzBridge.lean` now includes the parametric cutoff theorem
`hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_cutoff` and the
finite cutoff-464 wrapper
`hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_464`, plus the T18
support wrapper `hasStrictDescent_of_a0CommonPrefix_suffix_threshold_at_648`.
The suffix and
pair certificate APIs now also have `ValidAtCutoff` and `ValidAt464` variants
plus computable list checkers, so future T16-style tables can use the correct
cutoff rather than pretending to satisfy `ValidAt455`.
The compact generated summary `a0SemanticReplayT19A20Cap200Cutoff648` records
the current high-cap T19 audit: with `a_cap=20`, semantic step cap `200`, and
certificate cutoff `648`, T19 is loss-free and all semantic-drop source
samples are covered by the current-run pair table.  This is still finite
accounting, not a parametric cover theorem.
The next compact generated summary `a0SemanticReplayT20A20Cap200Cutoff648`
records the same high-cap audit at T20: it is loss-free, has full source
coverage `3739212/3739212`, keeps the same observed threshold maximum `647`
and max drop/return steps `138/105`, while the pair-row count grows from
`749` to `842`.  The comparison theorem
`a0SemanticReplayT19T20A20Cap200Cutoff648_stable_bounds` records this finite
T19/T20 stability only; it is not a parametric or asymptotic theorem.
The proof-facing suffix/source cover interface has also been made independent
of the T14 table: `A0SemanticSuffixPairCover` and
`A0SemanticDropSourcePairCover` accept an arbitrary finite pair-certificate
table, while
`hasStrictDescent_of_a0SemanticSuffixPairCoverAtCutoff` and
`hasStrictDescent_of_a0SemanticDropSourcePairCoverAtCutoff` use any
`allValidAtCutoffBool cutoff rows = true` proof plus a small-exception theorem
below that cutoff.  The generated T14 table is connected to this interface by
`a0SemanticSuffixPairCertificatesT14_allValidAtCutoff455` and
`A0SemanticSuffixT14PairCover.toGeneric`.
The higher-level `A0SemanticDropTableSpec` packages this table-validity data
once and exposes `A0SemanticDropTableSpec.SourceCover`; theorem
`A0SemanticDropTableSpec.hasStrictDescent_of_sourceCover` is now the clean
local target.  The generated T14 data instantiates it as
`a0SemanticDropTableSpecT14`.
At the branch level, `A0SemanticDropBranchCoverSound` and
`branchSound_of_a0SemanticDropBranchCoverSound` connect this local table
contract to the existing `BranchSound` interface used by
`FiniteModelSoundSpec`: a resolved branch must supply source-cover data into
the chosen table.
The common-prefix part of that source-cover data is no longer merely an
observed finite-prefix fact.  Lean proves
`a0SemanticDropCommonPrefix_matches_source_cylinder` for every
`n = 103 + 256*t`, the A0 source cylinder used by script `126`, and proves
`eval_a0SemanticDropCommonPrefix_source_cylinder` with endpoint
`593 + 1458*t`.  The `AffineTBranch.localInteger` wrappers connect this to
the local-coordinate representation, and
`AffineTBranch.a0SemanticDropSourcePairCover_of_localInteger_suffixCover`
reduces source-cover construction to a suffix match from that endpoint plus
a valid suffix-pair cover.
This residual datum is now named `A0EndpointSuffixPairCover`; the table-level
theorem `A0SemanticDropTableSpec.hasStrictDescent_of_endpointSuffixCover`
turns it into `HasStrictDescent (103 + 256*t)`.  The generated T14 table has
the specialized wrapper
`hasStrictDescent_of_a0SemanticDropTableSpecT14_endpointSuffixCover`.
The first post-prefix suffix split is formalized: after endpoint
`593 + 1458*t`, theorem `syracuseExponent_a0CommonPrefix_endpoint_of_odd_t`
forces the next exponent to be `1` when `t` is odd, while
`syracuseExponent_a0CommonPrefix_endpoint_even_t` rewrites the even case as
`2 + ν₂(445 + 2187*u)`.  Thus the next obstruction is a genuine recursive
valuation problem on a new affine parameter.
A no-write suffix-closure probe found no misses for `t < 2^20` within
suffix cap `300`, but it also did not exhibit a small finite closure:
distinct suffix words grew from `206920` at `D=19` to `383215` at `D=20`,
and pair rows grew from `982` to `1123`.  First suffix exponent `>= 5`
drops coefficientwise in one step; the low-exponent branches `1..4` are the
recursive obstruction.
A second exact no-write probe followed the repeated first-bad `e=1` branch.
For every tested depth `m <= 30`, a residue class `t == r_m (mod 2^m)` forces
the first `m` post-prefix suffix exponents to be `1`, and the affine endpoint
after those steps remains coefficientwise above the source.  At `m=30`,
`r_m = 79536431` and the slope ratio is about `1.09e6`.  This rules out a
proof strategy based on uniformly bounded suffix length/table closure.  Lean
now contains the local affine obstruction API
`AffineNatDropBranch.CoeffNondecreasing`, `AffineNatDropBranch.eOneChild`,
and `AffineNatDropBranch.eOneChild_not_coeffDrop_of_slope_growth`.
The repeated `e=1` boundary is not mysterious: the residue bits are periodic
with period `18` in the no-write probe and represent the 2-adic parameter
`t = -11/27`.  Lean records
`a0Endpoint_phantomParameter_eq_negOne`,
`593 + 1458*(-11/27) = -1`, and
`a0Source_phantomParameter_eq_negThirtyFiveOverTwentySeven`,
`103 + 256*(-11/27) = -35/27`.  Thus this obstruction is the standard `-1`
phantom endpoint written in the A0 post-prefix coordinate.
The periodic-boundary diagnosis is now general rather than one example.
`syracuseWordAffineEndpointQ` and `syracuseWordFormalFixedPoint` define the
rational affine map and formal periodic endpoint for an exponent word.
Theorem `syracuseWordFormalFixedPoint_fixed` verifies the fixed-point
identity when the denominator is nonzero, and
`syracuseWordFormalFixedPoint_neg_of_expanding` proves that every nonempty
word satisfying `2^sum(word) < 3^length(word)` has a negative formal fixed
point.  Examples `[1]`, `[1,2]`, and `[2,1]` give `-1`, `-5`, and `-7`.
The exact deviation formula
`syracuseWordAffineEndpointQ_sub_formalFixedPoint` shows that one word
application multiplies `x - x_*` by `3^length/2^sum`, and
`syracuseWordExpansionFactor_gt_one_of_expanding` records that this multiplier
is larger than `1` in the expanding case.
A no-write enumeration found `6050` primitive binary low-average periodic
words through length `12`; these are all phantom-boundary examples, not
positive integer cycles.
Exact no-write residue lifting for repeated patterns `[1]`, `[1,2]`,
`[2,1]`, `[1,1,2]`, `[1,2,1]`, and `[2,1,1]` confirms that their finite
approximating residue classes can force arbitrarily long coefficientwise
non-drop prefixes.  The next proof target is therefore not a finite suffix
closure, but an exit/Diophantine mechanism for natural integers near negative
periodic phantom boundaries, or a controlled fallback to finite-rank
certificates.
An additional no-write exit probe on the same repeated patterns, through
`20` repetitions and suffix cap `5000`, found no misses after the forced
prefixes.  This supports, but does not prove, a two-stage exit/renewal target:
control finite neighborhoods of periodic phantom boundaries, then prove a
drop after leaving those neighborhoods.
The table-free endpoint target is now named `A0EndpointSuffixExit t`: from
the A0 endpoint `593 + 1458*t`, some matched suffix must land below the
original source `103 + 256*t`.  The theorem
`hasStrictDescent_of_a0EndpointSuffixExit` proves that this target directly
implies `HasStrictDescent (103 + 256*t)`.  This is the clean local statement
for any future exit/renewal proof.  `A0EndpointSuffixExitAll` and
`hasStrictDescent_a0Cylinder_of_endpointSuffixExitAll` package the conditional
all-parameter version for the A0 cylinder.
The direct certificate criteria
`a0EndpointSuffixExit_of_suffix_scaled_contracting`,
`a0EndpointSuffix_scaled_contracting_of_threshold`, and
`a0EndpointSuffixExit_of_suffix_threshold_contracting` turn a matched suffix
from `593 + 1458*t` into `A0EndpointSuffixExit t` using only the endpoint
affine inequality, or its threshold form with slope gap
`256*2^sum - 1458*3^length`.
The widest no-write phantom-neighborhood probe so far checked `62037`
primitive expanding words on `{1,2,3,4}` through length `12`, repeated `10`
times, with exit cap `5000`; it found no misses.  The smallest observed
surplus margin over `log2(729/128)` was about `0.001474779`, indicating that
the slope barrier is sharp and unlikely to admit a comfortable uniform
margin.
A follow-up no-write check found that all these phantom-neighborhood exits
occur exactly at the first matched-suffix prefix satisfying
`1458*3^L <= 256*2^A`; the endpoint threshold inequality is already true at
that first crossing.  The same rule held for the dense sample
`0 <= t < 2^20` under cap `1000`, with max suffix length `205`.  This is
finite evidence for a first-barrier crossing theorem, not a proof.
A fixed-pattern repetition probe indicates that the post-periodic extra tail
is not uniformly bounded in a simple way: for patterns such as
`11121211212`, `121111114121`, and `211111311111`, increasing repetitions can
push the extra segment into the hundreds of steps.  The plausible target is
therefore first-barrier crossing, not a periodic-word plus bounded-tail
automaton.
Lean now names this target.  `A0EndpointSuffixSlopeBarrier` and
`A0EndpointSuffixThreshold` are the two endpoint inequalities;
`A0FirstBarrierSuffix` packages a matched nonempty suffix crossing the slope
barrier while all nonempty proper prefixes remain below it.
`A0FirstBarrierExistsAll` and `A0FirstBarrierThresholdAutomatic` are the two
open obligations.  Theorems
`a0EndpointSuffixExit_of_firstBarrier_threshold` and
`A0EndpointSuffixExitAll_of_firstBarrier` prove the conditional bridge from
those obligations to `A0EndpointSuffixExitAll`.
Lean also proves the length-one base case of the threshold side:
`syracuseWordConst_append_singleton` records the append-singleton constant
formula, and `a0EndpointSuffixThreshold_singleton_of_barrier` /
`a0FirstBarrierThreshold_singleton` prove that a singleton first-barrier suffix
automatically satisfies `A0EndpointSuffixThreshold`.  This is not the general
`A0FirstBarrierThresholdAutomatic` theorem and leaves longer suffixes and
`A0FirstBarrierExistsAll` open.
The threshold is monotone in the endpoint parameter: lemmas
`a0EndpointSuffixThreshold_mono_t` and
`a0EndpointSuffixThreshold_of_one_le` move any verified threshold inequality
to larger `t`.  This isolates the next required input as a lower bound on the
matched parameter, rather than another finite word metric.
The exact matching congruence is now available in Lean.  For a nonempty
matched word, `evalSyracuseWord_odd_of_matches` proves that the endpoint is
odd, and `padicValNat_syracuseWordAffine_of_matches` proves
`ν₂(3^len*n + C_word) = sum(word)`.  The A0-specific corollary
`padicValNat_a0EndpointSuffixAffine_of_matches` applies this to
`n = 593 + 1458*t`.  This is the formal input needed to turn first-barrier
matching into residue classes and lower bounds on `t`.
The same bridge is available as divisibility/congruence:
`syracuseWordAffine_dvd_of_matches`,
`a0EndpointSuffixAffine_dvd_of_matches`, `A0EndpointSuffixCongruence`, and
`a0EndpointSuffixCongruence_of_matches`.  In A0 form it says
`2^sum ∣ (593*3^len + C_word) + 2*(729*3^len)*t`, leaving the inverse/residue
choice for a later proof rather than baking it into the API.  Lemma
`a0EndpointSuffixCongruence_reducedCoeff_odd` records that the reduced
coefficient `729*3^len` is odd.  Lemma
`a0EndpointSuffixCongruence_half_of_even_constant` is the inverse-ready
halving step: under `sum = a+1` and
`593*3^len + C_word = 2*b`, the congruence gives
`2^a ∣ b + (729*3^len)*t`.
The longer-suffix threshold target is also factored through
`A0EndpointSuffixThresholdWitness`: prove the threshold at some `t0 <= t`, then
use monotonicity.  `A0FirstBarrierThresholdWitnessAutomatic` and
`A0FirstBarrierThresholdAutomatic_of_thresholdWitness` record the resulting
intermediate obligation.
The first-barrier package now exposes the congruence automatically:
`a0FirstBarrierSuffix_congruence` derives `A0EndpointSuffixCongruence` from a
first-barrier suffix, and
`A0FirstBarrierCongruenceThresholdWitnessAutomatic` names the reduced target
`first-barrier + A0 linear congruence => threshold witness`.
`A0FirstBarrierThresholdWitnessAutomatic_of_congruence` connects this reduced
target back to the previous witness formulation.
The naive slope-only extension is now explicitly ruled out in Lean:
`a0NaiveSlopeBarrierCounterexampleWord` crosses the slope barrier, but
`a0NaiveSlopeBarrierCounterexample_thresholdZeroFails` proves that
`A0EndpointSuffixThreshold 0` fails for it.  A no-write congruence lift for
that same word gives the compatible matched class
`t == 237364345562 (mod 2^39)`, far above the `t >= 1` needed by the threshold.
The longer-suffix proof must therefore use matching congruences/lower bounds
on `t`, not just slope arithmetic.
Lean proves the concrete repair
`a0NaiveSlopeBarrierCounterexample_threshold_of_match`: if this word actually
matches from the A0 endpoint, its first exponent rules out `t = 0`, and the
threshold follows from the `t = 1` check plus monotonicity.

Decision recorded 2026-06-04: the Collatz-relevant continuation is the
pointwise A0 first-barrier route, not the weak/L1/operator approximation route.
The weak branch remains useful as an operator-approximation program, but it does
not remove the distributional-to-pointwise barrier.  The pointwise branch is
blocked at the aperiodic obstruction: `A0FirstBarrierExistsAll` would fail via
an infinite expanding valuation word that shadows changing phantom
neighborhoods without ever crossing the slope barrier.  The periodic
no-shadowing theorem excludes eventually periodic phantom behavior through a
fixed-point equation, but that equation disappears for aperiodic limits
`ξ_W`.  The next serious mathematical question is whether first-barrier
minimality plus the A0 congruence/threshold package imposes a new rigidity on
aperiodic `ξ_W`, or whether this is only a cleaner parity-vector reformulation.
`NoInfinite.lean` now records the positive boundary result explicitly as
`no_positive_endpoint_eventually_periodic_expansive_congruence`: any positive
post-prefix endpoint is excluded from all period-congruence classes of an
expansive phantom period.  This is the formal limit of the current phantom
sign argument; it excludes the eventually periodic expansive obstruction and
leaves the aperiodic obstruction untouched.

## Phase 8 Additions: Episode Graphs and Finite Certificates

Phase 8 extends the formalization beyond the Section-3 2-adic
shadowing core. The detailed API reconnaissance is in
`CollatzShadowing/EPISODE_INVENTORY.md`; this section records the
production choices now present in the Lean tree.

### Directed Episode Graph

Mathlib in this project pin does not provide a production directed graph
API that is a better fit than a local relation. The production module is
`CollatzShadowing/EpisodeGraph.lean`.

Core declarations:

```lean
abbrev EpisodeRel (α : Type*) := α → α → Prop

structure EpisodeNode where
  k : ℕ
  c : ℕ
  b : ℕ

def Reachable (E : EpisodeRel α) (u v : α) : Prop :=
  Relation.ReflTransGen E u v
```

For finite certificates, `TruncatedEpisodeNode K C B` uses products of
`Fin`, and `TruncatedEpisodeGraph.SCC`, `Walk`,
`HubSCCCertificate`, and `CriticalSCCCertificate` provide an explicit
certificate import shape based on finite paths. The generated module
`CollatzShadowing/Generated/K16S16KSCC.lean` instantiates this shape for
the 37-state compressed `K,b` Phase-7 SCC, including the Boolean edge
table, hub walks, SCC object, and critical-SCC certificate. It is
generated by `scripts/phantom_taxonomy/lean_scc_certificate.py` from the
Phase-7 JSON certificate. `CollatzShadowing/Generated/K16S16KBridge.lean`
checks that this SCC certificate and the generated CW matrix certificate
use the same `Fin 37` state ordering and labels, and packages the
combined result as `k16s16KCertifiedComponentWithCW`.

### Finite Phase States and Operators

`CollatzShadowing/Operator.lean` defines the finite phase state used by
the truncated operator layer:

```lean
abbrev PhaseState (V : ℕ) :=
  Fin (V + 1) × Fin 4 × Fin 4

abbrev TransferMatrix (V : ℕ) :=
  Matrix (PhaseState V) (PhaseState V) NNReal
```

The operator API uses `NNReal` so non-negativity is carried by the entry
type. The local row-bound predicate is:

```lean
def RowSubstochastic {V : ℕ} (M : TransferMatrix V) : Prop :=
  ∀ i, ∑ j, M i j ≤ 1
```

`splitCore`, `splitTail`, and
`decompositionOfPartitionFromFull` implement the finite
`full = core + tail` decomposition from a decidable entry partition. The
split matrices inherit row-substochasticity from the full matrix by
pointwise domination.

`CollatzShadowing/Generated/T10CriticalSymbolic.lean` is generated by
`scripts/phantom_taxonomy/lean_phase_transfer.py` from
`collatz_75_critical_symbolic_edges.csv`. It imports the exact rational
`T = 10` empirical critical-symbolic full matrix as
`Generated.t10CriticalSymbolicFull`, proves
`Generated.t10CriticalSymbolicFull_rowSubstochastic`, and packages
`Generated.t10CriticalSymbolicBaselineDecomposition` with `core = full`
and `tail = 0`. This baseline object checks the generated empirical
matrix against the `OperatorDecomposition` API; the true
empirical-signature majority `core/tail` partition is still a later
generated refinement.

`scripts/phantom_taxonomy/export_high_bit_tail_edges.py` reuses the
majority-signature split from
`scripts/spectral_program/77_high_bit_tail_bound.py` but exports exact
rational edge weights. For `T = 10, j = 32`, the generated CSV
`scripts/phantom_taxonomy/high_bit_tail_edges_T10_j32.csv` is imported
by `CollatzShadowing/Generated/T10J32HighBitTail.lean`. That module
defines `Generated.t10j32HighBitTailCore`,
`Generated.t10j32HighBitTailTail`, and
`Generated.t10j32HighBitTailFull := core + tail`, with theorem
`Generated.t10j32HighBitTailFull_eq_core_add_tail`. The observed
nonterminal state set reaches valuation coordinate `13`, so these
matrices live over `TransferMatrix 13`. The same module uses generated
per-row destination supports to prove exact row-sum lemmas and the
row-substochasticity certificates
`Generated.t10j32HighBitTailCore_rowSubstochastic`,
`Generated.t10j32HighBitTailTail_rowSubstochastic`, and
`Generated.t10j32HighBitTailFull_rowSubstochastic`, then packages the
true majority split as
`Generated.t10j32HighBitTailDecomposition : OperatorDecomposition 13`.

### Collatz-Wielandt Certificate Layer

`CollatzShadowing/Bound.lean` deliberately starts with a finite,
rowwise certificate predicate rather than a spectral theorem:

```lean
structure FiniteCWBasis (ι : Type*) where
  vector : ι → NNReal
  positive : ∀ i, 0 < vector i

def FiniteCWCertificate {ι : Type*} [Fintype ι]
    (M : Matrix ι ι NNReal)
    (basis : FiniteCWBasis ι)
    (alpha : NNReal) : Prop :=
  ∀ i, Matrix.mulVec M basis.vector i ≤ alpha * basis.vector i
```

The exact arithmetic import layer is:

```lean
structure ClearedCWRowBound where
  lhsNum : ℕ
  lhsDen : ℕ
  lhsDen_pos : 0 < lhsDen
  vector : ℕ
  vector_pos : 0 < vector
  alphaNum : ℕ
  alphaDen : ℕ
  alphaDen_pos : 0 < alphaDen
  cleared : lhsNum * alphaDen ≤ alphaNum * vector * lhsDen
```

`ClearedCWRowBound.toNNRealInequality` converts the denominator-cleared
natural-number inequality into the corresponding `NNReal` row
inequality. `EvaluatedCWRowBound` adds the semantic equalities that
identify the cleared row with one row of `Matrix.mulVec`, and
`finiteCWCertificateOfEvaluatedRows` packages all evaluated rows into a
full finite certificate.

For the finite operator decomposition, `FiniteCWCertificate.add`,
`finiteCWCertificateOfSumEq`, `CWCertificate.add`, and
`OperatorDecomposition.cwCertificate_full` prove the rowwise
`core + tail` Collatz-Wielandt bound over a shared positive basis.

The spectral bridge in `Bound.lean` realifies finite `NNReal` matrices
with `nnrealMatrixToReal`. It first proves an explicit matrix `ℓ∞`
operator-norm bound via `matrixLinftyOpNNNorm` and
`spectralRadius_le_of_matrixLinftyOpNNNorm_le`, then proves
`spectralRadius_le_of_finiteCWCertificate` by conjugating the realified
matrix with the positive diagonal matrix of the CW basis. The generic
`core + tail` version is `spectralRadius_le_of_finiteCWCertificateOfSumEq`;
the phase-state version is
`OperatorDecomposition.spectralRadius_le_full`.

### Generated 37-State Certificate

`CollatzShadowing/Generated/K16S16KExactCWSummary.lean` is generated by
`scripts/phantom_taxonomy/lean_cw_summary.py` from the Phase-7 JSON
certificate
`scripts/phantom_taxonomy/orbit_harness_k16_s16_scc_K_cw_certificate.json`.

It defines:

- `K16S16KState := Fin 37`
- `k16s16KMatrix : Matrix K16S16KState K16S16KState NNReal`
- `k16s16KCWBasis : FiniteCWBasis K16S16KState`
- `k16s16KAlphaNNReal : NNReal`
- 37 cleared row certificates and row-evaluation witnesses
- `k16s16KFiniteCWCertificate`

The final certificate has type:

```lean
FiniteCWCertificate k16s16KMatrix k16s16KCWBasis k16s16KAlphaNNReal
```

The generated row-evaluation proofs use row support finsets and
`Finset.sum_subset` to avoid expanding all 37 columns for every row.
Some generated row arithmetic is large enough to require a scoped
`set_option maxHeartbeats 1000000`.

### Generated Spectral Bound

`CollatzShadowing/Generated/K16S16KBridge.lean` now applies
`spectralRadius_le_of_finiteCWCertificate` to
`k16s16KFiniteCWCertificate`, exposing:

```lean
Generated.k16s16KSpectralRadiusBound :
  spectralRadius ℝ (nnrealMatrixToReal k16s16KMatrix) ≤
    (k16s16KAlphaNNReal : ℝ≥0∞)
```

The packaged object `Generated.k16s16KCertifiedComponentWithCW` includes
the generated critical-SCC certificate, the generated finite CW
certificate, the spectral-radius bound, and the label/order
compatibility facts.

### Generated Deterministic Residue-Cell Certificate

`CollatzShadowing/Generated/K16S16KDeterministicCW.lean` is generated by
the same `scripts/phantom_taxonomy/lean_cw_summary.py` pipeline, using
the deterministic finite residue-cell JSON certificate
`scripts/phantom_taxonomy/deterministic_k16_s16_residue_K_cw_certificate.json`.
The generator now accepts declaration-prefix and state-type arguments so
this deterministic 37-state certificate can be imported next to the
older empirical `K,b` certificate without namespace collisions.

It exposes:

```lean
Generated.k16s16KDeterministicFiniteCWCertificate :
  FiniteCWCertificate
    k16s16KDeterministicMatrix
    k16s16KDeterministicCWBasis
    k16s16KDeterministicAlphaNNReal

Generated.k16s16KDeterministicGeneratedSpectralRadiusBound :
  spectralRadius ℝ (nnrealMatrixToReal k16s16KDeterministicMatrix) ≤
    (k16s16KDeterministicAlphaNNReal : ℝ≥0∞)
```

Here `k16s16KDeterministicAlpha = 3/4`, matching the exact deterministic
finite residue-cell Collatz-Wielandt certificate.

The `lift_bits = 5` and `lift_bits = 6` deterministic sensitivity
checks are also imported as Lean-generated certificates:

- `CollatzShadowing/Generated/K16S16KLB5DeterministicCW.lean`
- `CollatzShadowing/Generated/K16S16KLB6DeterministicCW.lean`

They expose:

```lean
Generated.k16s16KLB5DeterministicGeneratedSpectralRadiusBound :
  spectralRadius ℝ (nnrealMatrixToReal k16s16KLB5DeterministicMatrix) ≤
    (k16s16KLB5DeterministicAlphaNNReal : ℝ≥0∞)

Generated.k16s16KLB6DeterministicGeneratedSpectralRadiusBound :
  spectralRadius ℝ (nnrealMatrixToReal k16s16KLB6DeterministicMatrix) ≤
    (k16s16KLB6DeterministicAlphaNNReal : ℝ≥0∞)
```

These are sensitivity certificates, not replacements for the
`lift_bits = 4` production theorem and not a convergence claim.
