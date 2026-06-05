/-
Generated finite A0 return-branch data for the Phase-10 weak branch.

Source JSON:
  scripts/spectral_program/collatz_126_current_A0_v2lt8_A0_return_branch_affine_probe_branches.json

Generated from the script-126 sampled branch extraction.  These rows say:
for each sampled point in a row, the observed return satisfies

  source_t = q*u+r,
  next_t   = a*u+b,
  delta    = bitLength(next_t) - bitLength(source_t).

The fields `refinedQ/refinedR/refinedA/refinedB` further refine the
source progression so that the sampled finite destination state is fixed:

  source_t = refinedQ*v+refinedR,
  next_t   = refinedA*v+refinedB.

The auxiliary word-cylinder table records the exact 2-adic cylinder
arithmetic for the distinct valuation words visible in this sampled
extraction, plus the affine no-drop prefix check.  This is stronger than
a sample check for the valuation word, but it still does not certify the
global "first return" condition of the shadowing automaton.

This file records sampled finite branch data only.  It does not prove
that the return label persists for every `u`, and it does not prove the
Phase-10 low-v2 limit.
-/

import CollatzShadowing.CollatzBridge

set_option linter.style.longLine false

namespace CollatzShadowing
namespace Generated

/-- One sampled A0 return branch after residue reparameterization. -/
structure A0ReturnBranch where
  phase : String
  dst : String
  step : Nat
  word : List Nat
  sampleCount : Nat
  q : Nat
  r : Nat
  a : Nat
  b : Nat
  dstV2 : Nat
  dstOdd : Nat
  dstH : Nat
  stateModBits : Nat
  uResidueMod : Nat
  uResidue : Nat
  refinedQ : Nat
  refinedR : Nat
  refinedA : Nat
  refinedB : Nat
  formulaFailures : Nat
  deltaFailures : Nat
  refinedFormulaFailures : Nat
  refinedStateFailures : Nat
  exactOnSamples : Bool
  deriving Repr, DecidableEq

/--
Sampled `v2 < 8` return branches from script 126.

Rows with no sampled returns are not represented here; they contribute no
return branch to this finite extraction table.
-/
def a0ReturnBranchesV2Lt8 : List A0ReturnBranch :=
  [
    { phase := "0|3|0", dst := "0|3|1", step := 6,
      word := [1, 1, 2, 1, 1, 1], sampleCount := 64,
      q := 128, r := 3, a := 729, b := 19,
      dstV2 := 0, dstOdd := 3, dstH := 1,
      stateModBits := 2, uResidueMod := 4, uResidue := 0,
      refinedQ := 512, refinedR := 3, refinedA := 2916, refinedB := 19,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "0|3|1", dst := "0|3|2", step := 6,
      word := [1, 1, 2, 1, 1, 1], sampleCount := 64,
      q := 128, r := 3, a := 729, b := 19,
      dstV2 := 0, dstOdd := 3, dstH := 2,
      stateModBits := 2, uResidueMod := 4, uResidue := 0,
      refinedQ := 512, refinedR := 3, refinedA := 2916, refinedB := 19,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "0|3|2", dst := "0|3|3", step := 6,
      word := [1, 1, 2, 1, 1, 1], sampleCount := 64,
      q := 128, r := 3, a := 729, b := 19,
      dstV2 := 0, dstOdd := 3, dstH := 3,
      stateModBits := 2, uResidueMod := 4, uResidue := 0,
      refinedQ := 512, refinedR := 3, refinedA := 2916, refinedB := 19,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "0|3|3", dst := "0|3|0", step := 6,
      word := [1, 1, 2, 1, 1, 1], sampleCount := 64,
      q := 128, r := 3, a := 729, b := 19,
      dstV2 := 0, dstOdd := 3, dstH := 0,
      stateModBits := 2, uResidueMod := 4, uResidue := 0,
      refinedQ := 512, refinedR := 3, refinedA := 2916, refinedB := 19,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "2|3|0", dst := "0|3|1", step := 4,
      word := [1, 1, 2, 1], sampleCount := 64,
      q := 32, r := 12, a := 81, b := 31,
      dstV2 := 0, dstOdd := 3, dstH := 1,
      stateModBits := 2, uResidueMod := 4, uResidue := 0,
      refinedQ := 128, refinedR := 12, refinedA := 324, refinedB := 31,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "2|3|1", dst := "0|3|2", step := 4,
      word := [1, 1, 2, 1], sampleCount := 64,
      q := 32, r := 12, a := 81, b := 31,
      dstV2 := 0, dstOdd := 3, dstH := 2,
      stateModBits := 2, uResidueMod := 4, uResidue := 0,
      refinedQ := 128, refinedR := 12, refinedA := 324, refinedB := 31,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "2|3|2", dst := "0|3|3", step := 4,
      word := [1, 1, 2, 1], sampleCount := 64,
      q := 32, r := 12, a := 81, b := 31,
      dstV2 := 0, dstOdd := 3, dstH := 3,
      stateModBits := 2, uResidueMod := 4, uResidue := 0,
      refinedQ := 128, refinedR := 12, refinedA := 324, refinedB := 31,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "2|3|3", dst := "0|3|0", step := 4,
      word := [1, 1, 2, 1], sampleCount := 64,
      q := 32, r := 12, a := 81, b := 31,
      dstV2 := 0, dstOdd := 3, dstH := 0,
      stateModBits := 2, uResidueMod := 4, uResidue := 0,
      refinedQ := 128, refinedR := 12, refinedA := 324, refinedB := 31,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "3|1|0", dst := "3|1|1", step := 9,
      word := [1, 1, 2, 1, 1, 1, 2, 2, 1], sampleCount := 64,
      q := 4096, r := 8, a := 19683, b := 40,
      dstV2 := 3, dstOdd := 1, dstH := 1,
      stateModBits := 5, uResidueMod := 32, uResidue := 0,
      refinedQ := 131072, refinedR := 8, refinedA := 629856, refinedB := 40,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "3|1|1", dst := "3|1|2", step := 9,
      word := [1, 1, 2, 1, 1, 1, 2, 2, 1], sampleCount := 64,
      q := 4096, r := 8, a := 19683, b := 40,
      dstV2 := 3, dstOdd := 1, dstH := 2,
      stateModBits := 5, uResidueMod := 32, uResidue := 0,
      refinedQ := 131072, refinedR := 8, refinedA := 629856, refinedB := 40,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "3|1|2", dst := "3|1|3", step := 9,
      word := [1, 1, 2, 1, 1, 1, 2, 2, 1], sampleCount := 64,
      q := 4096, r := 8, a := 19683, b := 40,
      dstV2 := 3, dstOdd := 1, dstH := 3,
      stateModBits := 5, uResidueMod := 32, uResidue := 0,
      refinedQ := 131072, refinedR := 8, refinedA := 629856, refinedB := 40,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "3|1|3", dst := "3|1|0", step := 9,
      word := [1, 1, 2, 1, 1, 1, 2, 2, 1], sampleCount := 64,
      q := 4096, r := 8, a := 19683, b := 40,
      dstV2 := 3, dstOdd := 1, dstH := 0,
      stateModBits := 5, uResidueMod := 32, uResidue := 0,
      refinedQ := 131072, refinedR := 8, refinedA := 629856, refinedB := 40,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "5|1|0", dst := "1|1|1", step := 10,
      word := [1, 1, 2, 1, 1, 1, 2, 3, 2, 1], sampleCount := 64,
      q := 32768, r := 32, a := 59049, b := 58,
      dstV2 := 1, dstOdd := 1, dstH := 1,
      stateModBits := 3, uResidueMod := 8, uResidue := 0,
      refinedQ := 262144, refinedR := 32, refinedA := 472392, refinedB := 58,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "5|1|1", dst := "1|1|2", step := 10,
      word := [1, 1, 2, 1, 1, 1, 2, 3, 2, 1], sampleCount := 64,
      q := 32768, r := 32, a := 59049, b := 58,
      dstV2 := 1, dstOdd := 1, dstH := 2,
      stateModBits := 3, uResidueMod := 8, uResidue := 0,
      refinedQ := 262144, refinedR := 32, refinedA := 472392, refinedB := 58,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "5|1|2", dst := "1|1|3", step := 10,
      word := [1, 1, 2, 1, 1, 1, 2, 3, 2, 1], sampleCount := 64,
      q := 32768, r := 32, a := 59049, b := 58,
      dstV2 := 1, dstOdd := 1, dstH := 3,
      stateModBits := 3, uResidueMod := 8, uResidue := 0,
      refinedQ := 262144, refinedR := 32, refinedA := 472392, refinedB := 58,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true },
    { phase := "5|1|3", dst := "1|1|0", step := 10,
      word := [1, 1, 2, 1, 1, 1, 2, 3, 2, 1], sampleCount := 64,
      q := 32768, r := 32, a := 59049, b := 58,
      dstV2 := 1, dstOdd := 1, dstH := 0,
      stateModBits := 3, uResidueMod := 8, uResidue := 0,
      refinedQ := 262144, refinedR := 32, refinedA := 472392, refinedB := 58,
      formulaFailures := 0, deltaFailures := 0,
      refinedFormulaFailures := 0, refinedStateFailures := 0, exactOnSamples := true }
  ]

/-- Total sampled branch rows imported from script 126. -/
def a0ReturnBranchesV2Lt8RowCount : Nat :=
  16

/-- Sum of sampled formula/delta failure counters in the imported rows. -/
def a0ReturnBranchesV2Lt8FailureTotal : Nat :=
  a0ReturnBranchesV2Lt8.foldl
    (fun acc br =>
      acc + br.formulaFailures + br.deltaFailures
        + br.refinedFormulaFailures + br.refinedStateFailures
        + if br.exactOnSamples then 0 else 1)
    0

/--
Internal consistency checks for the imported branch rows:

* the valuation word length equals the observed return step;
* the target slope equals `3^step`;
* the source denominator/residue modulus equals `2^(sum word)`.
* the destination-refined progression is the expected residue
  subprogression of the valuation-word branch.

These are arithmetic checks on the imported rows, not a proof that the
same branch persists outside the sampled points.
-/
def a0ReturnBranchesV2Lt8ScaleFailureTotal : Nat :=
  a0ReturnBranchesV2Lt8.foldl
    (fun acc br =>
      acc
        + (if br.word.length = br.step then 0 else 1)
        + (if br.a = 3 ^ br.step then 0 else 1)
        + (if br.q = 2 ^ br.word.sum then 0 else 1)
        + (if br.stateModBits = br.dstV2 + 2 then 0 else 1)
        + (if br.uResidueMod = 2 ^ br.stateModBits then 0 else 1)
        + (if br.refinedQ = br.q * br.uResidueMod then 0 else 1)
        + (if br.refinedR = br.q * br.uResidue + br.r then 0 else 1)
        + (if br.refinedA = br.a * br.uResidueMod then 0 else 1)
        + (if br.refinedB = br.a * br.uResidue + br.b then 0 else 1))
    0

theorem a0ReturnBranchesV2Lt8_length :
    a0ReturnBranchesV2Lt8.length = a0ReturnBranchesV2Lt8RowCount := by
  norm_num [a0ReturnBranchesV2Lt8, a0ReturnBranchesV2Lt8RowCount]

theorem a0ReturnBranchesV2Lt8_sample_checks_zero :
    a0ReturnBranchesV2Lt8FailureTotal = 0 := by
  norm_num [a0ReturnBranchesV2Lt8FailureTotal, a0ReturnBranchesV2Lt8]

theorem a0ReturnBranchesV2Lt8_scale_checks_zero :
    a0ReturnBranchesV2Lt8ScaleFailureTotal = 0 := by
  norm_num [a0ReturnBranchesV2Lt8ScaleFailureTotal, a0ReturnBranchesV2Lt8]

/--
Exact word-cylinder arithmetic for the distinct sampled `v2 < 8` return
words in script 126.

`wordResidue mod 2^wordModBits` is the exact odd-source cylinder for the
valuation word.  In the A0 coordinate `n = targetResidue + 2^8*t`, this
induces `t = tWordResidue mod 2^tWordModBits`.  The listed branch
progression `t = q*u+r` implies that congruence.

This table does not prove that the branch is the first return; it only
certifies the valuation-word cylinder, the source split arithmetic, and
the affine no-drop prefix check for the listed branch shapes.
-/
structure A0WordCylinder where
  word : List Nat
  q : Nat
  r : Nat
  wordModBits : Nat
  wordResidue : Nat
  tWordModBits : Nat
  tWordResidue : Nat
  wordCongruenceFailures : Nat
  dropAffineFailures : Nat
  branchImpliesWordCongruence : Bool
  noDropCertificateRows : Nat
  arithmeticCertificateRows : Nat
  deriving Repr, DecidableEq

def a0WordCylindersV2Lt8 : List A0WordCylinder :=
  [
    { word := [1, 1, 2, 1, 1, 1], q := 128, r := 3,
      wordModBits := 8, wordResidue := 103,
      tWordModBits := 0, tWordResidue := 0,
      wordCongruenceFailures := 0, dropAffineFailures := 0,
      branchImpliesWordCongruence := true, noDropCertificateRows := 4,
      arithmeticCertificateRows := 4 },
    { word := [1, 1, 2, 1], q := 32, r := 12,
      wordModBits := 6, wordResidue := 39,
      tWordModBits := 0, tWordResidue := 0,
      wordCongruenceFailures := 0, dropAffineFailures := 0,
      branchImpliesWordCongruence := true, noDropCertificateRows := 4,
      arithmeticCertificateRows := 4 },
    { word := [1, 1, 2, 1, 1, 1, 2, 2, 1], q := 4096, r := 8,
      wordModBits := 13, wordResidue := 2151,
      tWordModBits := 5, tWordResidue := 8,
      wordCongruenceFailures := 0, dropAffineFailures := 0,
      branchImpliesWordCongruence := true, noDropCertificateRows := 4,
      arithmeticCertificateRows := 4 },
    { word := [1, 1, 2, 1, 1, 1, 2, 3, 2, 1], q := 32768, r := 32,
      wordModBits := 16, wordResidue := 8295,
      tWordModBits := 8, tWordResidue := 32,
      wordCongruenceFailures := 0, dropAffineFailures := 0,
      branchImpliesWordCongruence := true, noDropCertificateRows := 4,
      arithmeticCertificateRows := 4 }
  ]

def a0WordCylindersV2Lt8FailureTotal : Nat :=
  a0WordCylindersV2Lt8.foldl
    (fun acc row =>
      acc
        + row.wordCongruenceFailures
        + row.dropAffineFailures
        + (if row.branchImpliesWordCongruence then 0 else 1)
        + (if row.noDropCertificateRows = row.arithmeticCertificateRows then 0 else 1)
        + (if row.wordModBits = row.word.sum + 1 then 0 else 1)
        + (if row.q = 2 ^ row.word.sum then 0 else 1)
        + (if row.q % (2 ^ row.tWordModBits) = 0 then 0 else 1)
        + (if row.r % (2 ^ row.tWordModBits) = row.tWordResidue then 0 else 1))
    0

def a0WordCylindersV2Lt8ArithmeticRows : Nat :=
  a0WordCylindersV2Lt8.foldl
    (fun acc row => acc + row.arithmeticCertificateRows)
    0

theorem a0WordCylindersV2Lt8_failure_total_zero :
    a0WordCylindersV2Lt8FailureTotal = 0 := by
  norm_num [a0WordCylindersV2Lt8FailureTotal, a0WordCylindersV2Lt8]

theorem a0WordCylindersV2Lt8_arithmetic_rows :
    a0WordCylindersV2Lt8ArithmeticRows = a0ReturnBranchesV2Lt8RowCount := by
  norm_num [a0WordCylindersV2Lt8ArithmeticRows, a0WordCylindersV2Lt8,
    a0ReturnBranchesV2Lt8RowCount]

/-- Summary of a complete finite dyadic-prefix script-126 run. -/
structure A0PrefixBranchSummary where
  prefixBits : Nat
  totalSamples : Nat
  returnSamples : Nat
  dropSamples : Nat
  valuationTailSamples : Nat
  stepTailSamples : Nat
  branchRows : Nat
  branchSampleCountTotal : Nat
  branchSampleCountCoverageFailures : Nat
  exactFailures : Nat
  nonintegerBranches : Nat
  wordCongruenceFailures : Nat
  dropAffineFailures : Nat
  noDropCertificateRows : Nat
  branchWordCertificateFailures : Nat
  arithmeticCertificateRows : Nat
  refinedFormulaFailures : Nat
  refinedStateFailures : Nat
  labelPrefixIntegralityFailures : Nat
  labelIntermediateVisibleFailures : Nat
  labelIntermediateTargetVisibleFailures : Nat
  labelIntermediateCompetingVisibleFailures : Nat
  labelIntermediateTargetVisiblePrefixes : Nat
  labelIntermediateCompetingVisiblePrefixes : Nat
  labelIntermediateVisibleK10C1Failures : Nat
  labelIntermediateVisibleK11C1Failures : Nat
  labelIntermediateVisibleK12C1Failures : Nat
  labelIntermediateVisibleK12C2Failures : Nat
  labelIntermediateVisibleK20C1Failures : Nat
  labelIntermediateProbeTotal : Nat
  labelIntermediateProbeCandidateSelected : Nat
  labelIntermediateProbeTargetSelected : Nat
  labelIntermediateProbeCompetingSelected : Nat
  labelIntermediateProbeNoneSelected : Nat
  labelIntermediateProbeSameStepReturn : Nat
  labelIntermediateProbeEarlyTargetReturn : Nat
  labelIntermediateProbeNoReturnByFinal : Nat
  labelIntermediateProbeTerminalByFinal : Nat
  labelIntermediateMultiprobeTotal : Nat
  labelIntermediateMultiprobeSameStepReturn : Nat
  labelIntermediateMultiprobeEarlyTargetReturn : Nat
  labelIntermediateMultiprobeNoReturnByFinal : Nat
  labelIntermediateMultiprobeTerminalByFinal : Nat
  labelIntermediateTargetMultiprobeTotal : Nat
  labelIntermediateTargetMultiprobeSameStepReturn : Nat
  labelIntermediateTargetMultiprobeEarlyTargetReturn : Nat
  labelIntermediateTargetMultiprobeNoReturnByFinal : Nat
  labelIntermediateTargetMultiprobeTerminalByFinal : Nat
  labelIntermediateMultiprobeNoReturnK10C1 : Nat
  labelIntermediateMultiprobeNoReturnK11C1 : Nat
  labelIntermediateMultiprobeNoReturnK12C1 : Nat
  labelIntermediateMultiprobeNoReturnK12C2 : Nat
  labelIntermediateMultiprobeNoReturnK20C1 : Nat
  labelIntermediateMultiprobeNoReturnExtendedLaterTarget : Nat
  labelIntermediateMultiprobeNoReturnExtendedTerminal : Nat
  labelIntermediateMultiprobeNoReturnExtendedUnresolved : Nat
  labelIntermediateMultiprobeNoReturnLaterTargetMinDelta : Nat
  labelIntermediateMultiprobeNoReturnLaterTargetMaxDelta : Nat
  labelIntermediateMultiprobeNoReturnContinuationSupported : Nat
  labelIntermediateMultiprobeNoReturnContinuationIntegralityFailures : Nat
  labelIntermediateMultiprobeNoReturnContinuationNoDropFailures : Nat
  labelIntermediateMultiprobeNoReturnActualPrefixMatches : Nat
  labelIntermediateMultiprobeNoReturnActualSuffixTargetWordMatches : Nat
  labelIntermediateMultiprobeNoReturnActualContinuationSupported : Nat
  labelIntermediateMultiprobeNoReturnActualContinuationIntegralityFailures : Nat
  labelIntermediateMultiprobeNoReturnActualContinuationNoDropFailures : Nat
  labelIntermediateMultiprobeNoReturnActualRefinedContinuationSupported : Nat
  labelIntermediateMultiprobeNoReturnActualRefinedContinuationFailures : Nat
  labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMin : Nat
  labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMax : Nat
  labelIntermediateCompetingNoLaterTargetIntersections : Nat
  labelIntermediateCompetingLaterTargetIntersections : Nat
  labelIntermediateTargetPersistentVisibility : Nat
  labelIntermediateTargetMissingPriorVisibility : Nat
  labelIntermediateTargetNoPriorCompetingIntersections : Nat
  labelIntermediateTargetPriorCompetingIntersections : Nat
  labelIntermediateTargetHighLiftCovered : Nat
  labelIntermediateTargetLowOnlyVisible : Nat
  labelFinalTargetLowFailures : Nat
  labelFinalTargetHighLiftFailures : Nat
  labelFinalTargetHighLiftMinModBits : Nat
  labelFinalTargetHighLiftMaxModBits : Nat
  labelFinalCompetingFailures : Nat
  labelSplitResolutionCertificate : Nat
  labelStatusProvedConstantTargetB1 : Nat
  labelStatusTargetHighLiftBoundary : Nat
  labelStatusBlockedLabelCongruence : Nat
  labelStatusBlockedPrefixIntegrality : Nat
  highLiftContinuationSupportedRows : Nat
  highLiftContinuationStepDeltaMin : Nat
  highLiftContinuationStepDeltaMax : Nat
  highLiftContinuationIntegralityFailures : Nat
  highLiftContinuationNoDropFailures : Nat
  deriving Repr, DecidableEq

/--
Complete finite-prefix branch extraction summaries for `v2 < 8`,
odd residues `{1,3}`, and `h < 4`.

These are finite-prefix enumerations only.  They do not assert an
infinite residue-class partition.
-/
def a0CompletePrefixSummariesV2Lt8 : List A0PrefixBranchSummary :=
  [
    { prefixBits := 12, totalSamples := 16320, returnSamples := 1652,
      dropSamples := 14548, valuationTailSamples := 120, stepTailSamples := 0,
      branchRows := 860, branchSampleCountTotal := 1652,
      branchSampleCountCoverageFailures := 0,
      exactFailures := 0, nonintegerBranches := 0,
      wordCongruenceFailures := 0, dropAffineFailures := 0,
      noDropCertificateRows := 860, branchWordCertificateFailures := 0,
      arithmeticCertificateRows := 860,
      refinedFormulaFailures := 0, refinedStateFailures := 0,
      labelPrefixIntegralityFailures := 0,
      labelIntermediateVisibleFailures := 216,
      labelIntermediateTargetVisibleFailures := 12,
      labelIntermediateCompetingVisibleFailures := 204,
      labelIntermediateTargetVisiblePrefixes := 12,
      labelIntermediateCompetingVisiblePrefixes := 204,
      labelIntermediateVisibleK10C1Failures := 0,
      labelIntermediateVisibleK11C1Failures := 156,
      labelIntermediateVisibleK12C1Failures := 48,
      labelIntermediateVisibleK12C2Failures := 12,
      labelIntermediateVisibleK20C1Failures := 0,
      labelIntermediateProbeTotal := 216,
      labelIntermediateProbeCandidateSelected := 216,
      labelIntermediateProbeTargetSelected := 12,
      labelIntermediateProbeCompetingSelected := 204,
      labelIntermediateProbeNoneSelected := 0,
      labelIntermediateProbeSameStepReturn := 216,
      labelIntermediateProbeEarlyTargetReturn := 0,
      labelIntermediateProbeNoReturnByFinal := 0,
      labelIntermediateProbeTerminalByFinal := 0,
      labelIntermediateMultiprobeTotal := 1728,
      labelIntermediateMultiprobeSameStepReturn := 1728,
      labelIntermediateMultiprobeEarlyTargetReturn := 0,
      labelIntermediateMultiprobeNoReturnByFinal := 0,
      labelIntermediateMultiprobeTerminalByFinal := 0,
      labelIntermediateTargetMultiprobeTotal := 96,
      labelIntermediateTargetMultiprobeSameStepReturn := 96,
      labelIntermediateTargetMultiprobeEarlyTargetReturn := 0,
      labelIntermediateTargetMultiprobeNoReturnByFinal := 0,
      labelIntermediateTargetMultiprobeTerminalByFinal := 0,
      labelIntermediateMultiprobeNoReturnK10C1 := 0,
      labelIntermediateMultiprobeNoReturnK11C1 := 0,
      labelIntermediateMultiprobeNoReturnK12C1 := 0,
      labelIntermediateMultiprobeNoReturnK12C2 := 0,
      labelIntermediateMultiprobeNoReturnK20C1 := 0,
      labelIntermediateMultiprobeNoReturnExtendedLaterTarget := 0,
      labelIntermediateMultiprobeNoReturnExtendedTerminal := 0,
      labelIntermediateMultiprobeNoReturnExtendedUnresolved := 0,
      labelIntermediateMultiprobeNoReturnLaterTargetMinDelta := 0,
      labelIntermediateMultiprobeNoReturnLaterTargetMaxDelta := 0,
      labelIntermediateMultiprobeNoReturnContinuationSupported := 0,
      labelIntermediateMultiprobeNoReturnContinuationIntegralityFailures := 0,
      labelIntermediateMultiprobeNoReturnContinuationNoDropFailures := 0,
      labelIntermediateMultiprobeNoReturnActualPrefixMatches := 0,
      labelIntermediateMultiprobeNoReturnActualSuffixTargetWordMatches := 0,
      labelIntermediateMultiprobeNoReturnActualContinuationSupported := 0,
      labelIntermediateMultiprobeNoReturnActualContinuationIntegralityFailures := 0,
      labelIntermediateMultiprobeNoReturnActualContinuationNoDropFailures := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedContinuationSupported := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedContinuationFailures := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMin := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMax := 0,
      labelIntermediateCompetingNoLaterTargetIntersections := 204,
      labelIntermediateCompetingLaterTargetIntersections := 0,
      labelIntermediateTargetPersistentVisibility := 0,
      labelIntermediateTargetMissingPriorVisibility := 12,
      labelIntermediateTargetNoPriorCompetingIntersections := 12,
      labelIntermediateTargetPriorCompetingIntersections := 0,
      labelIntermediateTargetHighLiftCovered := 12,
      labelIntermediateTargetLowOnlyVisible := 0,
      labelFinalTargetLowFailures := 0,
      labelFinalTargetHighLiftFailures := 860,
      labelFinalTargetHighLiftMinModBits := 7,
      labelFinalTargetHighLiftMaxModBits := 7,
      labelFinalCompetingFailures := 0,
      labelSplitResolutionCertificate := 860,
      labelStatusProvedConstantTargetB1 := 0,
      labelStatusTargetHighLiftBoundary := 656,
      labelStatusBlockedLabelCongruence := 204,
      labelStatusBlockedPrefixIntegrality := 0,
      highLiftContinuationSupportedRows := 860,
      highLiftContinuationStepDeltaMin := 6,
      highLiftContinuationStepDeltaMax := 6,
      highLiftContinuationIntegralityFailures := 0,
      highLiftContinuationNoDropFailures := 0 },
    { prefixBits := 13, totalSamples := 32640, returnSamples := 3352,
      dropSamples := 29040, valuationTailSamples := 240, stepTailSamples := 8,
      branchRows := 1564, branchSampleCountTotal := 3352,
      branchSampleCountCoverageFailures := 0,
      exactFailures := 0, nonintegerBranches := 0,
      wordCongruenceFailures := 0, dropAffineFailures := 0,
      noDropCertificateRows := 1564, branchWordCertificateFailures := 0,
      arithmeticCertificateRows := 1564,
      refinedFormulaFailures := 0, refinedStateFailures := 0,
      labelPrefixIntegralityFailures := 0,
      labelIntermediateVisibleFailures := 376,
      labelIntermediateTargetVisibleFailures := 16,
      labelIntermediateCompetingVisibleFailures := 360,
      labelIntermediateTargetVisiblePrefixes := 16,
      labelIntermediateCompetingVisiblePrefixes := 360,
      labelIntermediateVisibleK10C1Failures := 0,
      labelIntermediateVisibleK11C1Failures := 268,
      labelIntermediateVisibleK12C1Failures := 92,
      labelIntermediateVisibleK12C2Failures := 16,
      labelIntermediateVisibleK20C1Failures := 0,
      labelIntermediateProbeTotal := 376,
      labelIntermediateProbeCandidateSelected := 376,
      labelIntermediateProbeTargetSelected := 16,
      labelIntermediateProbeCompetingSelected := 360,
      labelIntermediateProbeNoneSelected := 0,
      labelIntermediateProbeSameStepReturn := 376,
      labelIntermediateProbeEarlyTargetReturn := 0,
      labelIntermediateProbeNoReturnByFinal := 0,
      labelIntermediateProbeTerminalByFinal := 0,
      labelIntermediateMultiprobeTotal := 3008,
      labelIntermediateMultiprobeSameStepReturn := 3008,
      labelIntermediateMultiprobeEarlyTargetReturn := 0,
      labelIntermediateMultiprobeNoReturnByFinal := 0,
      labelIntermediateMultiprobeTerminalByFinal := 0,
      labelIntermediateTargetMultiprobeTotal := 128,
      labelIntermediateTargetMultiprobeSameStepReturn := 128,
      labelIntermediateTargetMultiprobeEarlyTargetReturn := 0,
      labelIntermediateTargetMultiprobeNoReturnByFinal := 0,
      labelIntermediateTargetMultiprobeTerminalByFinal := 0,
      labelIntermediateMultiprobeNoReturnK10C1 := 0,
      labelIntermediateMultiprobeNoReturnK11C1 := 0,
      labelIntermediateMultiprobeNoReturnK12C1 := 0,
      labelIntermediateMultiprobeNoReturnK12C2 := 0,
      labelIntermediateMultiprobeNoReturnK20C1 := 0,
      labelIntermediateMultiprobeNoReturnExtendedLaterTarget := 0,
      labelIntermediateMultiprobeNoReturnExtendedTerminal := 0,
      labelIntermediateMultiprobeNoReturnExtendedUnresolved := 0,
      labelIntermediateMultiprobeNoReturnLaterTargetMinDelta := 0,
      labelIntermediateMultiprobeNoReturnLaterTargetMaxDelta := 0,
      labelIntermediateMultiprobeNoReturnContinuationSupported := 0,
      labelIntermediateMultiprobeNoReturnContinuationIntegralityFailures := 0,
      labelIntermediateMultiprobeNoReturnContinuationNoDropFailures := 0,
      labelIntermediateMultiprobeNoReturnActualPrefixMatches := 0,
      labelIntermediateMultiprobeNoReturnActualSuffixTargetWordMatches := 0,
      labelIntermediateMultiprobeNoReturnActualContinuationSupported := 0,
      labelIntermediateMultiprobeNoReturnActualContinuationIntegralityFailures := 0,
      labelIntermediateMultiprobeNoReturnActualContinuationNoDropFailures := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedContinuationSupported := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedContinuationFailures := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMin := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMax := 0,
      labelIntermediateCompetingNoLaterTargetIntersections := 360,
      labelIntermediateCompetingLaterTargetIntersections := 0,
      labelIntermediateTargetPersistentVisibility := 0,
      labelIntermediateTargetMissingPriorVisibility := 16,
      labelIntermediateTargetNoPriorCompetingIntersections := 16,
      labelIntermediateTargetPriorCompetingIntersections := 0,
      labelIntermediateTargetHighLiftCovered := 16,
      labelIntermediateTargetLowOnlyVisible := 0,
      labelFinalTargetLowFailures := 0,
      labelFinalTargetHighLiftFailures := 1564,
      labelFinalTargetHighLiftMinModBits := 7,
      labelFinalTargetHighLiftMaxModBits := 7,
      labelFinalCompetingFailures := 0,
      labelSplitResolutionCertificate := 1564,
      labelStatusProvedConstantTargetB1 := 0,
      labelStatusTargetHighLiftBoundary := 1212,
      labelStatusBlockedLabelCongruence := 352,
      labelStatusBlockedPrefixIntegrality := 0,
      highLiftContinuationSupportedRows := 1564,
      highLiftContinuationStepDeltaMin := 6,
      highLiftContinuationStepDeltaMax := 6,
      highLiftContinuationIntegralityFailures := 0,
      highLiftContinuationNoDropFailures := 0 },
    { prefixBits := 14, totalSamples := 65280, returnSamples := 6748,
      dropSamples := 58040, valuationTailSamples := 484, stepTailSamples := 8,
      branchRows := 2868, branchSampleCountTotal := 6748,
      branchSampleCountCoverageFailures := 0,
      exactFailures := 0, nonintegerBranches := 0,
      wordCongruenceFailures := 0, dropAffineFailures := 0,
      noDropCertificateRows := 2868, branchWordCertificateFailures := 0,
      arithmeticCertificateRows := 2868,
      refinedFormulaFailures := 0, refinedStateFailures := 0,
      labelPrefixIntegralityFailures := 0,
      labelIntermediateVisibleFailures := 744,
      labelIntermediateTargetVisibleFailures := 64,
      labelIntermediateCompetingVisibleFailures := 680,
      labelIntermediateTargetVisiblePrefixes := 64,
      labelIntermediateCompetingVisiblePrefixes := 680,
      labelIntermediateVisibleK10C1Failures := 8,
      labelIntermediateVisibleK11C1Failures := 472,
      labelIntermediateVisibleK12C1Failures := 200,
      labelIntermediateVisibleK12C2Failures := 64,
      labelIntermediateVisibleK20C1Failures := 0,
      labelIntermediateProbeTotal := 744,
      labelIntermediateProbeCandidateSelected := 744,
      labelIntermediateProbeTargetSelected := 64,
      labelIntermediateProbeCompetingSelected := 680,
      labelIntermediateProbeNoneSelected := 0,
      labelIntermediateProbeSameStepReturn := 744,
      labelIntermediateProbeEarlyTargetReturn := 0,
      labelIntermediateProbeNoReturnByFinal := 0,
      labelIntermediateProbeTerminalByFinal := 0,
      labelIntermediateMultiprobeTotal := 5952,
      labelIntermediateMultiprobeSameStepReturn := 5944,
      labelIntermediateMultiprobeEarlyTargetReturn := 0,
      labelIntermediateMultiprobeNoReturnByFinal := 8,
      labelIntermediateMultiprobeTerminalByFinal := 0,
      labelIntermediateTargetMultiprobeTotal := 512,
      labelIntermediateTargetMultiprobeSameStepReturn := 512,
      labelIntermediateTargetMultiprobeEarlyTargetReturn := 0,
      labelIntermediateTargetMultiprobeNoReturnByFinal := 0,
      labelIntermediateTargetMultiprobeTerminalByFinal := 0,
      labelIntermediateMultiprobeNoReturnK10C1 := 0,
      labelIntermediateMultiprobeNoReturnK11C1 := 0,
      labelIntermediateMultiprobeNoReturnK12C1 := 8,
      labelIntermediateMultiprobeNoReturnK12C2 := 0,
      labelIntermediateMultiprobeNoReturnK20C1 := 0,
      labelIntermediateMultiprobeNoReturnExtendedLaterTarget := 8,
      labelIntermediateMultiprobeNoReturnExtendedTerminal := 0,
      labelIntermediateMultiprobeNoReturnExtendedUnresolved := 0,
      labelIntermediateMultiprobeNoReturnLaterTargetMinDelta := 6,
      labelIntermediateMultiprobeNoReturnLaterTargetMaxDelta := 6,
      labelIntermediateMultiprobeNoReturnContinuationSupported := 0,
      labelIntermediateMultiprobeNoReturnContinuationIntegralityFailures := 8,
      labelIntermediateMultiprobeNoReturnContinuationNoDropFailures := 0,
      labelIntermediateMultiprobeNoReturnActualPrefixMatches := 8,
      labelIntermediateMultiprobeNoReturnActualSuffixTargetWordMatches := 8,
      labelIntermediateMultiprobeNoReturnActualContinuationSupported := 0,
      labelIntermediateMultiprobeNoReturnActualContinuationIntegralityFailures := 8,
      labelIntermediateMultiprobeNoReturnActualContinuationNoDropFailures := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedContinuationSupported := 8,
      labelIntermediateMultiprobeNoReturnActualRefinedContinuationFailures := 0,
      labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMin := 4,
      labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMax := 4,
      labelIntermediateCompetingNoLaterTargetIntersections := 680,
      labelIntermediateCompetingLaterTargetIntersections := 0,
      labelIntermediateTargetPersistentVisibility := 0,
      labelIntermediateTargetMissingPriorVisibility := 64,
      labelIntermediateTargetNoPriorCompetingIntersections := 64,
      labelIntermediateTargetPriorCompetingIntersections := 0,
      labelIntermediateTargetHighLiftCovered := 64,
      labelIntermediateTargetLowOnlyVisible := 0,
      labelFinalTargetLowFailures := 0,
      labelFinalTargetHighLiftFailures := 2868,
      labelFinalTargetHighLiftMinModBits := 7,
      labelFinalTargetHighLiftMaxModBits := 7,
      labelFinalCompetingFailures := 0,
      labelSplitResolutionCertificate := 2868,
      labelStatusProvedConstantTargetB1 := 0,
      labelStatusTargetHighLiftBoundary := 2176,
      labelStatusBlockedLabelCongruence := 692,
      labelStatusBlockedPrefixIntegrality := 0,
      highLiftContinuationSupportedRows := 2868,
      highLiftContinuationStepDeltaMin := 6,
      highLiftContinuationStepDeltaMax := 6,
      highLiftContinuationIntegralityFailures := 0,
      highLiftContinuationNoDropFailures := 0 }
  ]

/-- Total failure counters across the imported complete-prefix summaries. -/
def a0CompletePrefixSummariesV2Lt8FailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc + row.exactFailures + row.nonintegerBranches
        + row.wordCongruenceFailures + row.dropAffineFailures
        + row.branchWordCertificateFailures
        + row.refinedFormulaFailures + row.refinedStateFailures
        + row.labelPrefixIntegralityFailures
        + row.labelFinalTargetLowFailures
        + row.labelFinalCompetingFailures
        + row.highLiftContinuationIntegralityFailures
        + row.highLiftContinuationNoDropFailures)
    0

/--
Open label-gate congruence counts.

These are not arithmetic failures.  `labelIntermediateVisibleFailures`
counts congruence classes on which an intermediate prefix may acquire a
phantom label and must be split or controlled.  `labelFinalTargetHighLiftFailures`
counts congruence classes on which the final target can lift from
`b = 1` to `b >= 2`.
-/
def a0CompletePrefixSummariesV2Lt8LabelOpenTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc + row.labelIntermediateVisibleFailures
        + row.labelFinalTargetHighLiftFailures)
    0

def a0CompletePrefixSummariesV2Lt8LabelStatusCoverageFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc +
        if row.labelStatusProvedConstantTargetB1
            + row.labelStatusTargetHighLiftBoundary
            + row.labelStatusBlockedLabelCongruence
            + row.labelStatusBlockedPrefixIntegrality
          = row.branchRows then 0 else 1)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetVisibleTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateTargetVisibleFailures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateCompetingVisibleTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateCompetingVisibleFailures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateSplitFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + (if row.labelIntermediateTargetVisibleFailures
              + row.labelIntermediateCompetingVisibleFailures
            = row.labelIntermediateVisibleFailures then 0 else 1)
        + (if row.labelIntermediateTargetVisiblePrefixes
              + row.labelIntermediateCompetingVisiblePrefixes
            = row.labelIntermediateVisibleFailures then 0 else 1))
    0

def a0CompletePrefixSummariesV2Lt8IntermediateK10C1VisibleTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateVisibleK10C1Failures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateK11C1VisibleTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateVisibleK11C1Failures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateK12C1VisibleTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateVisibleK12C1Failures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateK12C2VisibleTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateVisibleK12C2Failures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateK20C1VisibleTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateVisibleK20C1Failures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateRecordSplitFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc +
        if row.labelIntermediateVisibleK10C1Failures
            + row.labelIntermediateVisibleK11C1Failures
            + row.labelIntermediateVisibleK12C1Failures
            + row.labelIntermediateVisibleK12C2Failures
            + row.labelIntermediateVisibleK20C1Failures
          = row.labelIntermediateVisibleFailures then 0 else 1)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateProbeTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateProbeTotal)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateProbeFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + (if row.labelIntermediateProbeTotal
            = row.labelIntermediateVisibleFailures then 0 else 1)
        + (if row.labelIntermediateProbeCandidateSelected
            = row.labelIntermediateProbeTotal then 0 else 1)
        + (if row.labelIntermediateProbeTargetSelected
              + row.labelIntermediateProbeCompetingSelected
              + row.labelIntermediateProbeNoneSelected
            = row.labelIntermediateProbeTotal then 0 else 1)
        + (if row.labelIntermediateProbeSameStepReturn
              + row.labelIntermediateProbeEarlyTargetReturn
              + row.labelIntermediateProbeNoReturnByFinal
              + row.labelIntermediateProbeTerminalByFinal
            = row.labelIntermediateProbeTotal then 0 else 1)
        + row.labelIntermediateProbeEarlyTargetReturn
        + row.labelIntermediateProbeNoReturnByFinal
        + row.labelIntermediateProbeTerminalByFinal)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateCompetingNoLaterTargetTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateCompetingNoLaterTargetIntersections)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateMultiprobeTotal)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeEarlyTargetTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateMultiprobeEarlyTargetReturn)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnByFinalTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateMultiprobeNoReturnByFinal)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnK12C1Total : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateMultiprobeNoReturnK12C1)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnExtendedLaterTargetTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateMultiprobeNoReturnExtendedLaterTarget)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnExtendedFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + (if row.labelIntermediateMultiprobeNoReturnK10C1 = 0 then 0 else 1)
        + (if row.labelIntermediateMultiprobeNoReturnK11C1 = 0 then 0 else 1)
        + (if row.labelIntermediateMultiprobeNoReturnK12C2 = 0 then 0 else 1)
        + (if row.labelIntermediateMultiprobeNoReturnK20C1 = 0 then 0 else 1)
        + (if row.labelIntermediateMultiprobeNoReturnK12C1
            = row.labelIntermediateMultiprobeNoReturnByFinal then 0 else 1)
        + (if row.labelIntermediateMultiprobeNoReturnExtendedLaterTarget
            = row.labelIntermediateMultiprobeNoReturnByFinal then 0 else 1)
        + row.labelIntermediateMultiprobeNoReturnExtendedTerminal
        + row.labelIntermediateMultiprobeNoReturnExtendedUnresolved
        + (if row.labelIntermediateMultiprobeNoReturnByFinal = 0 then 0
          else
            (if row.labelIntermediateMultiprobeNoReturnLaterTargetMinDelta = 6
              then 0 else 1)
            + (if row.labelIntermediateMultiprobeNoReturnLaterTargetMaxDelta = 6
              then 0 else 1)))
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnContinuationIntegralityFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc
      + row.labelIntermediateMultiprobeNoReturnContinuationIntegralityFailures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualPrefixMatchTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc
      + row.labelIntermediateMultiprobeNoReturnActualPrefixMatches)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualSuffixTargetWordMatchTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc
      + row.labelIntermediateMultiprobeNoReturnActualSuffixTargetWordMatches)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualContinuationIntegralityFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc
      + row.labelIntermediateMultiprobeNoReturnActualContinuationIntegralityFailures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualRefinedSupportedTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc
      + row.labelIntermediateMultiprobeNoReturnActualRefinedContinuationSupported)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualRefinedFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc
      + row.labelIntermediateMultiprobeNoReturnActualRefinedContinuationFailures)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualRefinedCheckFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + (if row.labelIntermediateMultiprobeNoReturnActualPrefixMatches
            = row.labelIntermediateMultiprobeNoReturnByFinal then 0 else 1)
        + (if row.labelIntermediateMultiprobeNoReturnActualSuffixTargetWordMatches
            = row.labelIntermediateMultiprobeNoReturnByFinal then 0 else 1)
        + (if row.labelIntermediateMultiprobeNoReturnActualRefinedContinuationSupported
            = row.labelIntermediateMultiprobeNoReturnByFinal then 0 else 1)
        + row.labelIntermediateMultiprobeNoReturnActualRefinedContinuationFailures
        + row.labelIntermediateMultiprobeNoReturnContinuationNoDropFailures
        + row.labelIntermediateMultiprobeNoReturnActualContinuationNoDropFailures
        + (if row.labelIntermediateMultiprobeNoReturnByFinal = 0 then 0
          else
            (if row.labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMin = 4
              then 0 else 1)
            + (if row.labelIntermediateMultiprobeNoReturnActualRefinedExtraBitsMax = 4
              then 0 else 1)))
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetMultiprobeTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateTargetMultiprobeTotal)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetMultiprobeFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + (if row.labelIntermediateTargetMultiprobeTotal
            = 8 * row.labelIntermediateTargetVisibleFailures then 0 else 1)
        + (if row.labelIntermediateTargetMultiprobeSameStepReturn
            = row.labelIntermediateTargetMultiprobeTotal then 0 else 1)
        + row.labelIntermediateTargetMultiprobeEarlyTargetReturn
        + row.labelIntermediateTargetMultiprobeNoReturnByFinal
        + row.labelIntermediateTargetMultiprobeTerminalByFinal)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateCompetingLaterTargetTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateCompetingLaterTargetIntersections)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateCompetingLaterTargetFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + (if row.labelIntermediateCompetingNoLaterTargetIntersections
              + row.labelIntermediateCompetingLaterTargetIntersections
            = row.labelIntermediateCompetingVisibleFailures then 0 else 1)
        + row.labelIntermediateCompetingLaterTargetIntersections)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetPersistentVisibilityTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateTargetPersistentVisibility)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetMissingPriorVisibilityTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateTargetMissingPriorVisibility)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetNoPriorCompetingIntersectionTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateTargetNoPriorCompetingIntersections)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetPriorCompetingIntersectionTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateTargetPriorCompetingIntersections)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetHighLiftCoveredTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateTargetHighLiftCovered)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetLowOnlyVisibleTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelIntermediateTargetLowOnlyVisible)
    0

def a0CompletePrefixSummariesV2Lt8IntermediateTargetVisibilityStructureFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + row.labelIntermediateTargetPersistentVisibility
        + (if row.labelIntermediateTargetMissingPriorVisibility
            = row.labelIntermediateTargetVisibleFailures then 0 else 1)
        + (if row.labelIntermediateTargetNoPriorCompetingIntersections
            = row.labelIntermediateTargetVisibleFailures then 0 else 1)
        + row.labelIntermediateTargetPriorCompetingIntersections
        + (if row.labelIntermediateTargetHighLiftCovered
            = row.labelIntermediateTargetVisibleFailures then 0 else 1)
        + row.labelIntermediateTargetLowOnlyVisible)
    0

def a0CompletePrefixSummariesV2Lt8HighLiftModBitsFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + (if row.labelFinalTargetHighLiftMinModBits = 7 then 0 else 1)
        + (if row.labelFinalTargetHighLiftMaxModBits = 7 then 0 else 1))
    0

def a0CompletePrefixSummariesV2Lt8HighLiftContinuationFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + (if row.highLiftContinuationSupportedRows = row.branchRows then 0 else 1)
        + (if row.highLiftContinuationStepDeltaMin = 6 then 0 else 1)
        + (if row.highLiftContinuationStepDeltaMax = 6 then 0 else 1))
    0

def a0CompletePrefixSummariesV2Lt8LabelSplitResolutionCertificateTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.labelSplitResolutionCertificate)
    0

def a0CompletePrefixSummariesV2Lt8BranchRowsTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.branchRows)
    0

def a0CompletePrefixSummariesV2Lt8ReturnSamplesTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.returnSamples)
    0

def a0CompletePrefixSummariesV2Lt8TotalSamplesTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.totalSamples)
    0

def a0CompletePrefixSummariesV2Lt8DropSamplesTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.dropSamples)
    0

def a0CompletePrefixSummariesV2Lt8ValuationTailSamplesTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.valuationTailSamples)
    0

def a0CompletePrefixSummariesV2Lt8StepTailSamplesTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.stepTailSamples)
    0

def a0CompletePrefixSummariesV2Lt8BranchSampleCountTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row => acc + row.branchSampleCountTotal)
    0

def a0CompletePrefixSummariesV2Lt8BranchSampleCoverageFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + row.branchSampleCountCoverageFailures
        + (if row.branchSampleCountTotal = row.returnSamples then 0 else 1))
    0

noncomputable def a0CompletePrefixSummariesV2Lt8ReturnPartitionSummary :
    WeakBridge.LabelSplit.ReturnPartitionSummary :=
  { returnSamples := a0CompletePrefixSummariesV2Lt8ReturnSamplesTotal,
    coveredReturnSamples := a0CompletePrefixSummariesV2Lt8BranchSampleCountTotal,
    coverageFailures := a0CompletePrefixSummariesV2Lt8BranchSampleCoverageFailureTotal }

noncomputable def a0CompletePrefixSummariesV2Lt8ReturnPartitionSummaryFailure : Nat :=
  WeakBridge.LabelSplit.returnPartitionFailure
    a0CompletePrefixSummariesV2Lt8ReturnPartitionSummary

noncomputable def a0CompletePrefixSummariesV2Lt8OutcomeSummary :
    WeakBridge.LabelSplit.OutcomeSummary :=
  { totalSamples := a0CompletePrefixSummariesV2Lt8TotalSamplesTotal,
    returnSamples := a0CompletePrefixSummariesV2Lt8ReturnSamplesTotal,
    coveredReturnSamples := a0CompletePrefixSummariesV2Lt8BranchSampleCountTotal,
    dropSamples := a0CompletePrefixSummariesV2Lt8DropSamplesTotal,
    valuationTailSamples := a0CompletePrefixSummariesV2Lt8ValuationTailSamplesTotal,
    stepTailSamples := a0CompletePrefixSummariesV2Lt8StepTailSamplesTotal,
    returnCoverageFailures := a0CompletePrefixSummariesV2Lt8BranchSampleCoverageFailureTotal }

noncomputable def a0CompletePrefixSummariesV2Lt8OutcomeDecompositionFailure : Nat :=
  WeakBridge.LabelSplit.outcomeDecompositionFailure
    a0CompletePrefixSummariesV2Lt8OutcomeSummary

def a0CompletePrefixSummariesV2Lt8LabelSplitResolutionCertificateFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc
        + (if row.labelSplitResolutionCertificate = row.branchRows then 0 else 1))
    0

noncomputable def a0CompletePrefixSummariesV2Lt8LabelSplitSummary :
    WeakBridge.LabelSplit.SummaryCounters :=
  { branchRows := a0CompletePrefixSummariesV2Lt8BranchRowsTotal,
    certificateRows := a0CompletePrefixSummariesV2Lt8LabelSplitResolutionCertificateTotal }

noncomputable def a0CompletePrefixSummariesV2Lt8LabelSplitSummaryFailure : Nat :=
  WeakBridge.LabelSplit.summaryFailure
    a0CompletePrefixSummariesV2Lt8LabelSplitSummary

/-- The complete-prefix rows all carry script-126 arithmetic certificates. -/
def a0CompletePrefixSummariesV2Lt8ArithmeticCertificateFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc +
        (if row.arithmeticCertificateRows = row.branchRows then 0 else 1)
        + (if row.noDropCertificateRows = row.branchRows then 0 else 1))
    0

/-- The summary rows account for every enumerated source point. -/
def a0CompletePrefixSummariesV2Lt8CoverageFailureTotal : Nat :=
  a0CompletePrefixSummariesV2Lt8.foldl
    (fun acc row =>
      acc +
        if row.returnSamples + row.dropSamples
            + row.valuationTailSamples + row.stepTailSamples
          = row.totalSamples then 0 else 1)
    0

theorem a0CompletePrefixSummariesV2Lt8_failure_total_zero :
    a0CompletePrefixSummariesV2Lt8FailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8FailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_label_open_total :
    a0CompletePrefixSummariesV2Lt8LabelOpenTotal = 6628 := by
  norm_num [a0CompletePrefixSummariesV2Lt8LabelOpenTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_label_status_coverage_zero :
    a0CompletePrefixSummariesV2Lt8LabelStatusCoverageFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8LabelStatusCoverageFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_intermediate_visible_split :
    a0CompletePrefixSummariesV2Lt8IntermediateTargetVisibleTotal = 92
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateCompetingVisibleTotal = 1244
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateSplitFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8IntermediateTargetVisibleTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateCompetingVisibleTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateSplitFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_intermediate_visible_by_record :
    a0CompletePrefixSummariesV2Lt8IntermediateK10C1VisibleTotal = 8
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateK11C1VisibleTotal = 896
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateK12C1VisibleTotal = 340
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateK12C2VisibleTotal = 92
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateK20C1VisibleTotal = 0
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateRecordSplitFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8IntermediateK10C1VisibleTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateK11C1VisibleTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateK12C1VisibleTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateK12C2VisibleTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateK20C1VisibleTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateRecordSplitFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_intermediate_probe_same_step :
    a0CompletePrefixSummariesV2Lt8IntermediateProbeTotal = 1336
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateProbeFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8IntermediateProbeTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateProbeFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_intermediate_multiprobe_no_early :
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeTotal = 10688
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeEarlyTargetTotal = 0
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnByFinalTotal = 8 := by
  norm_num [a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeEarlyTargetTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnByFinalTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_intermediate_multiprobe_no_return_extended :
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnK12C1Total = 8
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnExtendedLaterTargetTotal = 8
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnExtendedFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnK12C1Total,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnExtendedLaterTargetTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnExtendedFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_intermediate_multiprobe_no_return_actual_refined :
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnContinuationIntegralityFailureTotal = 8
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualPrefixMatchTotal = 8
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualSuffixTargetWordMatchTotal = 8
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualContinuationIntegralityFailureTotal = 8
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualRefinedSupportedTotal = 8
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualRefinedFailureTotal = 0
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualRefinedCheckFailureTotal = 0 := by
  norm_num [
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnContinuationIntegralityFailureTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualPrefixMatchTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualSuffixTargetWordMatchTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualContinuationIntegralityFailureTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualRefinedSupportedTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualRefinedFailureTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateMultiprobeNoReturnActualRefinedCheckFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_intermediate_target_multiprobe_same_step :
    a0CompletePrefixSummariesV2Lt8IntermediateTargetMultiprobeTotal = 736
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateTargetMultiprobeFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8IntermediateTargetMultiprobeTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateTargetMultiprobeFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_intermediate_competing_no_later_target :
    a0CompletePrefixSummariesV2Lt8IntermediateCompetingNoLaterTargetTotal = 1244
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateCompetingLaterTargetTotal = 0
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateCompetingLaterTargetFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8IntermediateCompetingNoLaterTargetTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateCompetingLaterTargetTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateCompetingLaterTargetFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_intermediate_target_visibility_structure :
    a0CompletePrefixSummariesV2Lt8IntermediateTargetPersistentVisibilityTotal = 0
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateTargetMissingPriorVisibilityTotal = 92
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateTargetNoPriorCompetingIntersectionTotal = 92
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateTargetPriorCompetingIntersectionTotal = 0
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateTargetHighLiftCoveredTotal = 92
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateTargetLowOnlyVisibleTotal = 0
      ∧ a0CompletePrefixSummariesV2Lt8IntermediateTargetVisibilityStructureFailureTotal = 0 := by
  norm_num [
    a0CompletePrefixSummariesV2Lt8IntermediateTargetPersistentVisibilityTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateTargetMissingPriorVisibilityTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateTargetNoPriorCompetingIntersectionTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateTargetPriorCompetingIntersectionTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateTargetHighLiftCoveredTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateTargetLowOnlyVisibleTotal,
    a0CompletePrefixSummariesV2Lt8IntermediateTargetVisibilityStructureFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_high_lift_mod_bits_seven :
    a0CompletePrefixSummariesV2Lt8HighLiftModBitsFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8HighLiftModBitsFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_high_lift_continuation_zero :
    a0CompletePrefixSummariesV2Lt8HighLiftContinuationFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8HighLiftContinuationFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_label_split_resolution_certificate :
    a0CompletePrefixSummariesV2Lt8BranchRowsTotal = 5292
      ∧ a0CompletePrefixSummariesV2Lt8LabelSplitResolutionCertificateTotal = 5292
      ∧ a0CompletePrefixSummariesV2Lt8LabelSplitResolutionCertificateFailureTotal = 0 := by
  norm_num [
    a0CompletePrefixSummariesV2Lt8BranchRowsTotal,
    a0CompletePrefixSummariesV2Lt8LabelSplitResolutionCertificateTotal,
    a0CompletePrefixSummariesV2Lt8LabelSplitResolutionCertificateFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_label_split_summary_resolved :
    WeakBridge.LabelSplit.summaryResolved
        a0CompletePrefixSummariesV2Lt8LabelSplitSummary
      ∧ a0CompletePrefixSummariesV2Lt8LabelSplitSummaryFailure = 0 := by
  norm_num [
    a0CompletePrefixSummariesV2Lt8LabelSplitSummary,
    a0CompletePrefixSummariesV2Lt8LabelSplitSummaryFailure,
    a0CompletePrefixSummariesV2Lt8BranchRowsTotal,
    a0CompletePrefixSummariesV2Lt8LabelSplitResolutionCertificateTotal,
    WeakBridge.LabelSplit.summaryResolved,
    WeakBridge.LabelSplit.summaryFailure,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_return_partition_summary_resolved :
    a0CompletePrefixSummariesV2Lt8ReturnSamplesTotal = 11752
      ∧ a0CompletePrefixSummariesV2Lt8BranchSampleCountTotal = 11752
      ∧ a0CompletePrefixSummariesV2Lt8BranchSampleCoverageFailureTotal = 0
      ∧ WeakBridge.LabelSplit.returnPartitionResolved
          a0CompletePrefixSummariesV2Lt8ReturnPartitionSummary
      ∧ a0CompletePrefixSummariesV2Lt8ReturnPartitionSummaryFailure = 0 := by
  norm_num [
    a0CompletePrefixSummariesV2Lt8ReturnSamplesTotal,
    a0CompletePrefixSummariesV2Lt8BranchSampleCountTotal,
    a0CompletePrefixSummariesV2Lt8BranchSampleCoverageFailureTotal,
    a0CompletePrefixSummariesV2Lt8ReturnPartitionSummary,
    a0CompletePrefixSummariesV2Lt8ReturnPartitionSummaryFailure,
    WeakBridge.LabelSplit.returnPartitionResolved,
    WeakBridge.LabelSplit.returnPartitionFailure,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_outcome_decomposition_resolved :
    a0CompletePrefixSummariesV2Lt8TotalSamplesTotal = 114240
      ∧ a0CompletePrefixSummariesV2Lt8ReturnSamplesTotal = 11752
      ∧ a0CompletePrefixSummariesV2Lt8BranchSampleCountTotal = 11752
      ∧ a0CompletePrefixSummariesV2Lt8DropSamplesTotal = 101628
      ∧ a0CompletePrefixSummariesV2Lt8ValuationTailSamplesTotal = 844
      ∧ a0CompletePrefixSummariesV2Lt8StepTailSamplesTotal = 16
      ∧ WeakBridge.LabelSplit.tailSamples
          a0CompletePrefixSummariesV2Lt8OutcomeSummary = 860
      ∧ WeakBridge.LabelSplit.outcomeAccountedSamples
          a0CompletePrefixSummariesV2Lt8OutcomeSummary = 114240
      ∧ WeakBridge.LabelSplit.outcomeDecompositionResolved
          a0CompletePrefixSummariesV2Lt8OutcomeSummary
      ∧ a0CompletePrefixSummariesV2Lt8OutcomeDecompositionFailure = 0 := by
  norm_num [
    a0CompletePrefixSummariesV2Lt8TotalSamplesTotal,
    a0CompletePrefixSummariesV2Lt8ReturnSamplesTotal,
    a0CompletePrefixSummariesV2Lt8BranchSampleCountTotal,
    a0CompletePrefixSummariesV2Lt8DropSamplesTotal,
    a0CompletePrefixSummariesV2Lt8ValuationTailSamplesTotal,
    a0CompletePrefixSummariesV2Lt8StepTailSamplesTotal,
    a0CompletePrefixSummariesV2Lt8BranchSampleCoverageFailureTotal,
    a0CompletePrefixSummariesV2Lt8OutcomeSummary,
    a0CompletePrefixSummariesV2Lt8OutcomeDecompositionFailure,
    WeakBridge.LabelSplit.tailSamples,
    WeakBridge.LabelSplit.outcomeAccountedSamples,
    WeakBridge.LabelSplit.outcomeDecompositionResolved,
    WeakBridge.LabelSplit.outcomeDecompositionFailure,
    a0CompletePrefixSummariesV2Lt8]

/--
Named extraction of the unresolved declared-tail counts in the current
complete-prefix A0 summary.

This is an audit fact, not an asymptotic statement: the imported finite
prefix has explicit valuation and step tails that still require a separate
loss-soundness or absence proof before it can instantiate the global bridge.
-/
theorem a0CompletePrefixSummariesV2Lt8_declared_tail_counts :
    a0CompletePrefixSummariesV2Lt8ValuationTailSamplesTotal = 844
      ∧ a0CompletePrefixSummariesV2Lt8StepTailSamplesTotal = 16
      ∧ WeakBridge.LabelSplit.tailSamples
          a0CompletePrefixSummariesV2Lt8OutcomeSummary = 860 := by
  rcases a0CompletePrefixSummariesV2Lt8_outcome_decomposition_resolved with
    ⟨_, _, _, _, hvaluation, hstep, htail, _, _, _⟩
  exact ⟨hvaluation, hstep, htail⟩

theorem a0CompletePrefixSummariesV2Lt8_declared_tail_positive :
    0 < WeakBridge.LabelSplit.tailSamples
      a0CompletePrefixSummariesV2Lt8OutcomeSummary := by
  have htail :=
    a0CompletePrefixSummariesV2Lt8_declared_tail_counts.2.2
  rw [htail]
  norm_num

/--
Finite semantic replay summary from script 126 with proof-facing terminal
priority.

These counters are produced with `--semantic-replay-step-cap 100`: after each
Syracuse step the replay checks `drop` before declaring a valuation tail.
This is a finite-prefix replay only.  It does not assert an infinite
source partition.
-/
structure A0SemanticReplaySummary where
  prefixBits : Nat
  stepCap : Nat
  totalSamples : Nat
  dropSamples : Nat
  returnSamples : Nat
  valuationTailSamples : Nat
  stepTailSamples : Nat
  dropStepMax : Nat
  returnStepMax : Nat
  deriving Repr, DecidableEq

def a0SemanticReplaySummariesV2Lt8Cap100 :
    List A0SemanticReplaySummary :=
  [
    { prefixBits := 12, stepCap := 100, totalSamples := 16320,
      dropSamples := 14668, returnSamples := 1652,
      valuationTailSamples := 0, stepTailSamples := 0,
      dropStepMax := 68, returnStepMax := 51 },
    { prefixBits := 13, stepCap := 100, totalSamples := 32640,
      dropSamples := 29288, returnSamples := 3352,
      valuationTailSamples := 0, stepTailSamples := 0,
      dropStepMax := 91, returnStepMax := 73 },
    { prefixBits := 14, stepCap := 100, totalSamples := 65280,
      dropSamples := 58532, returnSamples := 6748,
      valuationTailSamples := 0, stepTailSamples := 0,
      dropStepMax := 91, returnStepMax := 75 }
  ]

def a0SemanticReplayV2Lt8Cap100TotalSamplesTotal : Nat :=
  a0SemanticReplaySummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.totalSamples)
    0

def a0SemanticReplayV2Lt8Cap100DropSamplesTotal : Nat :=
  a0SemanticReplaySummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.dropSamples)
    0

def a0SemanticReplayV2Lt8Cap100ReturnSamplesTotal : Nat :=
  a0SemanticReplaySummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.returnSamples)
    0

def a0SemanticReplayV2Lt8Cap100ValuationTailSamplesTotal : Nat :=
  a0SemanticReplaySummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.valuationTailSamples)
    0

def a0SemanticReplayV2Lt8Cap100StepTailSamplesTotal : Nat :=
  a0SemanticReplaySummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.stepTailSamples)
    0

def a0SemanticReplayV2Lt8Cap100LossSamplesTotal : Nat :=
  a0SemanticReplayV2Lt8Cap100ValuationTailSamplesTotal
    + a0SemanticReplayV2Lt8Cap100StepTailSamplesTotal

def a0SemanticReplayV2Lt8Cap100DropStepMax : Nat :=
  a0SemanticReplaySummariesV2Lt8Cap100.foldl
    (fun acc row => max acc row.dropStepMax)
    0

def a0SemanticReplayV2Lt8Cap100ReturnStepMax : Nat :=
  a0SemanticReplaySummariesV2Lt8Cap100.foldl
    (fun acc row => max acc row.returnStepMax)
    0

def a0SemanticReplayV2Lt8Cap100CoverageFailureTotal : Nat :=
  a0SemanticReplaySummariesV2Lt8Cap100.foldl
    (fun acc row =>
      acc +
        if row.dropSamples + row.returnSamples
            + row.valuationTailSamples + row.stepTailSamples
          = row.totalSamples then 0 else 1)
    0

noncomputable def a0SemanticReplayV2Lt8Cap100OutcomeSummary :
    WeakBridge.LabelSplit.OutcomeSummary :=
  { totalSamples := a0SemanticReplayV2Lt8Cap100TotalSamplesTotal,
    returnSamples := a0SemanticReplayV2Lt8Cap100ReturnSamplesTotal,
    coveredReturnSamples := a0SemanticReplayV2Lt8Cap100ReturnSamplesTotal,
    dropSamples := a0SemanticReplayV2Lt8Cap100DropSamplesTotal,
    valuationTailSamples := a0SemanticReplayV2Lt8Cap100ValuationTailSamplesTotal,
    stepTailSamples := a0SemanticReplayV2Lt8Cap100StepTailSamplesTotal,
    returnCoverageFailures := 0 }

noncomputable def a0SemanticReplayV2Lt8Cap100OutcomeFailure : Nat :=
  WeakBridge.LabelSplit.outcomeDecompositionFailure
    a0SemanticReplayV2Lt8Cap100OutcomeSummary

theorem a0SemanticReplayV2Lt8Cap100_loss_free :
    a0SemanticReplayV2Lt8Cap100TotalSamplesTotal = 114240
      ∧ a0SemanticReplayV2Lt8Cap100DropSamplesTotal = 102488
      ∧ a0SemanticReplayV2Lt8Cap100ReturnSamplesTotal = 11752
      ∧ a0SemanticReplayV2Lt8Cap100ValuationTailSamplesTotal = 0
      ∧ a0SemanticReplayV2Lt8Cap100StepTailSamplesTotal = 0
      ∧ a0SemanticReplayV2Lt8Cap100LossSamplesTotal = 0
      ∧ a0SemanticReplayV2Lt8Cap100DropStepMax = 91
      ∧ a0SemanticReplayV2Lt8Cap100ReturnStepMax = 75
      ∧ WeakBridge.LabelSplit.tailSamples
          a0SemanticReplayV2Lt8Cap100OutcomeSummary = 0
      ∧ WeakBridge.LabelSplit.outcomeAccountedSamples
          a0SemanticReplayV2Lt8Cap100OutcomeSummary = 114240
      ∧ WeakBridge.LabelSplit.outcomeDecompositionResolved
          a0SemanticReplayV2Lt8Cap100OutcomeSummary
      ∧ a0SemanticReplayV2Lt8Cap100CoverageFailureTotal = 0
      ∧ a0SemanticReplayV2Lt8Cap100OutcomeFailure = 0 := by
  norm_num [
    a0SemanticReplayV2Lt8Cap100TotalSamplesTotal,
    a0SemanticReplayV2Lt8Cap100DropSamplesTotal,
    a0SemanticReplayV2Lt8Cap100ReturnSamplesTotal,
    a0SemanticReplayV2Lt8Cap100ValuationTailSamplesTotal,
    a0SemanticReplayV2Lt8Cap100StepTailSamplesTotal,
    a0SemanticReplayV2Lt8Cap100LossSamplesTotal,
    a0SemanticReplayV2Lt8Cap100DropStepMax,
    a0SemanticReplayV2Lt8Cap100ReturnStepMax,
    a0SemanticReplayV2Lt8Cap100CoverageFailureTotal,
    a0SemanticReplayV2Lt8Cap100OutcomeSummary,
    a0SemanticReplayV2Lt8Cap100OutcomeFailure,
    WeakBridge.LabelSplit.tailSamples,
    WeakBridge.LabelSplit.outcomeAccountedSamples,
    WeakBridge.LabelSplit.outcomeDecompositionResolved,
    WeakBridge.LabelSplit.outcomeDecompositionFailure,
    a0SemanticReplaySummariesV2Lt8Cap100]

/--
Comparison between the conservative complete-prefix accounting and the
proof-facing semantic replay.

The finite replay keeps the same total sample count and the same return count,
but moves exactly the formerly declared conservative tail mass into the direct
drop count.  This is only a finite cap-100 replay fact; it does not assert an
infinite source partition.
-/
theorem a0SemanticReplayV2Lt8Cap100_reclassifies_conservative_tails :
    a0SemanticReplayV2Lt8Cap100TotalSamplesTotal
        = a0CompletePrefixSummariesV2Lt8TotalSamplesTotal
      ∧ a0SemanticReplayV2Lt8Cap100ReturnSamplesTotal
        = a0CompletePrefixSummariesV2Lt8ReturnSamplesTotal
      ∧ a0SemanticReplayV2Lt8Cap100DropSamplesTotal
        = a0CompletePrefixSummariesV2Lt8DropSamplesTotal
          + WeakBridge.LabelSplit.tailSamples
              a0CompletePrefixSummariesV2Lt8OutcomeSummary
      ∧ WeakBridge.LabelSplit.tailSamples
          a0SemanticReplayV2Lt8Cap100OutcomeSummary = 0
      ∧ a0SemanticReplayV2Lt8Cap100CoverageFailureTotal = 0
      ∧ a0SemanticReplayV2Lt8Cap100OutcomeFailure = 0 := by
  norm_num [
    a0SemanticReplayV2Lt8Cap100TotalSamplesTotal,
    a0SemanticReplayV2Lt8Cap100ReturnSamplesTotal,
    a0SemanticReplayV2Lt8Cap100DropSamplesTotal,
    a0SemanticReplayV2Lt8Cap100ValuationTailSamplesTotal,
    a0SemanticReplayV2Lt8Cap100StepTailSamplesTotal,
    a0SemanticReplayV2Lt8Cap100CoverageFailureTotal,
    a0SemanticReplayV2Lt8Cap100OutcomeSummary,
    a0SemanticReplayV2Lt8Cap100OutcomeFailure,
    a0CompletePrefixSummariesV2Lt8TotalSamplesTotal,
    a0CompletePrefixSummariesV2Lt8ReturnSamplesTotal,
    a0CompletePrefixSummariesV2Lt8DropSamplesTotal,
    a0CompletePrefixSummariesV2Lt8ValuationTailSamplesTotal,
    a0CompletePrefixSummariesV2Lt8StepTailSamplesTotal,
    a0CompletePrefixSummariesV2Lt8OutcomeSummary,
    WeakBridge.LabelSplit.tailSamples,
    WeakBridge.LabelSplit.outcomeAccountedSamples,
    WeakBridge.LabelSplit.outcomeDecompositionResolved,
    WeakBridge.LabelSplit.outcomeDecompositionFailure,
    a0SemanticReplaySummariesV2Lt8Cap100,
    a0CompletePrefixSummariesV2Lt8]

/--
Compact word-audit summary for the semantic replay drops.

This intentionally records only compression counters.  The actual suffix words
are not imported here: the purpose is to document that a raw Lean row import
would be large and mostly singleton, while the common-prefix/suffix criterion
is the right proof-facing target.
-/
structure A0SemanticDropWordAuditSummary where
  prefixBits : Nat
  dropSamples : Nat
  distinctWords : Nat
  phaseWordGroups : Nat
  phaseWordSingletonGroups : Nat
  distinctSuffixes : Nat
  suffixSlopeFailureWords : Nat
  suffixThresholdMax : Nat
  suffixCertificateRows : Nat
  suffixCertificateFailures : Nat
  suffixCertificateThresholdMax : Nat
  suffixPairCertificateRows : Nat
  suffixPairCertificateFailures : Nat
  suffixPairCertificateThresholdMax : Nat
  commonPrefixFailures : Nat
  commonPrefixSamples : Nat
  deriving Repr, DecidableEq

def a0SemanticDropWordAuditSummariesV2Lt8Cap100 :
    List A0SemanticDropWordAuditSummary :=
  [
    { prefixBits := 12, dropSamples := 14668,
      distinctWords := 2287, phaseWordGroups := 9148,
      phaseWordSingletonGroups := 8252, distinctSuffixes := 2287,
      suffixSlopeFailureWords := 0, suffixThresholdMax := 320,
      suffixCertificateRows := 2287, suffixCertificateFailures := 0,
      suffixCertificateThresholdMax := 320,
      suffixPairCertificateRows := 241, suffixPairCertificateFailures := 0,
      suffixPairCertificateThresholdMax := 320,
      commonPrefixFailures := 0, commonPrefixSamples := 14668 },
    { prefixBits := 13, dropSamples := 29288,
      distinctWords := 4230, phaseWordGroups := 16920,
      phaseWordSingletonGroups := 15592, distinctSuffixes := 4230,
      suffixSlopeFailureWords := 0, suffixThresholdMax := 320,
      suffixCertificateRows := 4230, suffixCertificateFailures := 0,
      suffixCertificateThresholdMax := 320,
      suffixPairCertificateRows := 290, suffixPairCertificateFailures := 0,
      suffixPairCertificateThresholdMax := 320,
      commonPrefixFailures := 0, commonPrefixSamples := 29288 },
    { prefixBits := 14, dropSamples := 58532,
      distinctWords := 7831, phaseWordGroups := 31324,
      phaseWordSingletonGroups := 28852, distinctSuffixes := 7831,
      suffixSlopeFailureWords := 0, suffixThresholdMax := 455,
      suffixCertificateRows := 7831, suffixCertificateFailures := 0,
      suffixCertificateThresholdMax := 455,
      suffixPairCertificateRows := 351, suffixPairCertificateFailures := 0,
      suffixPairCertificateThresholdMax := 455,
      commonPrefixFailures := 0, commonPrefixSamples := 58532 }
  ]

def a0SemanticDropWordAuditV2Lt8Cap100DropSamplesTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.dropSamples)
    0

def a0SemanticDropWordAuditV2Lt8Cap100DistinctWordsTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.distinctWords)
    0

def a0SemanticDropWordAuditV2Lt8Cap100PhaseWordGroupsTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.phaseWordGroups)
    0

def a0SemanticDropWordAuditV2Lt8Cap100PhaseWordSingletonGroupsTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.phaseWordSingletonGroups)
    0

def a0SemanticDropWordAuditV2Lt8Cap100DistinctSuffixesTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.distinctSuffixes)
    0

def a0SemanticDropWordAuditV2Lt8Cap100SuffixSlopeFailureWordsTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.suffixSlopeFailureWords)
    0

def a0SemanticDropWordAuditV2Lt8Cap100SuffixThresholdMax : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => max acc row.suffixThresholdMax)
    0

def a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateRowsTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.suffixCertificateRows)
    0

def a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateFailuresTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.suffixCertificateFailures)
    0

def a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateThresholdMax : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => max acc row.suffixCertificateThresholdMax)
    0

def a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateRowsTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.suffixPairCertificateRows)
    0

def a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateRowsMax : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => max acc row.suffixPairCertificateRows)
    0

def a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateFailuresTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.suffixPairCertificateFailures)
    0

def a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateThresholdMax : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => max acc row.suffixPairCertificateThresholdMax)
    0

def a0SemanticDropWordAuditV2Lt8Cap100CommonPrefixFailuresTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.commonPrefixFailures)
    0

def a0SemanticDropWordAuditV2Lt8Cap100CommonPrefixSamplesTotal : Nat :=
  a0SemanticDropWordAuditSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.commonPrefixSamples)
    0

theorem a0SemanticDropWordAuditV2Lt8Cap100_summary :
    a0SemanticDropWordAuditSummariesV2Lt8Cap100.length = 3
      ∧ a0SemanticDropWordAuditV2Lt8Cap100DropSamplesTotal = 102488
      ∧ a0SemanticDropWordAuditV2Lt8Cap100DropSamplesTotal
        = a0SemanticReplayV2Lt8Cap100DropSamplesTotal
      ∧ a0SemanticDropWordAuditV2Lt8Cap100DistinctWordsTotal = 14348
      ∧ a0SemanticDropWordAuditV2Lt8Cap100PhaseWordGroupsTotal = 57392
      ∧ a0SemanticDropWordAuditV2Lt8Cap100PhaseWordSingletonGroupsTotal = 52696
      ∧ a0SemanticDropWordAuditV2Lt8Cap100DistinctSuffixesTotal = 14348
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixSlopeFailureWordsTotal = 0
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixThresholdMax = 455
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateRowsTotal = 14348
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateRowsTotal
        = a0SemanticDropWordAuditV2Lt8Cap100DistinctSuffixesTotal
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateFailuresTotal = 0
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateThresholdMax = 455
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateRowsTotal = 882
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateRowsMax = 351
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateFailuresTotal = 0
      ∧ a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateThresholdMax = 455
      ∧ a0SemanticDropWordAuditV2Lt8Cap100CommonPrefixFailuresTotal = 0
      ∧ a0SemanticDropWordAuditV2Lt8Cap100CommonPrefixSamplesTotal = 102488
      ∧ a0SemanticDropWordAuditV2Lt8Cap100CommonPrefixSamplesTotal
        = a0SemanticReplayV2Lt8Cap100DropSamplesTotal := by
  norm_num [
    a0SemanticDropWordAuditSummariesV2Lt8Cap100,
    a0SemanticDropWordAuditV2Lt8Cap100DropSamplesTotal,
    a0SemanticDropWordAuditV2Lt8Cap100DistinctWordsTotal,
    a0SemanticDropWordAuditV2Lt8Cap100PhaseWordGroupsTotal,
    a0SemanticDropWordAuditV2Lt8Cap100PhaseWordSingletonGroupsTotal,
    a0SemanticDropWordAuditV2Lt8Cap100DistinctSuffixesTotal,
    a0SemanticDropWordAuditV2Lt8Cap100SuffixSlopeFailureWordsTotal,
    a0SemanticDropWordAuditV2Lt8Cap100SuffixThresholdMax,
    a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateRowsTotal,
    a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateFailuresTotal,
    a0SemanticDropWordAuditV2Lt8Cap100SuffixCertificateThresholdMax,
    a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateRowsTotal,
    a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateRowsMax,
    a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateFailuresTotal,
    a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateThresholdMax,
    a0SemanticDropWordAuditV2Lt8Cap100CommonPrefixFailuresTotal,
    a0SemanticDropWordAuditV2Lt8Cap100CommonPrefixSamplesTotal,
    a0SemanticReplayV2Lt8Cap100DropSamplesTotal,
    a0SemanticReplaySummariesV2Lt8Cap100]

/--
A single T14 pair-compression row with the largest observed suffix threshold.

This is a feasibility check for the next generated table: Lean can verify the
exact `ValidAt455` arithmetic for a row whose pair is `(suffix_len,suffix_sum)
= (35,58)`.  It is not a cover theorem and it is not the full pair table.
-/
def a0SemanticSuffixPairCertificateT14ThresholdMax :
    A0SemanticSuffixPairCertificate :=
  { suffixLength := 35
    suffixSum := 58
    suffixConstMax := 1174428324757245841
    slopeGap := 420491770248316829
    thresholdMinNMax := 455 }

theorem a0SemanticSuffixPairCertificateT14ThresholdMax_valid :
    a0SemanticSuffixPairCertificateT14ThresholdMax.ValidAt455 := by
  norm_num [
    a0SemanticSuffixPairCertificateT14ThresholdMax,
    A0SemanticSuffixPairCertificate.ValidAt455,
    A0SemanticSuffixPairCertificate.ValidAtCutoff]

def a0SemanticSuffixPairCertificatesT14Prototype :
    List A0SemanticSuffixPairCertificate :=
  [a0SemanticSuffixPairCertificateT14ThresholdMax]

set_option linter.style.nativeDecide false in
theorem a0SemanticSuffixPairCertificatesT14Prototype_allValid :
    A0SemanticSuffixPairCertificate.allValidAt455Bool
      a0SemanticSuffixPairCertificatesT14Prototype = true := by
  native_decide

/--
The complete T14 pair-compressed semantic-drop suffix certificate.

Each row groups observed suffixes with the same `(length,sum)` and
stores the largest observed `syracuseWordConst` and threshold for
that pair.  This is finite-prefix data only: it does not prove that
future sources land in this table.
-/
def a0SemanticSuffixPairCertificatesT14 :
    List A0SemanticSuffixPairCertificate :=
  [
    { suffixLength := 1, suffixSum := 5, suffixConstMax := 1, slopeGap := 1909, thresholdMinNMax := 2 },
    { suffixLength := 1, suffixSum := 6, suffixConstMax := 1, slopeGap := 6005, thresholdMinNMax := 1 },
    { suffixLength := 1, suffixSum := 7, suffixConstMax := 1, slopeGap := 14197, thresholdMinNMax := 1 },
    { suffixLength := 1, suffixSum := 8, suffixConstMax := 1, slopeGap := 30581, thresholdMinNMax := 1 },
    { suffixLength := 1, suffixSum := 9, suffixConstMax := 1, slopeGap := 63349, thresholdMinNMax := 1 },
    { suffixLength := 1, suffixSum := 10, suffixConstMax := 1, slopeGap := 128885, thresholdMinNMax := 1 },
    { suffixLength := 1, suffixSum := 11, suffixConstMax := 1, slopeGap := 259957, thresholdMinNMax := 1 },
    { suffixLength := 1, suffixSum := 12, suffixConstMax := 1, slopeGap := 522101, thresholdMinNMax := 1 },
    { suffixLength := 1, suffixSum := 13, suffixConstMax := 1, slopeGap := 1046389, thresholdMinNMax := 1 },
    { suffixLength := 1, suffixSum := 14, suffixConstMax := 1, slopeGap := 2094965, thresholdMinNMax := 1 },
    { suffixLength := 1, suffixSum := 15, suffixConstMax := 1, slopeGap := 4192117, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 6, suffixConstMax := 19, slopeGap := 1631, thresholdMinNMax := 6 },
    { suffixLength := 2, suffixSum := 7, suffixConstMax := 19, slopeGap := 9823, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 8, suffixConstMax := 19, slopeGap := 26207, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 9, suffixConstMax := 19, slopeGap := 58975, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 10, suffixConstMax := 19, slopeGap := 124511, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 11, suffixConstMax := 19, slopeGap := 255583, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 12, suffixConstMax := 19, slopeGap := 517727, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 13, suffixConstMax := 19, slopeGap := 1042015, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 14, suffixConstMax := 19, slopeGap := 2090591, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 15, suffixConstMax := 19, slopeGap := 4187743, thresholdMinNMax := 1 },
    { suffixLength := 2, suffixSum := 16, suffixConstMax := 11, slopeGap := 8382047, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 8, suffixConstMax := 89, slopeGap := 13085, thresholdMinNMax := 3 },
    { suffixLength := 3, suffixSum := 9, suffixConstMax := 89, slopeGap := 45853, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 10, suffixConstMax := 89, slopeGap := 111389, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 11, suffixConstMax := 89, slopeGap := 242461, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 12, suffixConstMax := 89, slopeGap := 504605, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 13, suffixConstMax := 89, slopeGap := 1028893, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 14, suffixConstMax := 89, slopeGap := 2077469, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 15, suffixConstMax := 89, slopeGap := 4174621, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 17, suffixConstMax := 19, slopeGap := 16757533, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 18, suffixConstMax := 65, slopeGap := 33534749, thresholdMinNMax := 1 },
    { suffixLength := 3, suffixSum := 19, suffixConstMax := 47, slopeGap := 67089181, thresholdMinNMax := 1 },
    { suffixLength := 4, suffixSum := 9, suffixConstMax := 395, slopeGap := 6487, thresholdMinNMax := 18 },
    { suffixLength := 4, suffixSum := 10, suffixConstMax := 395, slopeGap := 72023, thresholdMinNMax := 2 },
    { suffixLength := 4, suffixSum := 11, suffixConstMax := 395, slopeGap := 203095, thresholdMinNMax := 1 },
    { suffixLength := 4, suffixSum := 12, suffixConstMax := 395, slopeGap := 465239, thresholdMinNMax := 1 },
    { suffixLength := 4, suffixSum := 13, suffixConstMax := 395, slopeGap := 989527, thresholdMinNMax := 1 },
    { suffixLength := 4, suffixSum := 14, suffixConstMax := 395, slopeGap := 2038103, thresholdMinNMax := 1 },
    { suffixLength := 4, suffixSum := 15, suffixConstMax := 395, slopeGap := 4135255, thresholdMinNMax := 1 },
    { suffixLength := 4, suffixSum := 16, suffixConstMax := 323, slopeGap := 8329559, thresholdMinNMax := 1 },
    { suffixLength := 4, suffixSum := 17, suffixConstMax := 211, slopeGap := 16718167, thresholdMinNMax := 1 },
    { suffixLength := 4, suffixSum := 18, suffixConstMax := 331, slopeGap := 33495383, thresholdMinNMax := 1 },
    { suffixLength := 5, suffixSum := 11, suffixConstMax := 1441, slopeGap := 84997, thresholdMinNMax := 5 },
    { suffixLength := 5, suffixSum := 12, suffixConstMax := 1441, slopeGap := 347141, thresholdMinNMax := 2 },
    { suffixLength := 5, suffixSum := 13, suffixConstMax := 1441, slopeGap := 871429, thresholdMinNMax := 1 },
    { suffixLength := 5, suffixSum := 14, suffixConstMax := 1441, slopeGap := 1920005, thresholdMinNMax := 1 },
    { suffixLength := 5, suffixSum := 15, suffixConstMax := 1441, slopeGap := 4017157, thresholdMinNMax := 1 },
    { suffixLength := 5, suffixSum := 16, suffixConstMax := 1249, slopeGap := 8211461, thresholdMinNMax := 1 },
    { suffixLength := 5, suffixSum := 17, suffixConstMax := 1225, slopeGap := 16600069, thresholdMinNMax := 1 },
    { suffixLength := 5, suffixSum := 18, suffixConstMax := 283, slopeGap := 33377285, thresholdMinNMax := 1 },
    { suffixLength := 5, suffixSum := 19, suffixConstMax := 811, slopeGap := 66931717, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 13, suffixConstMax := 5347, slopeGap := 517135, thresholdMinNMax := 3 },
    { suffixLength := 6, suffixSum := 14, suffixConstMax := 5347, slopeGap := 1565711, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 15, suffixConstMax := 4835, slopeGap := 3662863, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 16, suffixConstMax := 5347, slopeGap := 7857167, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 17, suffixConstMax := 4213, slopeGap := 16245775, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 18, suffixConstMax := 3863, slopeGap := 33022991, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 19, suffixConstMax := 4387, slopeGap := 66577423, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 20, suffixConstMax := 3701, slopeGap := 133686287, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 21, suffixConstMax := 2065, slopeGap := 267904015, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 22, suffixConstMax := 1121, slopeGap := 536339471, thresholdMinNMax := 1 },
    { suffixLength := 6, suffixSum := 24, suffixConstMax := 989, slopeGap := 2146952207, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 14, suffixConstMax := 20137, slopeGap := 502829, thresholdMinNMax := 9 },
    { suffixLength := 7, suffixSum := 15, suffixConstMax := 20137, slopeGap := 2599981, thresholdMinNMax := 2 },
    { suffixLength := 7, suffixSum := 16, suffixConstMax := 18409, slopeGap := 6794285, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 17, suffixConstMax := 16657, slopeGap := 15182893, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 18, suffixConstMax := 18193, slopeGap := 31960109, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 19, suffixConstMax := 13063, slopeGap := 65514541, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 20, suffixConstMax := 12289, slopeGap := 132623405, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 21, suffixConstMax := 16735, slopeGap := 266841133, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 22, suffixConstMax := 13903, slopeGap := 535276589, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 23, suffixConstMax := 11663, slopeGap := 1072147501, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 24, suffixConstMax := 7183, slopeGap := 2145889325, thresholdMinNMax := 1 },
    { suffixLength := 7, suffixSum := 25, suffixConstMax := 14825, slopeGap := 4293372973, thresholdMinNMax := 1 },
    { suffixLength := 8, suffixSum := 16, suffixConstMax := 62771, slopeGap := 3605639, thresholdMinNMax := 4 },
    { suffixLength := 8, suffixSum := 17, suffixConstMax := 63419, slopeGap := 11994247, thresholdMinNMax := 2 },
    { suffixLength := 8, suffixSum := 18, suffixConstMax := 58811, slopeGap := 28771463, thresholdMinNMax := 1 },
    { suffixLength := 8, suffixSum := 19, suffixConstMax := 50783, slopeGap := 62325895, thresholdMinNMax := 1 },
    { suffixLength := 8, suffixSum := 20, suffixConstMax := 38183, slopeGap := 129434759, thresholdMinNMax := 1 },
    { suffixLength := 8, suffixSum := 21, suffixConstMax := 45727, slopeGap := 263652487, thresholdMinNMax := 1 },
    { suffixLength := 8, suffixSum := 22, suffixConstMax := 43817, slopeGap := 532087943, thresholdMinNMax := 1 },
    { suffixLength := 8, suffixSum := 23, suffixConstMax := 18125, slopeGap := 1068958855, thresholdMinNMax := 1 },
    { suffixLength := 8, suffixSum := 24, suffixConstMax := 17333, slopeGap := 2142700679, thresholdMinNMax := 1 },
    { suffixLength := 9, suffixSum := 17, suffixConstMax := 206321, slopeGap := 2428309, thresholdMinNMax := 18 },
    { suffixLength := 9, suffixSum := 18, suffixConstMax := 220145, slopeGap := 19205525, thresholdMinNMax := 3 },
    { suffixLength := 9, suffixSum := 19, suffixConstMax := 212657, slopeGap := 52759957, thresholdMinNMax := 1 },
    { suffixLength := 9, suffixSum := 20, suffixConstMax := 166061, slopeGap := 119868821, thresholdMinNMax := 1 },
    { suffixLength := 9, suffixSum := 21, suffixConstMax := 149963, slopeGap := 254086549, thresholdMinNMax := 1 },
    { suffixLength := 9, suffixSum := 22, suffixConstMax := 180721, slopeGap := 522522005, thresholdMinNMax := 1 },
    { suffixLength := 9, suffixSum := 23, suffixConstMax := 176639, slopeGap := 1059392917, thresholdMinNMax := 1 },
    { suffixLength := 9, suffixSum := 24, suffixConstMax := 148181, slopeGap := 2133134741, thresholdMinNMax := 1 },
    { suffixLength := 9, suffixSum := 25, suffixConstMax := 155291, slopeGap := 4280618389, thresholdMinNMax := 1 },
    { suffixLength := 10, suffixSum := 19, suffixConstMax := 685459, slopeGap := 24062143, thresholdMinNMax := 6 },
    { suffixLength := 10, suffixSum := 20, suffixConstMax := 781267, slopeGap := 91171007, thresholdMinNMax := 2 },
    { suffixLength := 10, suffixSum := 21, suffixConstMax := 568723, slopeGap := 225388735, thresholdMinNMax := 1 },
    { suffixLength := 10, suffixSum := 22, suffixConstMax := 652315, slopeGap := 493824191, thresholdMinNMax := 1 },
    { suffixLength := 10, suffixSum := 23, suffixConstMax := 591835, slopeGap := 1030695103, thresholdMinNMax := 1 },
    { suffixLength := 10, suffixSum := 24, suffixConstMax := 566021, slopeGap := 2104436927, thresholdMinNMax := 1 },
    { suffixLength := 10, suffixSum := 25, suffixConstMax := 390271, slopeGap := 4251920575, thresholdMinNMax := 1 },
    { suffixLength := 10, suffixSum := 26, suffixConstMax := 493813, slopeGap := 8546887871, thresholdMinNMax := 1 },
    { suffixLength := 10, suffixSum := 27, suffixConstMax := 655879, slopeGap := 17136822463, thresholdMinNMax := 1 },
    { suffixLength := 10, suffixSum := 28, suffixConstMax := 321743, slopeGap := 34316691647, thresholdMinNMax := 1 },
    { suffixLength := 11, suffixSum := 20, suffixConstMax := 2054969, slopeGap := 5077565, thresholdMinNMax := 81 },
    { suffixLength := 11, suffixSum := 21, suffixConstMax := 1939639, slopeGap := 139295293, thresholdMinNMax := 3 },
    { suffixLength := 11, suffixSum := 22, suffixConstMax := 2190415, slopeGap := 407730749, thresholdMinNMax := 2 },
    { suffixLength := 11, suffixSum := 23, suffixConstMax := 2212433, slopeGap := 944601661, thresholdMinNMax := 1 },
    { suffixLength := 11, suffixSum := 24, suffixConstMax := 1515703, slopeGap := 2018343485, thresholdMinNMax := 1 },
    { suffixLength := 11, suffixSum := 25, suffixConstMax := 1444067, slopeGap := 4165827133, thresholdMinNMax := 1 },
    { suffixLength := 11, suffixSum := 26, suffixConstMax := 783155, slopeGap := 8460794429, thresholdMinNMax := 1 },
    { suffixLength := 11, suffixSum := 27, suffixConstMax := 874621, slopeGap := 17050729021, thresholdMinNMax := 1 },
    { suffixLength := 11, suffixSum := 28, suffixConstMax := 1163167, slopeGap := 34230598205, thresholdMinNMax := 1 },
    { suffixLength := 12, suffixSum := 22, suffixConstMax := 6227051, slopeGap := 149450423, thresholdMinNMax := 9 },
    { suffixLength := 12, suffixSum := 23, suffixConstMax := 6685997, slopeGap := 686321335, thresholdMinNMax := 2 },
    { suffixLength := 12, suffixSum := 24, suffixConstMax := 6771371, slopeGap := 1760063159, thresholdMinNMax := 1 },
    { suffixLength := 12, suffixSum := 25, suffixConstMax := 4437815, slopeGap := 3907546807, thresholdMinNMax := 1 },
    { suffixLength := 12, suffixSum := 26, suffixConstMax := 4459895, slopeGap := 8202514103, thresholdMinNMax := 1 },
    { suffixLength := 12, suffixSum := 27, suffixConstMax := 4914365, slopeGap := 16792448695, thresholdMinNMax := 1 },
    { suffixLength := 12, suffixSum := 28, suffixConstMax := 4459037, slopeGap := 33972317879, thresholdMinNMax := 1 },
    { suffixLength := 12, suffixSum := 29, suffixConstMax := 3016879, slopeGap := 68332056247, thresholdMinNMax := 1 },
    { suffixLength := 12, suffixSum := 30, suffixConstMax := 4642541, slopeGap := 137051532983, thresholdMinNMax := 1 },
    { suffixLength := 13, suffixSum := 24, suffixConstMax := 24037697, slopeGap := 985222181, thresholdMinNMax := 5 },
    { suffixLength := 13, suffixSum := 25, suffixConstMax := 17609621, slopeGap := 3132705829, thresholdMinNMax := 2 },
    { suffixLength := 13, suffixSum := 26, suffixConstMax := 19603645, slopeGap := 7427673125, thresholdMinNMax := 1 },
    { suffixLength := 13, suffixSum := 27, suffixConstMax := 17130497, slopeGap := 16017607717, thresholdMinNMax := 1 },
    { suffixLength := 13, suffixSum := 28, suffixConstMax := 12939077, slopeGap := 33197476901, thresholdMinNMax := 1 },
    { suffixLength := 13, suffixSum := 29, suffixConstMax := 19689391, slopeGap := 67557215269, thresholdMinNMax := 1 },
    { suffixLength := 13, suffixSum := 30, suffixConstMax := 15186277, slopeGap := 136276692005, thresholdMinNMax := 1 },
    { suffixLength := 13, suffixSum := 31, suffixConstMax := 3204115, slopeGap := 273715645477, thresholdMinNMax := 1 },
    { suffixLength := 14, suffixSum := 25, suffixConstMax := 68785211, slopeGap := 808182895, thresholdMinNMax := 16 },
    { suffixLength := 14, suffixSum := 26, suffixConstMax := 60450593, slopeGap := 5103150191, thresholdMinNMax := 3 },
    { suffixLength := 14, suffixSum := 27, suffixConstMax := 56807111, slopeGap := 13693084783, thresholdMinNMax := 1 },
    { suffixLength := 14, suffixSum := 28, suffixConstMax := 77047355, slopeGap := 30872953967, thresholdMinNMax := 1 },
    { suffixLength := 14, suffixSum := 29, suffixConstMax := 40290545, slopeGap := 65232692335, thresholdMinNMax := 1 },
    { suffixLength := 14, suffixSum := 30, suffixConstMax := 42548041, slopeGap := 133952169071, thresholdMinNMax := 1 },
    { suffixLength := 14, suffixSum := 31, suffixConstMax := 47676125, slopeGap := 271391122543, thresholdMinNMax := 1 },
    { suffixLength := 14, suffixSum := 32, suffixConstMax := 23133565, slopeGap := 546269029487, thresholdMinNMax := 1 },
    { suffixLength := 14, suffixSum := 33, suffixConstMax := 39665575, slopeGap := 1096024843375, thresholdMinNMax := 1 },
    { suffixLength := 15, suffixSum := 27, suffixConstMax := 221452657, slopeGap := 6719515981, thresholdMinNMax := 6 },
    { suffixLength := 15, suffixSum := 28, suffixConstMax := 203705161, slopeGap := 23899385165, thresholdMinNMax := 2 },
    { suffixLength := 15, suffixSum := 29, suffixConstMax := 180878299, slopeGap := 58259123533, thresholdMinNMax := 1 },
    { suffixLength := 15, suffixSum := 30, suffixConstMax := 151678159, slopeGap := 126978600269, thresholdMinNMax := 1 },
    { suffixLength := 15, suffixSum := 31, suffixConstMax := 167827583, slopeGap := 264417553741, thresholdMinNMax := 1 },
    { suffixLength := 15, suffixSum := 32, suffixConstMax := 160325557, slopeGap := 539295460685, thresholdMinNMax := 1 },
    { suffixLength := 15, suffixSum := 33, suffixConstMax := 67257259, slopeGap := 1089051274573, thresholdMinNMax := 1 },
    { suffixLength := 16, suffixSum := 28, suffixConstMax := 746163725, slopeGap := 2978678759, thresholdMinNMax := 44 },
    { suffixLength := 16, suffixSum := 29, suffixConstMax := 608836591, slopeGap := 37338417127, thresholdMinNMax := 4 },
    { suffixLength := 16, suffixSum := 30, suffixConstMax := 699497699, slopeGap := 106057893863, thresholdMinNMax := 2 },
    { suffixLength := 16, suffixSum := 31, suffixConstMax := 575732165, slopeGap := 243496847335, thresholdMinNMax := 1 },
    { suffixLength := 16, suffixSum := 32, suffixConstMax := 602829275, slopeGap := 518374754279, thresholdMinNMax := 1 },
    { suffixLength := 16, suffixSum := 33, suffixConstMax := 305863801, slopeGap := 1068130568167, thresholdMinNMax := 1 },
    { suffixLength := 16, suffixSum := 34, suffixConstMax := 487105205, slopeGap := 2167642195943, thresholdMinNMax := 1 },
    { suffixLength := 16, suffixSum := 35, suffixConstMax := 332806445, slopeGap := 4366665451495, thresholdMinNMax := 1 },
    { suffixLength := 16, suffixSum := 37, suffixConstMax := 405055861, slopeGap := 17560804984807, thresholdMinNMax := 1 },
    { suffixLength := 17, suffixSum := 30, suffixConstMax := 1970519117, slopeGap := 43295774645, thresholdMinNMax := 9 },
    { suffixLength := 17, suffixSum := 31, suffixConstMax := 1705764521, slopeGap := 180734728117, thresholdMinNMax := 2 },
    { suffixLength := 17, suffixSum := 32, suffixConstMax := 2369340437, slopeGap := 455612635061, thresholdMinNMax := 1 },
    { suffixLength := 17, suffixSum := 33, suffixConstMax := 1318641743, slopeGap := 1005368448949, thresholdMinNMax := 1 },
    { suffixLength := 17, suffixSum := 34, suffixConstMax := 1288336637, slopeGap := 2104880076725, thresholdMinNMax := 1 },
    { suffixLength := 17, suffixSum := 35, suffixConstMax := 1520402641, slopeGap := 4303903332277, thresholdMinNMax := 1 },
    { suffixLength := 17, suffixSum := 36, suffixConstMax := 1676828135, slopeGap := 8701949843381, thresholdMinNMax := 1 },
    { suffixLength := 18, suffixSum := 32, suffixConstMax := 5876706235, slopeGap := 267326277407, thresholdMinNMax := 4 },
    { suffixLength := 18, suffixSum := 33, suffixConstMax := 4927958515, slopeGap := 817082091295, thresholdMinNMax := 2 },
    { suffixLength := 18, suffixSum := 34, suffixConstMax := 5201077823, slopeGap := 1916593719071, thresholdMinNMax := 1 },
    { suffixLength := 18, suffixSum := 35, suffixConstMax := 3980999965, slopeGap := 4115616974623, thresholdMinNMax := 1 },
    { suffixLength := 18, suffixSum := 36, suffixConstMax := 4030660417, slopeGap := 8513663485727, thresholdMinNMax := 1 },
    { suffixLength := 18, suffixSum := 37, suffixConstMax := 4138373729, slopeGap := 17309756507935, thresholdMinNMax := 1 },
    { suffixLength := 18, suffixSum := 38, suffixConstMax := 2107716887, slopeGap := 34901942552351, thresholdMinNMax := 1 },
    { suffixLength := 18, suffixSum := 39, suffixConstMax := 2297824265, slopeGap := 70086314641183, thresholdMinNMax := 1 },
    { suffixLength := 18, suffixSum := 40, suffixConstMax := 2114757901, slopeGap := 140455058818847, thresholdMinNMax := 1 },
    { suffixLength := 19, suffixSum := 33, suffixConstMax := 18969829379, slopeGap := 252223018333, thresholdMinNMax := 14 },
    { suffixLength := 19, suffixSum := 34, suffixConstMax := 22394735837, slopeGap := 1351734646109, thresholdMinNMax := 3 },
    { suffixLength := 19, suffixSum := 35, suffixConstMax := 20266367173, slopeGap := 3550757901661, thresholdMinNMax := 1 },
    { suffixLength := 19, suffixSum := 36, suffixConstMax := 16209623047, slopeGap := 7948804412765, thresholdMinNMax := 1 },
    { suffixLength := 19, suffixSum := 37, suffixConstMax := 9839461457, slopeGap := 16744897434973, thresholdMinNMax := 1 },
    { suffixLength := 19, suffixSum := 38, suffixConstMax := 19076062453, slopeGap := 34337083479389, thresholdMinNMax := 1 },
    { suffixLength := 20, suffixSum := 35, suffixConstMax := 60791455819, slopeGap := 1856180682775, thresholdMinNMax := 6 },
    { suffixLength := 20, suffixSum := 36, suffixConstMax := 61783118731, slopeGap := 6254227193879, thresholdMinNMax := 2 },
    { suffixLength := 20, suffixSum := 37, suffixConstMax := 34222065767, slopeGap := 15050320216087, thresholdMinNMax := 1 },
    { suffixLength := 20, suffixSum := 38, suffixConstMax := 37636815535, slopeGap := 32642506260503, thresholdMinNMax := 1 },
    { suffixLength := 20, suffixSum := 39, suffixConstMax := 34024775353, slopeGap := 67826878349335, thresholdMinNMax := 1 },
    { suffixLength := 20, suffixSum := 40, suffixConstMax := 28493241137, slopeGap := 138195622526999, thresholdMinNMax := 1 },
    { suffixLength := 20, suffixSum := 41, suffixConstMax := 44539996087, slopeGap := 278933110882327, thresholdMinNMax := 1 },
    { suffixLength := 20, suffixSum := 42, suffixConstMax := 28575030517, slopeGap := 560408087592983, thresholdMinNMax := 1 },
    { suffixLength := 21, suffixSum := 36, suffixConstMax := 233060403233, slopeGap := 1170495537221, thresholdMinNMax := 33 },
    { suffixLength := 21, suffixSum := 37, suffixConstMax := 158441340071, slopeGap := 9966588559429, thresholdMinNMax := 3 },
    { suffixLength := 21, suffixSum := 38, suffixConstMax := 143732519803, slopeGap := 27558774603845, thresholdMinNMax := 1 },
    { suffixLength := 21, suffixSum := 39, suffixConstMax := 136612703255, slopeGap := 62743146692677, thresholdMinNMax := 1 },
    { suffixLength := 21, suffixSum := 40, suffixConstMax := 146375602841, slopeGap := 133111890870341, thresholdMinNMax := 1 },
    { suffixLength := 21, suffixSum := 41, suffixConstMax := 75422452631, slopeGap := 273849379225669, thresholdMinNMax := 1 },
    { suffixLength := 21, suffixSum := 42, suffixConstMax := 76771624531, slopeGap := 555324355936325, thresholdMinNMax := 1 },
    { suffixLength := 21, suffixSum := 43, suffixConstMax := 45029597243, slopeGap := 1118274309357637, thresholdMinNMax := 1 },
    { suffixLength := 22, suffixSum := 38, suffixConstMax := 553247201825, slopeGap := 12307579633871, thresholdMinNMax := 8 },
    { suffixLength := 22, suffixSum := 39, suffixConstMax := 499618148105, slopeGap := 47491951722703, thresholdMinNMax := 2 },
    { suffixLength := 22, suffixSum := 40, suffixConstMax := 544655529307, slopeGap := 117860695900367, thresholdMinNMax := 1 },
    { suffixLength := 22, suffixSum := 41, suffixConstMax := 230167511561, slopeGap := 258598184255695, thresholdMinNMax := 1 },
    { suffixLength := 22, suffixSum := 42, suffixConstMax := 372822078947, slopeGap := 540073160966351, thresholdMinNMax := 1 },
    { suffixLength := 22, suffixSum := 43, suffixConstMax := 456163144397, slopeGap := 1103023114387663, thresholdMinNMax := 1 },
    { suffixLength := 22, suffixSum := 44, suffixConstMax := 252980396921, slopeGap := 2228923021230287, thresholdMinNMax := 1 },
    { suffixLength := 23, suffixSum := 39, suffixConstMax := 1969500910993, slopeGap := 1738366812781, thresholdMinNMax := 190 },
    { suffixLength := 23, suffixSum := 40, suffixConstMax := 1585433592899, slopeGap := 72107110990445, thresholdMinNMax := 4 },
    { suffixLength := 23, suffixSum := 41, suffixConstMax := 1343026854215, slopeGap := 212844599345773, thresholdMinNMax := 2 },
    { suffixLength := 23, suffixSum := 42, suffixConstMax := 1003849555291, slopeGap := 494319576056429, thresholdMinNMax := 1 },
    { suffixLength := 23, suffixSum := 43, suffixConstMax := 1279703029957, slopeGap := 1057269529477741, thresholdMinNMax := 1 },
    { suffixLength := 23, suffixSum := 44, suffixConstMax := 877862918699, slopeGap := 2183169436320365, thresholdMinNMax := 1 },
    { suffixLength := 23, suffixSum := 47, suffixConstMax := 1256963119873, slopeGap := 17945768132117101, thresholdMinNMax := 1 },
    { suffixLength := 24, suffixSum := 41, suffixConstMax := 5361504664141, slopeGap := 75583844616007, thresholdMinNMax := 13 },
    { suffixLength := 24, suffixSum := 42, suffixConstMax := 3382038774275, slopeGap := 357058821326663, thresholdMinNMax := 2 },
    { suffixLength := 24, suffixSum := 43, suffixConstMax := 3468618981469, slopeGap := 920008774747975, thresholdMinNMax := 1 },
    { suffixLength := 24, suffixSum := 44, suffixConstMax := 1981394942527, slopeGap := 2045908681590599, thresholdMinNMax := 1 },
    { suffixLength := 24, suffixSum := 45, suffixConstMax := 3428658885841, slopeGap := 4297708495275847, thresholdMinNMax := 1 },
    { suffixLength := 25, suffixSum := 43, suffixConstMax := 11989518920407, slopeGap := 508226510558677, thresholdMinNMax := 5 },
    { suffixLength := 25, suffixSum := 44, suffixConstMax := 10327110003487, slopeGap := 1634126417401301, thresholdMinNMax := 2 },
    { suffixLength := 25, suffixSum := 45, suffixConstMax := 9729006102857, slopeGap := 3885926231086549, thresholdMinNMax := 1 },
    { suffixLength := 25, suffixSum := 46, suffixConstMax := 6038639728867, slopeGap := 8389525858457045, thresholdMinNMax := 1 },
    { suffixLength := 25, suffixSum := 47, suffixConstMax := 11283598658797, slopeGap := 17396725113198037, thresholdMinNMax := 1 },
    { suffixLength := 26, suffixSum := 44, suffixConstMax := 53854915329427, slopeGap := 398779624833407, thresholdMinNMax := 23 },
    { suffixLength := 26, suffixSum := 45, suffixConstMax := 41546350776779, slopeGap := 2650579438518655, thresholdMinNMax := 3 },
    { suffixLength := 26, suffixSum := 46, suffixConstMax := 33477876511681, slopeGap := 7154179065889151, thresholdMinNMax := 1 },
    { suffixLength := 26, suffixSum := 47, suffixConstMax := 26421807524795, slopeGap := 16161378320630143, thresholdMinNMax := 1 },
    { suffixLength := 26, suffixSum := 48, suffixConstMax := 30950079801001, slopeGap := 34175776830112127, thresholdMinNMax := 1 },
    { suffixLength := 26, suffixSum := 49, suffixConstMax := 30794932419833, slopeGap := 70204573849076095, thresholdMinNMax := 1 },
    { suffixLength := 26, suffixSum := 50, suffixConstMax := 11306774558953, slopeGap := 142262167887004031, thresholdMinNMax := 1 },
    { suffixLength := 27, suffixSum := 46, suffixConstMax := 150888554821247, slopeGap := 3448138688185469, thresholdMinNMax := 8 },
    { suffixLength := 27, suffixSum := 47, suffixConstMax := 126417062810977, slopeGap := 12455337942926461, thresholdMinNMax := 2 },
    { suffixLength := 27, suffixSum := 48, suffixConstMax := 83807898138077, slopeGap := 30469736452408445, thresholdMinNMax := 1 },
    { suffixLength := 27, suffixSum := 49, suffixConstMax := 43993966508827, slopeGap := 66498533471372413, thresholdMinNMax := 1 },
    { suffixLength := 27, suffixSum := 50, suffixConstMax := 114463873667249, slopeGap := 138556127509300349, thresholdMinNMax := 1 },
    { suffixLength := 27, suffixSum := 52, suffixConstMax := 53544359779715, slopeGap := 570901691736867965, thresholdMinNMax := 1 },
    { suffixLength := 28, suffixSum := 47, suffixConstMax := 378439990565149, slopeGap := 1337216809815415, thresholdMinNMax := 51 },
    { suffixLength := 28, suffixSum := 48, suffixConstMax := 506151869748697, slopeGap := 19351615319297399, thresholdMinNMax := 5 },
    { suffixLength := 28, suffixSum := 49, suffixConstMax := 250342728597761, slopeGap := 55380412338261367, thresholdMinNMax := 1 },
    { suffixLength := 28, suffixSum := 50, suffixConstMax := 414653456888759, slopeGap := 127438006376189303, thresholdMinNMax := 1 },
    { suffixLength := 28, suffixSum := 51, suffixConstMax := 162511134249457, slopeGap := 271553194452045175, thresholdMinNMax := 1 },
    { suffixLength := 28, suffixSum := 52, suffixConstMax := 209039107644935, slopeGap := 559783570603756919, thresholdMinNMax := 1 },
    { suffixLength := 29, suffixSum := 49, suffixConstMax := 1397913579402679, slopeGap := 22026048938928229, thresholdMinNMax := 11 },
    { suffixLength := 29, suffixSum := 50, suffixConstMax := 1023678747375917, slopeGap := 94083642976856165, thresholdMinNMax := 2 },
    { suffixLength := 29, suffixSum := 51, suffixConstMax := 582222066005395, slopeGap := 238198831052712037, thresholdMinNMax := 1 },
    { suffixLength := 29, suffixSum := 52, suffixConstMax := 797794443246035, slopeGap := 526429207204423781, thresholdMinNMax := 1 },
    { suffixLength := 29, suffixSum := 54, suffixConstMax := 1436354525324683, slopeGap := 2255811464114694245, thresholdMinNMax := 1 },
    { suffixLength := 29, suffixSum := 60, suffixConstMax := 1208115598169941, slopeGap := 147523921044577413221, thresholdMinNMax := 1 },
    { suffixLength := 30, suffixSum := 51, suffixConstMax := 4394134001352743, slopeGap := 138135740854712623, thresholdMinNMax := 6 },
    { suffixLength := 30, suffixSum := 52, suffixConstMax := 3463088166298033, slopeGap := 426366117006424367, thresholdMinNMax := 2 },
    { suffixLength := 30, suffixSum := 53, suffixConstMax := 2438877824004185, slopeGap := 1002826869309847855, thresholdMinNMax := 1 },
    { suffixLength := 30, suffixSum := 54, suffixConstMax := 3642521573589205, slopeGap := 2155748373916694831, thresholdMinNMax := 1 },
    { suffixLength := 30, suffixSum := 55, suffixConstMax := 3295459358022575, slopeGap := 4461591383130388783, thresholdMinNMax := 1 },
    { suffixLength := 31, suffixSum := 52, suffixConstMax := 11737485813137803, slopeGap := 126176846412426125, thresholdMinNMax := 16 },
    { suffixLength := 31, suffixSum := 53, suffixConstMax := 12760350060331843, slopeGap := 702637598715849613, thresholdMinNMax := 4 },
    { suffixLength := 31, suffixSum := 54, suffixConstMax := 10327877081760067, slopeGap := 1855559103322696589, thresholdMinNMax := 1 },
    { suffixLength := 31, suffixSum := 55, suffixConstMax := 7541151039581621, slopeGap := 4161402112536390541, thresholdMinNMax := 1 },
    { suffixLength := 31, suffixSum := 56, suffixConstMax := 6321319126275713, slopeGap := 8773088130963778445, thresholdMinNMax := 1 },
    { suffixLength := 32, suffixSum := 54, suffixConstMax := 36495713423764657, slopeGap := 954991291540701863, thresholdMinNMax := 7 },
    { suffixLength := 32, suffixSum := 55, suffixConstMax := 29570542183017695, slopeGap := 3260834300754395815, thresholdMinNMax := 2 },
    { suffixLength := 32, suffixSum := 56, suffixConstMax := 30071179278923857, slopeGap := 7872520319181783719, thresholdMinNMax := 1 },
    { suffixLength := 32, suffixSum := 57, suffixConstMax := 19455827345322953, slopeGap := 17095892356036559527, thresholdMinNMax := 1 },
    { suffixLength := 32, suffixSum := 59, suffixConstMax := 30088713537744553, slopeGap := 72436124577165214375, thresholdMinNMax := 1 },
    { suffixLength := 33, suffixSum := 55, suffixConstMax := 110597543208194645, slopeGap := 559130865408411637, thresholdMinNMax := 34 },
    { suffixLength := 33, suffixSum := 56, suffixConstMax := 82592780976656291, slopeGap := 5170816883835799541, thresholdMinNMax := 3 },
    { suffixLength := 33, suffixSum := 57, suffixConstMax := 81050727047779739, slopeGap := 14394188920690575349, thresholdMinNMax := 2 },
    { suffixLength := 33, suffixSum := 58, suffixConstMax := 21155152623304933, slopeGap := 32840932994400126965, thresholdMinNMax := 1 },
    { suffixLength := 33, suffixSum := 59, suffixConstMax := 64072441061480971, slopeGap := 69734421141819230197, thresholdMinNMax := 1 },
    { suffixLength := 33, suffixSum := 61, suffixConstMax := 57959590357682851, slopeGap := 291095350026333849589, thresholdMinNMax := 1 },
    { suffixLength := 34, suffixSum := 57, suffixConstMax := 291990364183367719, slopeGap := 6289078614652622815, thresholdMinNMax := 9 },
    { suffixLength := 34, suffixSum := 58, suffixConstMax := 352548527386003951, slopeGap := 24735822688362174431, thresholdMinNMax := 3 },
    { suffixLength := 34, suffixSum := 59, suffixConstMax := 249311169356894077, slopeGap := 61629310835781277663, thresholdMinNMax := 1 },
    { suffixLength := 34, suffixSum := 60, suffixConstMax := 301394030819307947, slopeGap := 135416287130619484127, thresholdMinNMax := 1 },
    { suffixLength := 34, suffixSum := 61, suffixConstMax := 137282892928789313, slopeGap := 282990239720295897055, thresholdMinNMax := 1 },
    { suffixLength := 34, suffixSum := 62, suffixConstMax := 70167077336263561, slopeGap := 578138144899648722911, thresholdMinNMax := 1 },
    { suffixLength := 34, suffixSum := 65, suffixConstMax := 210171963091945961, slopeGap := 4710208817410588284895, thresholdMinNMax := 1 },
    { suffixLength := 35, suffixSum := 58, suffixConstMax := 1174428324757245841, slopeGap := 420491770248316829, thresholdMinNMax := 455 },
    { suffixLength := 35, suffixSum := 59, suffixConstMax := 1020842995939363609, slopeGap := 37313979917667420061, thresholdMinNMax := 5 },
    { suffixLength := 35, suffixSum := 60, suffixConstMax := 1132719929304787457, slopeGap := 111100956212505626525, thresholdMinNMax := 2 },
    { suffixLength := 35, suffixSum := 63, suffixConstMax := 234480090478643675, slopeGap := 1144118624340240517021, thresholdMinNMax := 1 },
    { suffixLength := 36, suffixSum := 60, suffixConstMax := 2329079599455588215, slopeGap := 38154963458164053719, thresholdMinNMax := 12 },
    { suffixLength := 36, suffixSum := 61, suffixConstMax := 2278620898643399681, slopeGap := 185728916047840466647, thresholdMinNMax := 3 },
    { suffixLength := 36, suffixSum := 62, suffixConstMax := 2974361554080292271, slopeGap := 480876821227193292503, thresholdMinNMax := 2 },
    { suffixLength := 36, suffixSum := 63, suffixConstMax := 3230464315314897101, slopeGap := 1071172631585898944215, thresholdMinNMax := 1 },
    { suffixLength := 37, suffixSum := 62, suffixConstMax := 12401208247781255359, slopeGap := 262038842964168574085, thresholdMinNMax := 8 },
    { suffixLength := 37, suffixSum := 63, suffixConstMax := 6706985348619811405, slopeGap := 852334653322874225797, thresholdMinNMax := 2 },
    { suffixLength := 37, suffixSum := 64, suffixConstMax := 3785320920790913497, slopeGap := 2032926274040285529221, thresholdMinNMax := 1 },
    { suffixLength := 37, suffixSum := 67, suffixConstMax := 1509608021354041459, slopeGap := 18561208964084043777157, thresholdMinNMax := 1 },
    { suffixLength := 38, suffixSum := 63, suffixConstMax := 32922840739448159753, slopeGap := 195820718533800070543, thresholdMinNMax := 28 },
    { suffixLength := 38, suffixSum := 64, suffixConstMax := 19934040004299492613, slopeGap := 1376412339251211373967, thresholdMinNMax := 3 },
    { suffixLength := 38, suffixSum := 65, suffixConstMax := 25427957111719465865, slopeGap := 3737595580686033980815, thresholdMinNMax := 2 },
    { suffixLength := 38, suffixSum := 67, suffixConstMax := 18570128811440273405, slopeGap := 17904695029294969621903, thresholdMinNMax := 1 },
    { suffixLength := 39, suffixSum := 65, suffixConstMax := 78990258985761280157, slopeGap := 1768053776318811515053, thresholdMinNMax := 8 },
    { suffixLength := 39, suffixSum := 67, suffixConstMax := 45197051241895504261, slopeGap := 15935153224927747156141, thresholdMinNMax := 1 },
    { suffixLength := 40, suffixSum := 66, suffixConstMax := 242361875129946090077, slopeGap := 581794846086789331463, thresholdMinNMax := 71 },
    { suffixLength := 40, suffixSum := 67, suffixConstMax := 231253490176820360959, slopeGap := 10026527811826079758855, thresholdMinNMax := 4 },
    { suffixLength := 40, suffixSum := 68, suffixConstMax := 150984907129482337757, slopeGap := 28915993743304660613639, thresholdMinNMax := 2 },
    { suffixLength := 40, suffixSum := 69, suffixConstMax := 43649764968133933729, slopeGap := 66694925606261822323207, thresholdMinNMax := 1 },
    { suffixLength := 40, suffixSum := 70, suffixConstMax := 227515886677442521019, slopeGap := 142252789332176145742343, thresholdMinNMax := 1 },
    { suffixLength := 41, suffixSum := 68, suffixConstMax := 496501955826985825703, slopeGap := 11190117503999658421781, thresholdMinNMax := 9 },
    { suffixLength := 41, suffixSum := 69, suffixConstMax := 701645518604605673141, slopeGap := 48969049366956820131349, thresholdMinNMax := 3 },
    { suffixLength := 41, suffixSum := 70, suffixConstMax := 426782888910950228491, slopeGap := 124526913092871143550485, thresholdMinNMax := 1 },
    { suffixLength := 41, suffixSum := 73, suffixConstMax := 517422579283884269515, slopeGap := 1182337005255671671418389, thresholdMinNMax := 1 },
    { suffixLength := 42, suffixSum := 70, suffixConstMax := 3027355446690721717595, slopeGap := 71349284374956136974911, thresholdMinNMax := 7 },
    { suffixLength := 42, suffixSum := 72, suffixConstMax := 1644880842238585973435, slopeGap := 524696466730442077489727, thresholdMinNMax := 1 },
    { suffixLength := 42, suffixSum := 74, suffixConstMax := 1179005941771951459921, slopeGap := 2338085196152385839548991, thresholdMinNMax := 1 },
    { suffixLength := 42, suffixSum := 77, suffixConstMax := 1293392476658851617833, slopeGap := 19263046670757194285435455, thresholdMinNMax := 1 },
    { suffixLength := 43, suffixSum := 71, suffixConstMax := 9026077145347930915769, slopeGap := 62932125673039764086461, thresholdMinNMax := 23 },
    { suffixLength := 43, suffixSum := 72, suffixConstMax := 4621585113474058321457, slopeGap := 365163580576697057763005, thresholdMinNMax := 3 },
    { suffixLength := 43, suffixSum := 73, suffixConstMax := 3077665016531522745623, slopeGap := 969626490384011645116093, thresholdMinNMax := 1 },
    { suffixLength := 43, suffixSum := 74, suffixConstMax := 2290804428120482103803, slopeGap := 2178552309998640819822269, thresholdMinNMax := 1 },
    { suffixLength := 44, suffixSum := 73, suffixConstMax := 24962674548065743979563, slopeGap := 491027831922776585935927, thresholdMinNMax := 9 },
    { suffixLength := 44, suffixSum := 74, suffixConstMax := 12792229526333339094853, slopeGap := 1699953651537405760642103, thresholdMinNMax := 2 },
    { suffixLength := 44, suffixSum := 75, suffixConstMax := 15791267209904264151715, slopeGap := 4117805290766664110054455, thresholdMinNMax := 1 },
    { suffixLength := 45, suffixSum := 74, suffixConstMax := 55891700460072549408595, slopeGap := 264157676153700583101605, thresholdMinNMax := 37 },
    { suffixLength := 45, suffixSum := 75, suffixConstMax := 52278892029381467698847, slopeGap := 2682009315382958932513957, thresholdMinNMax := 4 },
    { suffixLength := 45, suffixSum := 76, suffixConstMax := 40547024613965407225171, slopeGap := 7517712593841475631338661, thresholdMinNMax := 2 },
    { suffixLength := 45, suffixSum := 77, suffixConstMax := 46929804015686255036635, slopeGap := 17189119150758509028988069, thresholdMinNMax := 1 },
    { suffixLength := 46, suffixSum := 76, suffixConstMax := 35217657897778140589817, slopeGap := 3210324667690360098717167, thresholdMinNMax := 4 },
    { suffixLength := 47, suffixSum := 78, suffixConstMax := 389097352538963245843507, slopeGap := 19302380559988113693800909, thresholdMinNMax := 4 },
    { suffixLength := 47, suffixSum := 80, suffixConstMax := 217234895471476520864207, slopeGap := 135359259242992514465593805, thresholdMinNMax := 1 },
    { suffixLength := 48, suffixSum := 79, suffixConstMax := 1503287146918598807679131, slopeGap := 19221515452296207490805095, thresholdMinNMax := 14 },
    { suffixLength := 48, suffixSum := 80, suffixConstMax := 1824709803295731804655481, slopeGap := 96592767907632474672000359, thresholdMinNMax := 4 },
    { suffixLength := 48, suffixSum := 83, suffixConstMax := 829960709123898426398465, slopeGap := 1179790302282340215208734055, thresholdMinNMax := 1 },
    { suffixLength := 49, suffixSum := 81, suffixConstMax := 3978723259271827957436819, slopeGap := 135035798812224889653610549, thresholdMinNMax := 6 },
    { suffixLength := 49, suffixSum := 82, suffixConstMax := 2964298663612640274741319, slopeGap := 444520808633569958378391605, thresholdMinNMax := 2 },
    { suffixLength := 50, suffixSum := 82, suffixConstMax := 7624691557620525852518153, slopeGap := 95622386615329600236050591, thresholdMinNMax := 17 },
    { suffixLength := 50, suffixSum := 83, suffixConstMax := 19151152483482426079577653, slopeGap := 714592406258019737685612703, thresholdMinNMax := 5 },
    { suffixLength := 50, suffixSum := 85, suffixConstMax := 18025241352051055891753681, slopeGap := 4428412524114160562382985375, thresholdMinNMax := 1 },
    { suffixLength := 51, suffixSum := 84, suffixConstMax := 60861522724461350359229057, slopeGap := 905837179488678938157713885, thresholdMinNMax := 11 },
    { suffixLength := 51, suffixSum := 85, suffixConstMax := 34970781724152272719013267, slopeGap := 3381717258059439487955962333, thresholdMinNMax := 2 },
    { suffixLength := 52, suffixSum := 85, suffixConstMax := 155296934361795903960189323, slopeGap := 241631459895276264674893207, thresholdMinNMax := 105 },
    { suffixLength := 52, suffixSum := 86, suffixConstMax := 61977232420332465429682849, slopeGap := 5193391617036797364271390103, thresholdMinNMax := 3 },
    { suffixLength := 52, suffixSum := 89, suffixConstMax := 33192053893743101973982577, slopeGap := 74518033817018092758622346647, thresholdMinNMax := 1 },
    { suffixLength := 53, suffixSum := 87, suffixConstMax := 416529960468913632102216997, slopeGap := 5676654536827349893621176517, thresholdMinNMax := 13 },
    { suffixLength := 54, suffixSum := 89, suffixConstMax := 1071771967236720560191611377, slopeGap := 36837004239048134079249517135, thresholdMinNMax := 6 },
    { suffixLength := 54, suffixSum := 93, suffixConstMax := 569380905741982344776485135, slopeGap := 1225259441953013197982408772175, thresholdMinNMax := 1 },
    { suffixLength := 55, suffixSum := 90, suffixConstMax := 2255838145441618316905646933, slopeGap := 31282850202880064644204601069, thresholdMinNMax := 14 },
    { suffixLength := 55, suffixSum := 91, suffixConstMax := 4317423390432957387871920331, slopeGap := 189739175231408739831292501741, thresholdMinNMax := 4 },
    { suffixLength := 56, suffixSum := 92, suffixConstMax := 3200144585410510899810792673, slopeGap := 252304875637168869119701703879, thresholdMinNMax := 4 },
    { suffixLength := 56, suffixSum := 93, suffixConstMax := 1313257100578813516552161937, slopeGap := 886130175751283569868053306567, thresholdMinNMax := 1 },
    { suffixLength := 57, suffixSum := 93, suffixConstMax := 10096797385103663219349882499, slopeGap := 123089326797391906610753508949, thresholdMinNMax := 21 },
    { suffixLength := 57, suffixSum := 95, suffixConstMax := 20850165881733045856976184419, slopeGap := 3926041127482080111100863125077, thresholdMinNMax := 2 },
    { suffixLength := 58, suffixSum := 95, suffixConstMax := 80734831993578674915468056699, slopeGap := 1636918580620405121328963732223, thresholdMinNMax := 9 },
    { suffixLength := 59, suffixSum := 97, suffixConstMax := 100031620385435392658489911525, slopeGap := 9981358142774132969973704018173, thresholdMinNMax := 3 },
    { suffixLength := 60, suffixSum := 98, suffixConstMax := 222729093688293683219161101745, slopeGap := 9661664824670728485973860768503, thresholdMinNMax := 7 },
    { suffixLength := 60, suffixSum := 99, suffixConstMax := 977342080109203483623055872463, slopeGap := 50226484031974069333868363340535, thresholdMinNMax := 4 },
    { suffixLength := 60, suffixSum := 100, suffixConstMax := 568500370069658957698027660721, slopeGap := 131356122446580751029657368484599, thresholdMinNMax := 1 },
    { suffixLength := 60, suffixSum := 101, suffixConstMax := 840454936109936762876901169217, slopeGap := 293615399275794114421235378772727, thresholdMinNMax := 1 },
    { suffixLength := 62, suffixSum := 101, suffixConstMax := 4957196335257625856043056624773, slopeGap := 46390164214733215525870244344495, thresholdMinNMax := 21 },
    { suffixLength := 62, suffixSum := 106, suffixConstMax := 2575982452278393375630161578009, slopeGap := 10106465327625961745803706882208431, thresholdMinNMax := 1 },
    { suffixLength := 63, suffixSum := 103, suffixConstMax := 16098448575042543939315295615091, slopeGap := 463689046302626373360766753609741, thresholdMinNMax := 7 },
    { suffixLength := 64, suffixSum := 104, suffixConstMax := 25855217820334794697643496486545, slopeGap := 92992924274172212949676178524199, thresholdMinNMax := 66 },
    { suffixLength := 65, suffixSum := 106, suffixConstMax := 140100715622702609348078536725923, slopeGap := 2875127202089930453114276700182645, thresholdMinNMax := 10 },
    { suffixLength := 67, suffixSum := 109, suffixConstMax := 1767064606418335437404575959267739, slopeGap := 15491551101739718820967497643203613, thresholdMinNMax := 20 },
    { suffixLength := 69, suffixSum := 115, suffixConstMax := 8616427811966865412251445647051979, slopeGap := 4708645195426305782495544248502516997, thresholdMinNMax := 1 },
    { suffixLength := 70, suffixSum := 114, suffixConstMax := 61088831099633728014148765041686411, slopeGap := 833655628429758618448562142704105231, thresholdMinNMax := 12 },
    { suffixLength := 85, suffixSum := 140, suffixConstMax := 844544140631857719291053854540292125006447, slopeGap := 152222070883981847854611553742756710027718981, thresholdMinNMax := 1 }
  ]

def a0SemanticSuffixPairCertificatesT14RowCount : Nat :=
  a0SemanticSuffixPairCertificatesT14.length

set_option linter.style.nativeDecide false in
theorem a0SemanticSuffixPairCertificatesT14_rowCount :
    a0SemanticSuffixPairCertificatesT14RowCount = 351 := by
  native_decide

set_option linter.style.nativeDecide false in
theorem a0SemanticSuffixPairCertificatesT14_allValid :
    A0SemanticSuffixPairCertificate.allValidAt455Bool
      a0SemanticSuffixPairCertificatesT14 = true := by
  native_decide

set_option linter.style.nativeDecide false in
theorem a0SemanticSuffixPairCertificatesT14_allValidAtCutoff455 :
    A0SemanticSuffixPairCertificate.allValidAtCutoffBool 455
      a0SemanticSuffixPairCertificatesT14 = true := by
  native_decide

def a0SemanticSuffixPairCertificatesT14TableThresholdMax : Nat :=
  a0SemanticSuffixPairCertificatesT14.foldl
    (fun acc row => max acc row.thresholdMinNMax)
    0

set_option linter.style.nativeDecide false in
theorem a0SemanticSuffixPairCertificatesT14_matches_summary :
    a0SemanticSuffixPairCertificatesT14RowCount = 351
      ∧ a0SemanticSuffixPairCertificatesT14RowCount
        = a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateRowsMax
      ∧ a0SemanticSuffixPairCertificatesT14TableThresholdMax = 455
      ∧ a0SemanticSuffixPairCertificatesT14TableThresholdMax
        = a0SemanticDropWordAuditV2Lt8Cap100SuffixPairCertificateThresholdMax := by
  native_decide

theorem hasStrictDescent_of_mem_a0SemanticSuffixPairCertificatesT14
    {P : A0SemanticSuffixPairCertificate} {suffix : List ℕ} {n : ℕ}
    (hmem : P ∈ a0SemanticSuffixPairCertificatesT14)
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ suffix) n)
    (hlen : suffix.length = P.suffixLength)
    (hsum : suffix.sum = P.suffixSum)
    (hconst : syracuseWordConst suffix ≤ P.suffixConstMax) :
    HasStrictDescent n := by
  have hP :
      P.ValidAt455 :=
    A0SemanticSuffixPairCertificate.validAt455_of_mem_of_allValidAt455Bool
      a0SemanticSuffixPairCertificatesT14_allValid hmem
  exact
    A0SemanticSuffixPairCertificate.hasStrictDescent_of_validAt455
      hn hodd hn1 hmatch hP hlen hsum hconst

/--
Proof-facing assignment of one concrete semantic-drop suffix to a row of the
T14 pair-compressed table.

This is the object a future generated suffix-cover map should produce.  It is
still local to a concrete suffix and does not assert that all future sources
produce such suffixes.
-/
structure A0SemanticSuffixT14PairCover where
  suffix : List ℕ
  pair : A0SemanticSuffixPairCertificate
  pairMem : pair ∈ a0SemanticSuffixPairCertificatesT14
  lengthEq : suffix.length = pair.suffixLength
  sumEq : suffix.sum = pair.suffixSum
  constLe : syracuseWordConst suffix ≤ pair.suffixConstMax

def A0SemanticSuffixT14PairCover.toGeneric
    (C : A0SemanticSuffixT14PairCover) :
    A0SemanticSuffixPairCover a0SemanticSuffixPairCertificatesT14 :=
  { suffix := C.suffix
    pair := C.pair
    pairMem := C.pairMem
    lengthEq := C.lengthEq
    sumEq := C.sumEq
    constLe := C.constLe }

theorem hasStrictDescent_of_a0SemanticSuffixT14PairCover
    {C : A0SemanticSuffixT14PairCover} {n : ℕ}
    (hn : 0 < n) (hodd : Odd n) (hn1 : n ≠ 1)
    (hmatch :
      SyracuseWordMatchesFrom (a0SemanticDropCommonPrefix ++ C.suffix) n) :
    HasStrictDescent n := by
  have hmatchGeneric :
      SyracuseWordMatchesFrom
        (a0SemanticDropCommonPrefix ++ C.toGeneric.suffix) n := by
    simpa [A0SemanticSuffixT14PairCover.toGeneric] using hmatch
  exact
    hasStrictDescent_of_a0SemanticSuffixPairCoverAtCutoff
    (C := C.toGeneric)
    a0SemanticSuffixPairCertificatesT14_allValidAtCutoff455
    (fun _m hm hoddm hm1 hltm =>
      hasStrictDescent_of_odd_lt_455 hm hoddm hm1 hltm)
    hn hodd hn1 hmatchGeneric

/--
Proof-facing source-level cover object for the A0 semantic-drop path.

Providing this object for a concrete source `n` is enough to prove strict
descent from `n`: it packages positivity/oddness/nontriviality, the concrete
suffix-to-T14-pair cover, and the actual common-prefix valuation-word match.
-/
structure A0SemanticDropSourceT14PairCover (n : ℕ) where
  positive : 0 < n
  odd : Odd n
  notOne : n ≠ 1
  suffixCover : A0SemanticSuffixT14PairCover
  wordMatch :
    SyracuseWordMatchesFrom
      (a0SemanticDropCommonPrefix ++ suffixCover.suffix) n

theorem hasStrictDescent_of_a0SemanticDropSourceT14PairCover
    {n : ℕ} (C : A0SemanticDropSourceT14PairCover n) :
    HasStrictDescent n :=
  hasStrictDescent_of_a0SemanticSuffixT14PairCover
    C.positive C.odd C.notOne C.wordMatch

def a0SemanticDropTableSpecT14 : A0SemanticDropTableSpec :=
  { rows := a0SemanticSuffixPairCertificatesT14
    cutoff := 455
    rowsValid := a0SemanticSuffixPairCertificatesT14_allValidAtCutoff455
    smallStrictDescent := by
      intro m hm hoddm hm1 hltm
      exact hasStrictDescent_of_odd_lt_455 hm hoddm hm1 hltm }

theorem hasStrictDescent_of_a0SemanticDropTableSpecT14_sourceCover
    {n : ℕ} (C : a0SemanticDropTableSpecT14.SourceCover n) :
    HasStrictDescent n :=
  A0SemanticDropTableSpec.hasStrictDescent_of_sourceCover
    a0SemanticDropTableSpecT14 C

theorem hasStrictDescent_of_a0SemanticDropTableSpecT14_endpointSuffixCover
    {t : ℕ} (C : a0SemanticDropTableSpecT14.EndpointSuffixCover t) :
    HasStrictDescent (103 + 256 * t) :=
  A0SemanticDropTableSpec.hasStrictDescent_of_endpointSuffixCover
    a0SemanticDropTableSpecT14 C

/--
Finite accounting summary for the observed suffix-to-T14-pair coverage audit.

Rows here record coverage of already observed finite-prefix suffixes by the
T14 pair table.  They are not a parametric theorem that future prefixes or all
integer orbits are covered.
-/
structure A0SemanticSuffixT14PairCoverageSummary where
  prefixBits : ℕ
  dropSamples : ℕ
  distinctSuffixes : ℕ
  phaseWordGroups : ℕ
  coveringPairRows : ℕ
  coveredSuffixRows : ℕ
  uncoveredSuffixRows : ℕ
  coveredDropSamples : ℕ
  coveredPhaseWordGroups : ℕ
  missingPairFailures : ℕ
  constBoundFailures : ℕ
  thresholdBoundFailures : ℕ
  deriving Repr, DecidableEq

def a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100 :
    List A0SemanticSuffixT14PairCoverageSummary :=
  [
    { prefixBits := 12, dropSamples := 14668, distinctSuffixes := 2287,
      phaseWordGroups := 9148, coveringPairRows := 351,
      coveredSuffixRows := 2287, uncoveredSuffixRows := 0,
      coveredDropSamples := 14668, coveredPhaseWordGroups := 9148,
      missingPairFailures := 0, constBoundFailures := 0,
      thresholdBoundFailures := 0 },
    { prefixBits := 13, dropSamples := 29288, distinctSuffixes := 4230,
      phaseWordGroups := 16920, coveringPairRows := 351,
      coveredSuffixRows := 4230, uncoveredSuffixRows := 0,
      coveredDropSamples := 29288, coveredPhaseWordGroups := 16920,
      missingPairFailures := 0, constBoundFailures := 0,
      thresholdBoundFailures := 0 },
    { prefixBits := 14, dropSamples := 58532, distinctSuffixes := 7831,
      phaseWordGroups := 31324, coveringPairRows := 351,
      coveredSuffixRows := 7831, uncoveredSuffixRows := 0,
      coveredDropSamples := 58532, coveredPhaseWordGroups := 31324,
      missingPairFailures := 0, constBoundFailures := 0,
      thresholdBoundFailures := 0 }
  ]

def a0SemanticSuffixT14PairCoverageDropSamplesTotal : ℕ :=
  a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.dropSamples)
    0

def a0SemanticSuffixT14PairCoverageDistinctSuffixesTotal : ℕ :=
  a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.distinctSuffixes)
    0

def a0SemanticSuffixT14PairCoverageCoveredSuffixRowsTotal : ℕ :=
  a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.coveredSuffixRows)
    0

def a0SemanticSuffixT14PairCoverageUncoveredSuffixRowsTotal : ℕ :=
  a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.uncoveredSuffixRows)
    0

def a0SemanticSuffixT14PairCoverageCoveredDropSamplesTotal : ℕ :=
  a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.coveredDropSamples)
    0

def a0SemanticSuffixT14PairCoveragePhaseWordGroupsTotal : ℕ :=
  a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.phaseWordGroups)
    0

def a0SemanticSuffixT14PairCoverageCoveredPhaseWordGroupsTotal : ℕ :=
  a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.coveredPhaseWordGroups)
    0

def a0SemanticSuffixT14PairCoverageFailureTotal : ℕ :=
  a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.foldl
    (fun acc row =>
      acc
        + row.uncoveredSuffixRows
        + row.missingPairFailures
        + row.constBoundFailures
        + row.thresholdBoundFailures)
    0

def a0SemanticSuffixT14PairCoveragePairRowsMax : ℕ :=
  a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => max acc row.coveringPairRows)
    0

set_option linter.style.nativeDecide false in
theorem a0SemanticSuffixT14PairCoverageV2Lt8Cap100_summary :
    a0SemanticSuffixT14PairCoverageSummariesV2Lt8Cap100.length = 3
      ∧ a0SemanticSuffixT14PairCoveragePairRowsMax = 351
      ∧ a0SemanticSuffixT14PairCoveragePairRowsMax
        = a0SemanticSuffixPairCertificatesT14RowCount
      ∧ a0SemanticSuffixT14PairCoverageDropSamplesTotal = 102488
      ∧ a0SemanticSuffixT14PairCoverageDropSamplesTotal
        = a0SemanticReplayV2Lt8Cap100DropSamplesTotal
      ∧ a0SemanticSuffixT14PairCoverageDistinctSuffixesTotal = 14348
      ∧ a0SemanticSuffixT14PairCoverageDistinctSuffixesTotal
        = a0SemanticDropWordAuditV2Lt8Cap100DistinctSuffixesTotal
      ∧ a0SemanticSuffixT14PairCoverageCoveredSuffixRowsTotal = 14348
      ∧ a0SemanticSuffixT14PairCoverageCoveredSuffixRowsTotal
        = a0SemanticSuffixT14PairCoverageDistinctSuffixesTotal
      ∧ a0SemanticSuffixT14PairCoverageUncoveredSuffixRowsTotal = 0
      ∧ a0SemanticSuffixT14PairCoverageCoveredDropSamplesTotal = 102488
      ∧ a0SemanticSuffixT14PairCoverageCoveredDropSamplesTotal
        = a0SemanticSuffixT14PairCoverageDropSamplesTotal
      ∧ a0SemanticSuffixT14PairCoveragePhaseWordGroupsTotal = 57392
      ∧ a0SemanticSuffixT14PairCoverageCoveredPhaseWordGroupsTotal = 57392
      ∧ a0SemanticSuffixT14PairCoverageCoveredPhaseWordGroupsTotal
        = a0SemanticSuffixT14PairCoveragePhaseWordGroupsTotal
      ∧ a0SemanticSuffixT14PairCoverageFailureTotal = 0 := by
  native_decide

/--
Finite accounting summary for source-level A0 semantic-drop coverage.

This counts observed finite-prefix sources whose semantic replay reached a
drop and whose observed word has the common prefix and a T14-covered suffix.
It does not assert that all future sources have such a cover.
-/
structure A0SemanticDropSourceT14CoverageSummary where
  prefixBits : ℕ
  dropSamples : ℕ
  coveredSourceSamples : ℕ
  uncoveredSourceSamples : ℕ
  commonPrefixFailures : ℕ
  suffixPairCoverageFailures : ℕ
  deriving Repr, DecidableEq

def a0SemanticDropSourceT14CoverageSummariesV2Lt8Cap100 :
    List A0SemanticDropSourceT14CoverageSummary :=
  [
    { prefixBits := 12, dropSamples := 14668,
      coveredSourceSamples := 14668, uncoveredSourceSamples := 0,
      commonPrefixFailures := 0, suffixPairCoverageFailures := 0 },
    { prefixBits := 13, dropSamples := 29288,
      coveredSourceSamples := 29288, uncoveredSourceSamples := 0,
      commonPrefixFailures := 0, suffixPairCoverageFailures := 0 },
    { prefixBits := 14, dropSamples := 58532,
      coveredSourceSamples := 58532, uncoveredSourceSamples := 0,
      commonPrefixFailures := 0, suffixPairCoverageFailures := 0 }
  ]

def a0SemanticDropSourceT14CoverageDropSamplesTotal : ℕ :=
  a0SemanticDropSourceT14CoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.dropSamples)
    0

def a0SemanticDropSourceT14CoverageCoveredSamplesTotal : ℕ :=
  a0SemanticDropSourceT14CoverageSummariesV2Lt8Cap100.foldl
    (fun acc row => acc + row.coveredSourceSamples)
    0

def a0SemanticDropSourceT14CoverageFailureTotal : ℕ :=
  a0SemanticDropSourceT14CoverageSummariesV2Lt8Cap100.foldl
    (fun acc row =>
      acc
        + row.uncoveredSourceSamples
        + row.commonPrefixFailures
        + row.suffixPairCoverageFailures)
    0

theorem a0SemanticDropSourceT14CoverageV2Lt8Cap100_summary :
    a0SemanticDropSourceT14CoverageSummariesV2Lt8Cap100.length = 3
      ∧ a0SemanticDropSourceT14CoverageDropSamplesTotal = 102488
      ∧ a0SemanticDropSourceT14CoverageDropSamplesTotal
        = a0SemanticReplayV2Lt8Cap100DropSamplesTotal
      ∧ a0SemanticDropSourceT14CoverageCoveredSamplesTotal = 102488
      ∧ a0SemanticDropSourceT14CoverageCoveredSamplesTotal
        = a0SemanticDropSourceT14CoverageDropSamplesTotal
      ∧ a0SemanticDropSourceT14CoverageFailureTotal = 0 := by
  norm_num [
    a0SemanticDropSourceT14CoverageSummariesV2Lt8Cap100,
    a0SemanticDropSourceT14CoverageDropSamplesTotal,
    a0SemanticDropSourceT14CoverageCoveredSamplesTotal,
    a0SemanticDropSourceT14CoverageFailureTotal,
    a0SemanticReplayV2Lt8Cap100DropSamplesTotal,
    a0SemanticReplaySummariesV2Lt8Cap100]

/--
Compact parameterized replay/certificate summary for later-prefix audits.

This avoids importing very large suffix tables while keeping the exact finite
parameters visible.  It remains a finite-prefix audit summary only.
-/
structure A0SemanticReplayParamSummary where
  prefixBits : ℕ
  stepCap : ℕ
  valuationCap : ℕ
  certificateCutoff : ℕ
  totalSamples : ℕ
  dropSamples : ℕ
  returnSamples : ℕ
  valuationTailSamples : ℕ
  stepTailSamples : ℕ
  dropStepMax : ℕ
  returnStepMax : ℕ
  distinctSuffixes : ℕ
  pairRows : ℕ
  thresholdMax : ℕ
  commonPrefixFailures : ℕ
  pairCertificateFailures : ℕ
  sourceCoveredSamples : ℕ
  sourceCoverageFailures : ℕ
  deriving Repr, DecidableEq

def a0SemanticReplayT19A20Cap200Cutoff648 :
    A0SemanticReplayParamSummary :=
  { prefixBits := 19
    stepCap := 200
    valuationCap := 20
    certificateCutoff := 648
    totalSamples := 2088960
    dropSamples := 1869500
    returnSamples := 219460
    valuationTailSamples := 0
    stepTailSamples := 0
    dropStepMax := 138
    returnStepMax := 105
    distinctSuffixes := 156188
    pairRows := 749
    thresholdMax := 647
    commonPrefixFailures := 0
    pairCertificateFailures := 0
    sourceCoveredSamples := 1869500
    sourceCoverageFailures := 0 }

theorem a0SemanticReplayT19A20Cap200Cutoff648_summary :
    a0SemanticReplayT19A20Cap200Cutoff648.totalSamples = 2088960
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.dropSamples = 1869500
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.returnSamples = 219460
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.valuationTailSamples = 0
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.stepTailSamples = 0
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.dropSamples
          + a0SemanticReplayT19A20Cap200Cutoff648.returnSamples
        = a0SemanticReplayT19A20Cap200Cutoff648.totalSamples
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.distinctSuffixes = 156188
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.pairRows = 749
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.thresholdMax = 647
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.thresholdMax
        < a0SemanticReplayT19A20Cap200Cutoff648.certificateCutoff
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.commonPrefixFailures = 0
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.pairCertificateFailures = 0
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.sourceCoveredSamples
        = a0SemanticReplayT19A20Cap200Cutoff648.dropSamples
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.sourceCoverageFailures = 0 := by
  norm_num [a0SemanticReplayT19A20Cap200Cutoff648]

def a0SemanticReplayT20A20Cap200Cutoff648 :
    A0SemanticReplayParamSummary :=
  { prefixBits := 20
    stepCap := 200
    valuationCap := 20
    certificateCutoff := 648
    totalSamples := 4177920
    dropSamples := 3739212
    returnSamples := 438708
    valuationTailSamples := 0
    stepTailSamples := 0
    dropStepMax := 138
    returnStepMax := 105
    distinctSuffixes := 284363
    pairRows := 842
    thresholdMax := 647
    commonPrefixFailures := 0
    pairCertificateFailures := 0
    sourceCoveredSamples := 3739212
    sourceCoverageFailures := 0 }

theorem a0SemanticReplayT20A20Cap200Cutoff648_summary :
    a0SemanticReplayT20A20Cap200Cutoff648.totalSamples = 4177920
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.dropSamples = 3739212
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.returnSamples = 438708
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.valuationTailSamples = 0
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.stepTailSamples = 0
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.dropSamples
          + a0SemanticReplayT20A20Cap200Cutoff648.returnSamples
        = a0SemanticReplayT20A20Cap200Cutoff648.totalSamples
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.distinctSuffixes = 284363
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.pairRows = 842
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.thresholdMax = 647
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.thresholdMax
        < a0SemanticReplayT20A20Cap200Cutoff648.certificateCutoff
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.commonPrefixFailures = 0
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.pairCertificateFailures = 0
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.sourceCoveredSamples
        = a0SemanticReplayT20A20Cap200Cutoff648.dropSamples
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.sourceCoverageFailures = 0 := by
  norm_num [a0SemanticReplayT20A20Cap200Cutoff648]

theorem a0SemanticReplayT19T20A20Cap200Cutoff648_stable_bounds :
    a0SemanticReplayT20A20Cap200Cutoff648.thresholdMax
        = a0SemanticReplayT19A20Cap200Cutoff648.thresholdMax
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.dropStepMax
        = a0SemanticReplayT19A20Cap200Cutoff648.dropStepMax
      ∧ a0SemanticReplayT20A20Cap200Cutoff648.returnStepMax
        = a0SemanticReplayT19A20Cap200Cutoff648.returnStepMax
      ∧ a0SemanticReplayT19A20Cap200Cutoff648.pairRows
        < a0SemanticReplayT20A20Cap200Cutoff648.pairRows := by
  norm_num [a0SemanticReplayT19A20Cap200Cutoff648,
    a0SemanticReplayT20A20Cap200Cutoff648]

theorem a0CompletePrefixSummariesV2Lt8_coverage_total_zero :
    a0CompletePrefixSummariesV2Lt8CoverageFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8CoverageFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

theorem a0CompletePrefixSummariesV2Lt8_arithmetic_certificate_total_zero :
    a0CompletePrefixSummariesV2Lt8ArithmeticCertificateFailureTotal = 0 := by
  norm_num [a0CompletePrefixSummariesV2Lt8ArithmeticCertificateFailureTotal,
    a0CompletePrefixSummariesV2Lt8]

end Generated
end CollatzShadowing
