/-
Finite Collatz-Wielandt certificate API for Phase 8.6 of `TODO.md`.

This file records the certificate shape that the finite operator
matrices will use before any later bridge to a formal spectral-radius
statement.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-05-11.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic
import CollatzShadowing.Operator

namespace CollatzShadowing

open scoped ENNReal NNReal

/-!
## Finite Collatz-Wielandt certificates

For a non-negative finite matrix, the computational certificate used in
Phase 7 has the pointwise form `(M.mulVec v) i ≤ alpha * v i` for a
positive vector `v`. This is the first Lean target; a later task can
connect it to Mathlib's spectral language if needed.
-/

/-- Positive vector certificate on an arbitrary finite state space. -/
structure FiniteCWBasis (ι : Type*) where
  vector : ι → NNReal
  positive : ∀ i, 0 < vector i

/-- Pointwise Collatz-Wielandt-style upper certificate on a finite state space. -/
def FiniteCWCertificate {ι : Type*} [Fintype ι]
    (M : Matrix ι ι NNReal)
    (basis : FiniteCWBasis ι)
    (alpha : NNReal) : Prop :=
  ∀ i, Matrix.mulVec M basis.vector i ≤ alpha * basis.vector i

/-- A packaged finite matrix bound certificate on an arbitrary finite state space. -/
structure FiniteMatrixBoundCertificate (ι : Type*) [Fintype ι] where
  matrix : Matrix ι ι NNReal
  basis : FiniteCWBasis ι
  alpha : NNReal
  certificate : FiniteCWCertificate matrix basis alpha

/--
One exact cleared-denominator row inequality:

`lhsNum / lhsDen ≤ (alphaNum / alphaDen) * vector`.

The field `cleared` is the denominator-cleared natural-number
inequality verified by generated arithmetic certificates.
-/
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

/-- A list-level exact arithmetic certificate for a finite CW check. -/
structure ClearedCWCertificateSummary where
  stateCount : ℕ
  alpha : ProbabilityEntry
  rows : List ClearedCWRowBound
  row_count : rows.length = stateCount

/--
A cleared row certificate together with the semantic equalities needed
to identify it with one row of `M.mulVec basis.vector`.
-/
structure EvaluatedCWRowBound {ι : Type*} [Fintype ι]
    (M : Matrix ι ι NNReal)
    (basis : FiniteCWBasis ι)
    (alpha : NNReal)
    (i : ι) where
  row : ClearedCWRowBound
  lhs_eq :
    Matrix.mulVec M basis.vector i =
      (row.lhsNum : NNReal) / (row.lhsDen : NNReal)
  vector_eq : basis.vector i = (row.vector : NNReal)
  alpha_eq :
    alpha = (row.alphaNum : NNReal) / (row.alphaDen : NNReal)

/-- Convert a cleared natural-number row certificate into an `NNReal` inequality. -/
theorem ClearedCWRowBound.toNNRealInequality (r : ClearedCWRowBound) :
    (r.lhsNum : NNReal) / (r.lhsDen : NNReal) ≤
      ((r.alphaNum : NNReal) / (r.alphaDen : NNReal)) * (r.vector : NNReal) := by
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_mul]
  have h_lhsDen_pos : (0 : ℝ) < r.lhsDen := by exact_mod_cast r.lhsDen_pos
  have h_alphaDen_pos : (0 : ℝ) < r.alphaDen := by exact_mod_cast r.alphaDen_pos
  have h_cleared :
      (r.lhsNum : ℝ) * r.alphaDen ≤ r.alphaNum * r.vector * r.lhsDen := by
    exact_mod_cast r.cleared
  field_simp [h_lhsDen_pos.ne', h_alphaDen_pos.ne']
  nlinarith [h_cleared, h_lhsDen_pos, h_alphaDen_pos]

/-- An evaluated cleared row gives the corresponding pointwise CW inequality. -/
theorem EvaluatedCWRowBound.toCWRow {ι : Type*} [Fintype ι]
    {M : Matrix ι ι NNReal}
    {basis : FiniteCWBasis ι}
    {alpha : NNReal}
    {i : ι}
    (r : EvaluatedCWRowBound M basis alpha i) :
    Matrix.mulVec M basis.vector i ≤ alpha * basis.vector i := by
  calc
    Matrix.mulVec M basis.vector i =
        (r.row.lhsNum : NNReal) / (r.row.lhsDen : NNReal) := r.lhs_eq
    _ ≤ ((r.row.alphaNum : NNReal) / (r.row.alphaDen : NNReal)) *
        (r.row.vector : NNReal) := r.row.toNNRealInequality
    _ = alpha * basis.vector i := by
      rw [← r.alpha_eq, ← r.vector_eq]

/--
Convert evaluated cleared row certificates for all rows into a finite
Collatz-Wielandt certificate.
-/
theorem finiteCWCertificateOfEvaluatedRows {ι : Type*} [Fintype ι]
    {M : Matrix ι ι NNReal}
    {basis : FiniteCWBasis ι}
    {alpha : NNReal}
    (rows : ∀ i, EvaluatedCWRowBound M basis alpha i) :
    FiniteCWCertificate M basis alpha := by
  intro i
  exact (rows i).toCWRow

@[simp] theorem Matrix.mulVec_add_NNReal {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι NNReal)
    (v : ι → NNReal)
    (i : ι) :
    Matrix.mulVec (A + B) v i =
      Matrix.mulVec A v i + Matrix.mulVec B v i := by
  simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, add_mul]

/--
Finite Collatz-Wielandt certificates are additive for a shared positive
basis. This is the finite `core + tail` bound used by the operator
decomposition layer.
-/
theorem FiniteCWCertificate.add {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι NNReal}
    {basis : FiniteCWBasis ι}
    {alpha beta : NNReal}
    (hA : FiniteCWCertificate A basis alpha)
    (hB : FiniteCWCertificate B basis beta) :
    FiniteCWCertificate (A + B) basis (alpha + beta) := by
  intro i
  calc
    Matrix.mulVec (A + B) basis.vector i =
        Matrix.mulVec A basis.vector i + Matrix.mulVec B basis.vector i := by
      simp
    _ ≤ alpha * basis.vector i + beta * basis.vector i :=
      add_le_add (hA i) (hB i)
    _ = (alpha + beta) * basis.vector i := by
      rw [add_mul]

/--
If a displayed full matrix is definitionally or propositionally the sum
of core and tail matrices, rowwise certificates for the parts give a
rowwise certificate for the full matrix.
-/
theorem finiteCWCertificateOfSumEq {ι : Type*} [Fintype ι]
    {full core tail : Matrix ι ι NNReal}
    {basis : FiniteCWBasis ι}
    {alphaCore alphaTail : NNReal}
    (hFull : full = core + tail)
    (hCore : FiniteCWCertificate core basis alphaCore)
    (hTail : FiniteCWCertificate tail basis alphaTail) :
    FiniteCWCertificate full basis (alphaCore + alphaTail) := by
  rw [hFull]
  exact hCore.add hTail

/-- The all-ones vector is positive on any finite state space. -/
def finiteOnesBasis (ι : Type*) : FiniteCWBasis ι where
  vector := fun _ => 1
  positive := by
    intro i
    norm_num

/-- Baseline finite certificate for the zero matrix. -/
def finiteZeroMatrixBoundCertificate (ι : Type*) [Fintype ι] :
    FiniteMatrixBoundCertificate ι where
  matrix := 0
  basis := finiteOnesBasis ι
  alpha := 0
  certificate := by
    intro i
    simp [Matrix.mulVec, finiteOnesBasis]

/-!
## First spectral-radius bridge

The finite CW certificates above are rowwise.  The first bridge to
Mathlib's spectral language records the standard norm-theoretic step:
under the matrix `ℓ∞` operator norm, `spectralRadius ℝ M ≤ ‖M‖`.
The weighted Collatz-Wielandt bridge below targets the explicit row-sum
bound used here.
-/

/-- Maximal row sum of entry norms for a real square matrix. -/
noncomputable def matrixLinftyOpNNNorm {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) : NNReal :=
  (Finset.univ : Finset ι).sup fun i => ∑ j, ‖M i j‖₊

/--
If the explicit `ℓ∞` row-sum norm of a real finite matrix is at most
`alpha`, then Mathlib's real spectral radius is at most `alpha`.
-/
theorem spectralRadius_le_of_matrixLinftyOpNNNorm_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (alpha : NNReal)
    (hM : matrixLinftyOpNNNorm M ≤ alpha) :
    spectralRadius ℝ M ≤ (alpha : ℝ≥0∞) := by
  letI := Matrix.linftyOpNormedAddCommGroup (m := ι) (n := ι) (α := ℝ)
  letI := Matrix.linftyOpNormedSpace (m := ι) (n := ι) (R := ℝ) (α := ℝ)
  letI := Matrix.linftyOpNormedRing (n := ι) (α := ℝ)
  letI := Matrix.linftyOpNormedAlgebra (n := ι) (R := ℝ) (α := ℝ)
  have hnorm : ‖M‖₊ ≤ alpha := by
    rw [Matrix.linfty_opNNNorm_def]
    simpa [matrixLinftyOpNNNorm] using hM
  exact (spectrum.spectralRadius_le_nnnorm (𝕜 := ℝ) (a := M)).trans
    (ENNReal.coe_le_coe.mpr hnorm)

/--
Rowwise bounds on the sums of entry norms imply the corresponding
Mathlib spectral-radius bound.
-/
theorem spectralRadius_le_of_forall_row_nnnorm_sum_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (alpha : NNReal)
    (hrow : ∀ i, (∑ j, ‖M i j‖₊) ≤ alpha) :
    spectralRadius ℝ M ≤ (alpha : ℝ≥0∞) := by
  refine spectralRadius_le_of_matrixLinftyOpNNNorm_le M alpha ?_
  unfold matrixLinftyOpNNNorm
  exact Finset.sup_le fun i _hi => hrow i

/-- Realification of a finite matrix with non-negative entries. -/
noncomputable def nnrealMatrixToReal {ι : Type*}
    (M : Matrix ι ι NNReal) : Matrix ι ι ℝ :=
  fun i j => (M i j : ℝ)

/--
A plain row-sum bound for a finite non-negative matrix gives a Mathlib
real spectral-radius bound for its realification.
-/
theorem spectralRadius_le_of_forall_nnreal_row_sum_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι NNReal) (alpha : NNReal)
    (hrow : ∀ i, (∑ j, M i j) ≤ alpha) :
    spectralRadius ℝ (nnrealMatrixToReal M) ≤ (alpha : ℝ≥0∞) := by
  refine spectralRadius_le_of_forall_row_nnnorm_sum_le
    (nnrealMatrixToReal M) alpha ?_
  intro i
  simpa [nnrealMatrixToReal, NNReal.nnnorm_eq] using hrow i

/--
The diagonal unit whose entries are the positive Collatz-Wielandt
basis coordinates.
-/
noncomputable def finiteCWDiagonalUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (basis : FiniteCWBasis ι) : (Matrix ι ι ℝ)ˣ where
  val := Matrix.diagonal fun i => (basis.vector i : ℝ)
  inv := Matrix.diagonal fun i => ((basis.vector i : ℝ)⁻¹)
  val_inv := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [ne_of_gt (by exact_mod_cast basis.positive i)]
    · simp [h]
  inv_val := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [ne_of_gt (by exact_mod_cast basis.positive i)]
    · simp [h]

/--
The real weighted conjugate `D⁻¹ M D`, written entrywise so its row
sums are exactly the Collatz-Wielandt ratios.
-/
noncomputable def finiteCWWeightedRealConjugate {ι : Type*}
    (M : Matrix ι ι NNReal) (basis : FiniteCWBasis ι) : Matrix ι ι ℝ :=
  fun i j => ((basis.vector i : ℝ)⁻¹) * (M i j : ℝ) * (basis.vector j : ℝ)

lemma finiteCWWeightedRealConjugate_nonneg {ι : Type*}
    (M : Matrix ι ι NNReal) (basis : FiniteCWBasis ι) (i j : ι) :
    0 ≤ finiteCWWeightedRealConjugate M basis i j := by
  dsimp [finiteCWWeightedRealConjugate]
  positivity

lemma finiteCWWeightedRealConjugate_eq_unit_conj {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι NNReal) (basis : FiniteCWBasis ι) :
    finiteCWWeightedRealConjugate M basis =
      (finiteCWDiagonalUnit basis)⁻¹ * nnrealMatrixToReal M *
        finiteCWDiagonalUnit basis := by
  ext i j
  simp [finiteCWWeightedRealConjugate, nnrealMatrixToReal, finiteCWDiagonalUnit, mul_assoc]

lemma finiteCWWeightedRealConjugate_row_sum_le {ι : Type*}
    [Fintype ι]
    (M : Matrix ι ι NNReal) (basis : FiniteCWBasis ι) (alpha : NNReal)
    (hCW : FiniteCWCertificate M basis alpha) :
    ∀ i, (∑ j, ‖finiteCWWeightedRealConjugate M basis i j‖₊) ≤ alpha := by
  intro i
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_sum, coe_nnnorm]
  have hnonneg : ∀ j, 0 ≤ finiteCWWeightedRealConjugate M basis i j :=
    finiteCWWeightedRealConjugate_nonneg M basis i
  simp_rw [Real.norm_of_nonneg (hnonneg _)]
  have hCWReal :
      (∑ j, (M i j : ℝ) * (basis.vector j : ℝ)) ≤
        (alpha : ℝ) * (basis.vector i : ℝ) := by
    have h := hCW i
    rw [← NNReal.coe_le_coe] at h
    simpa [Matrix.mulVec, dotProduct, NNReal.coe_sum, NNReal.coe_mul] using h
  have hi_pos : 0 < (basis.vector i : ℝ) := by
    exact_mod_cast basis.positive i
  have hsum_eq :
      (∑ j, (basis.vector i : ℝ)⁻¹ * (M i j : ℝ) * (basis.vector j : ℝ)) =
        (basis.vector i : ℝ)⁻¹ * ∑ j, (M i j : ℝ) * (basis.vector j : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  calc
    (∑ j, finiteCWWeightedRealConjugate M basis i j) =
        (∑ j, (basis.vector i : ℝ)⁻¹ * (M i j : ℝ) * (basis.vector j : ℝ)) := by
      simp [finiteCWWeightedRealConjugate]
    _ = (basis.vector i : ℝ)⁻¹ * ∑ j, (M i j : ℝ) * (basis.vector j : ℝ) := hsum_eq
    _ ≤ (basis.vector i : ℝ)⁻¹ * ((alpha : ℝ) * (basis.vector i : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hCWReal (inv_nonneg.mpr hi_pos.le)
    _ = alpha := by
      field_simp [hi_pos.ne']

lemma finiteCWWeightedRealConjugate_spectrum_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι NNReal) (basis : FiniteCWBasis ι) :
    spectrum ℝ (finiteCWWeightedRealConjugate M basis) =
      spectrum ℝ (nnrealMatrixToReal M) := by
  rw [finiteCWWeightedRealConjugate_eq_unit_conj]
  exact spectrum.units_conjugate'

/--
A finite Collatz-Wielandt certificate bounds the Mathlib real spectral
radius of the realified non-negative matrix.
-/
theorem spectralRadius_le_of_finiteCWCertificate {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι NNReal) (basis : FiniteCWBasis ι) (alpha : NNReal)
    (hCW : FiniteCWCertificate M basis alpha) :
    spectralRadius ℝ (nnrealMatrixToReal M) ≤ (alpha : ℝ≥0∞) := by
  calc
    spectralRadius ℝ (nnrealMatrixToReal M) =
        spectralRadius ℝ (finiteCWWeightedRealConjugate M basis) := by
      rw [spectralRadius, spectralRadius, ← finiteCWWeightedRealConjugate_spectrum_eq M basis]
    _ ≤ (alpha : ℝ≥0∞) :=
      spectralRadius_le_of_forall_row_nnnorm_sum_le
        (finiteCWWeightedRealConjugate M basis) alpha
        (finiteCWWeightedRealConjugate_row_sum_le M basis alpha hCW)

/--
The finite `core + tail` CW certificate gives the corresponding
spectral-radius bound for the full realified matrix.
-/
theorem spectralRadius_le_of_finiteCWCertificateOfSumEq {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {full core tail : Matrix ι ι NNReal}
    {basis : FiniteCWBasis ι}
    {alphaCore alphaTail : NNReal}
    (hFull : full = core + tail)
    (hCore : FiniteCWCertificate core basis alphaCore)
    (hTail : FiniteCWCertificate tail basis alphaTail) :
    spectralRadius ℝ (nnrealMatrixToReal full) ≤
      ((alphaCore + alphaTail : NNReal) : ℝ≥0∞) :=
  spectralRadius_le_of_finiteCWCertificate full basis (alphaCore + alphaTail)
    (finiteCWCertificateOfSumEq hFull hCore hTail)

/-- Positive vector certificate for a finite non-negative matrix bound. -/
structure CWBasis (V : ℕ) where
  vector : PhaseState V → NNReal
  positive : ∀ i, 0 < vector i

/-- View a phase-state CW basis as the generic finite CW basis. -/
def CWBasis.toFiniteCWBasis {V : ℕ} (basis : CWBasis V) :
    FiniteCWBasis (PhaseState V) where
  vector := basis.vector
  positive := basis.positive

/-- Pointwise Collatz-Wielandt-style upper certificate. -/
def CWCertificate {V : ℕ}
    (M : TransferMatrix V)
    (basis : CWBasis V)
    (alpha : NNReal) : Prop :=
  ∀ i, Matrix.mulVec M basis.vector i ≤ alpha * basis.vector i

/-- View a phase-state CW certificate as the generic finite CW certificate. -/
theorem CWCertificate.toFiniteCWCertificate {V : ℕ}
    {M : TransferMatrix V}
    {basis : CWBasis V}
    {alpha : NNReal}
    (hCW : CWCertificate M basis alpha) :
    FiniteCWCertificate M basis.toFiniteCWBasis alpha := by
  intro i
  exact hCW i

/--
A phase-state CW certificate bounds the Mathlib real spectral radius of
the corresponding realified transfer matrix.
-/
theorem spectralRadius_le_of_CWCertificate {V : ℕ}
    (M : TransferMatrix V) (basis : CWBasis V) (alpha : NNReal)
    (hCW : CWCertificate M basis alpha) :
    spectralRadius ℝ (nnrealMatrixToReal M) ≤ (alpha : ℝ≥0∞) :=
  spectralRadius_le_of_finiteCWCertificate M basis.toFiniteCWBasis alpha
    hCW.toFiniteCWCertificate

/-- A packaged finite matrix bound certificate. -/
structure MatrixBoundCertificate (V : ℕ) where
  matrix : TransferMatrix V
  basis : CWBasis V
  alpha : NNReal
  certificate : CWCertificate matrix basis alpha

/-- The all-ones vector is positive on every finite phase space. -/
def onesBasis (V : ℕ) : CWBasis V where
  vector := fun _ => 1
  positive := by
    intro i
    norm_num

/-- Baseline certificate for the zero matrix. -/
def zeroMatrixBoundCertificate (V : ℕ) : MatrixBoundCertificate V where
  matrix := 0
  basis := onesBasis V
  alpha := 0
  certificate := by
    intro i
    simp [Matrix.mulVec, onesBasis]

/--
Phase-state Collatz-Wielandt certificates are additive for a shared
positive basis.
-/
theorem CWCertificate.add {V : ℕ}
    {A B : TransferMatrix V}
    {basis : CWBasis V}
    {alpha beta : NNReal}
    (hA : CWCertificate A basis alpha)
    (hB : CWCertificate B basis beta) :
    CWCertificate (A + B) basis (alpha + beta) := by
  intro i
  calc
    Matrix.mulVec (A + B) basis.vector i =
        Matrix.mulVec A basis.vector i + Matrix.mulVec B basis.vector i := by
      simp
    _ ≤ alpha * basis.vector i + beta * basis.vector i :=
      add_le_add (hA i) (hB i)
    _ = (alpha + beta) * basis.vector i := by
      rw [add_mul]

/--
Apply the finite `core + tail` CW bound to an `OperatorDecomposition`.
-/
theorem OperatorDecomposition.cwCertificate_full {V : ℕ}
    (op : OperatorDecomposition V)
    {basis : CWBasis V}
    {alphaCore alphaTail : NNReal}
    (hCore : CWCertificate op.core basis alphaCore)
    (hTail : CWCertificate op.tail basis alphaTail) :
    CWCertificate op.full basis (alphaCore + alphaTail) := by
  rw [op.full_eq_core_add_tail]
  exact hCore.add hTail

/--
The phase-state `core + tail` CW certificates bound the real spectral
radius of the full transfer matrix.
-/
theorem OperatorDecomposition.spectralRadius_le_full {V : ℕ}
    (op : OperatorDecomposition V)
    {basis : CWBasis V}
    {alphaCore alphaTail : NNReal}
    (hCore : CWCertificate op.core basis alphaCore)
    (hTail : CWCertificate op.tail basis alphaTail) :
    spectralRadius ℝ (nnrealMatrixToReal op.full) ≤
      ((alphaCore + alphaTail : NNReal) : ℝ≥0∞) :=
  spectralRadius_le_of_CWCertificate op.full basis (alphaCore + alphaTail)
    (op.cwCertificate_full hCore hTail)

end CollatzShadowing
