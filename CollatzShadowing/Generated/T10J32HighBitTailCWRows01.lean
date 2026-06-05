import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 16. -/
def t10j32HighBitTailNode016Label : String :=
  "v2=1|odd=0|h=0"

/-- Destination support of generated row 16. -/
def t10j32HighBitTailNode016Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 16. -/
def t10j32HighBitTailNode016LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 16. -/
def t10j32HighBitTailNode016LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 16. -/
def t10j32HighBitTailNode016Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 16. -/
theorem t10j32HighBitTailNode016Bound :
    t10j32HighBitTailNode016LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode016Vector * t10j32HighBitTailNode016LhsDen := by
  norm_num [t10j32HighBitTailNode016LhsNum, t10j32HighBitTailNode016LhsDen, t10j32HighBitTailNode016Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 16. -/
def t10j32HighBitTailNode016Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode016LhsNum
  lhsDen := t10j32HighBitTailNode016LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode016LhsDen]
  vector := t10j32HighBitTailNode016Vector
  vector_pos := by norm_num [t10j32HighBitTailNode016Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode016Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 16. -/
theorem t10j32HighBitTailNode016MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (16 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode016LhsNum : NNReal) / (t10j32HighBitTailNode016LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode016LhsNum, t10j32HighBitTailNode016LhsDen]

/-- Evaluated row certificate for generated row 16. -/
def t10j32HighBitTailNode016Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (16 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode016Row
  lhs_eq := by simpa using t10j32HighBitTailNode016MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode016Row]


/-- State label for generated row 17. -/
def t10j32HighBitTailNode017Label : String :=
  "v2=1|odd=0|h=1"

/-- Destination support of generated row 17. -/
def t10j32HighBitTailNode017Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 17. -/
def t10j32HighBitTailNode017LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 17. -/
def t10j32HighBitTailNode017LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 17. -/
def t10j32HighBitTailNode017Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 17. -/
theorem t10j32HighBitTailNode017Bound :
    t10j32HighBitTailNode017LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode017Vector * t10j32HighBitTailNode017LhsDen := by
  norm_num [t10j32HighBitTailNode017LhsNum, t10j32HighBitTailNode017LhsDen, t10j32HighBitTailNode017Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 17. -/
def t10j32HighBitTailNode017Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode017LhsNum
  lhsDen := t10j32HighBitTailNode017LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode017LhsDen]
  vector := t10j32HighBitTailNode017Vector
  vector_pos := by norm_num [t10j32HighBitTailNode017Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode017Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 17. -/
theorem t10j32HighBitTailNode017MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (17 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode017LhsNum : NNReal) / (t10j32HighBitTailNode017LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode017LhsNum, t10j32HighBitTailNode017LhsDen]

/-- Evaluated row certificate for generated row 17. -/
def t10j32HighBitTailNode017Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (17 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode017Row
  lhs_eq := by simpa using t10j32HighBitTailNode017MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode017Row]


/-- State label for generated row 18. -/
def t10j32HighBitTailNode018Label : String :=
  "v2=1|odd=0|h=2"

/-- Destination support of generated row 18. -/
def t10j32HighBitTailNode018Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 18. -/
def t10j32HighBitTailNode018LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 18. -/
def t10j32HighBitTailNode018LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 18. -/
def t10j32HighBitTailNode018Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 18. -/
theorem t10j32HighBitTailNode018Bound :
    t10j32HighBitTailNode018LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode018Vector * t10j32HighBitTailNode018LhsDen := by
  norm_num [t10j32HighBitTailNode018LhsNum, t10j32HighBitTailNode018LhsDen, t10j32HighBitTailNode018Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 18. -/
def t10j32HighBitTailNode018Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode018LhsNum
  lhsDen := t10j32HighBitTailNode018LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode018LhsDen]
  vector := t10j32HighBitTailNode018Vector
  vector_pos := by norm_num [t10j32HighBitTailNode018Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode018Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 18. -/
theorem t10j32HighBitTailNode018MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (18 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode018LhsNum : NNReal) / (t10j32HighBitTailNode018LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode018LhsNum, t10j32HighBitTailNode018LhsDen]

/-- Evaluated row certificate for generated row 18. -/
def t10j32HighBitTailNode018Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (18 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode018Row
  lhs_eq := by simpa using t10j32HighBitTailNode018MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode018Row]


/-- State label for generated row 19. -/
def t10j32HighBitTailNode019Label : String :=
  "v2=1|odd=0|h=3"

/-- Destination support of generated row 19. -/
def t10j32HighBitTailNode019Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 19. -/
def t10j32HighBitTailNode019LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 19. -/
def t10j32HighBitTailNode019LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 19. -/
def t10j32HighBitTailNode019Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 19. -/
theorem t10j32HighBitTailNode019Bound :
    t10j32HighBitTailNode019LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode019Vector * t10j32HighBitTailNode019LhsDen := by
  norm_num [t10j32HighBitTailNode019LhsNum, t10j32HighBitTailNode019LhsDen, t10j32HighBitTailNode019Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 19. -/
def t10j32HighBitTailNode019Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode019LhsNum
  lhsDen := t10j32HighBitTailNode019LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode019LhsDen]
  vector := t10j32HighBitTailNode019Vector
  vector_pos := by norm_num [t10j32HighBitTailNode019Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode019Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 19. -/
theorem t10j32HighBitTailNode019MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (19 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode019LhsNum : NNReal) / (t10j32HighBitTailNode019LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode019LhsNum, t10j32HighBitTailNode019LhsDen]

/-- Evaluated row certificate for generated row 19. -/
def t10j32HighBitTailNode019Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (19 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode019Row
  lhs_eq := by simpa using t10j32HighBitTailNode019MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode019Row]


/-- State label for generated row 20. -/
def t10j32HighBitTailNode020Label : String :=
  "v2=1|odd=1|h=0"

/-- Destination support of generated row 20. -/
def t10j32HighBitTailNode020Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 37, 45, 53, 61, 69, 77, 85, 93, 109}

/-- Exact generated summand values for row 20. -/
noncomputable def t10j32HighBitTailNode020Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((2706297 : NNReal) / (512 : NNReal))
  | 13 => ((260923069 : NNReal) / (65536 : NNReal))
  | 21 => ((18245487 : NNReal) / (16384 : NNReal))
  | 29 => ((5756505 : NNReal) / (4096 : NNReal))
  | 37 => ((4722957 : NNReal) / (8192 : NNReal))
  | 45 => ((37977417 : NNReal) / (8192 : NNReal))
  | 53 => ((3322485 : NNReal) / (4096 : NNReal))
  | 61 => ((2874741 : NNReal) / (4096 : NNReal))
  | 69 => ((15625 : NNReal) / (256 : NNReal))
  | 77 => ((15625 : NNReal) / (64 : NNReal))
  | 85 => ((1834187 : NNReal) / (4096 : NNReal))
  | 93 => ((15625 : NNReal) / (128 : NNReal))
  | 109 => ((46875 : NNReal) / (256 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 20. -/
def t10j32HighBitTailNode020LhsNum : Nat :=
  1282520713

/-- Exact denominator of `(M v)_i` for generated row 20. -/
def t10j32HighBitTailNode020LhsDen : Nat :=
  65536

/-- Exact vector entry for generated row 20. -/
def t10j32HighBitTailNode020Vector : Nat :=
  1403499

/-- Exact cleared-denominator CW inequality for generated row 20. -/
theorem t10j32HighBitTailNode020Bound :
    t10j32HighBitTailNode020LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode020Vector * t10j32HighBitTailNode020LhsDen := by
  norm_num [t10j32HighBitTailNode020LhsNum, t10j32HighBitTailNode020LhsDen, t10j32HighBitTailNode020Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 20. -/
def t10j32HighBitTailNode020Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode020LhsNum
  lhsDen := t10j32HighBitTailNode020LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode020LhsDen]
  vector := t10j32HighBitTailNode020Vector
  vector_pos := by norm_num [t10j32HighBitTailNode020Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode020Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 20. -/
theorem t10j32HighBitTailNode020MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (20 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode020LhsNum : NNReal) / (t10j32HighBitTailNode020LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode020Support,
      t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) dst *
        t10j32HighBitTailCWBasis.vector dst
  · symm
    refine Finset.sum_subset (by intro dst hdst; simp) ?_
    intro dst _ hdst
    fin_cases dst <;>
      first
      | exact False.elim (hdst (by decide))
      | change (0 : NNReal) * _ = 0
        norm_num
  ·
    have h005 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (5 : T10J32HighBitTailState) := by
      change (((33 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode020Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h013 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (13 : T10J32HighBitTailState) := by
      change (((121 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode020Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h021 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (21 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (16384 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode020Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h029 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (29 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode020Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h037 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (37 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (37 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (37 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode020Term (37 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h045 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (45 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (45 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (45 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode020Term (45 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h053 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (53 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (53 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (53 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode020Term (53 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h061 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (61 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (61 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (61 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode020Term (61 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h069 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (69 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (69 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (69 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode020Term (69 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h077 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (77 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (77 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (77 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode020Term (77 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h085 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (85 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (85 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (85 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode020Term (85 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h093 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (93 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (93 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (93 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode020Term (93 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    have h109 :
        t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) (109 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (109 : T10J32HighBitTailState) =
          t10j32HighBitTailNode020Term (109 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode020Term (109 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode020Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode020Support,
          t10j32HighBitTailMatrix (20 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode020Support, t10j32HighBitTailNode020Term dst := by
        simp [t10j32HighBitTailNode020Support, h005, h013, h021, h029, h037, h045, h053, h061, h069, h077, h085, h093, h109]
      _ = (t10j32HighBitTailNode020LhsNum : NNReal) / (t10j32HighBitTailNode020LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode020Support, t10j32HighBitTailNode020Term]
        norm_num [t10j32HighBitTailNode020LhsNum, t10j32HighBitTailNode020LhsDen]

/-- Evaluated row certificate for generated row 20. -/
def t10j32HighBitTailNode020Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (20 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode020Row
  lhs_eq := by simpa using t10j32HighBitTailNode020MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode020Row]


/-- State label for generated row 21. -/
def t10j32HighBitTailNode021Label : String :=
  "v2=1|odd=1|h=1"

/-- Destination support of generated row 21. -/
def t10j32HighBitTailNode021Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 38, 46, 54, 62, 70, 78, 86, 94, 110}

/-- Exact generated summand values for row 21. -/
noncomputable def t10j32HighBitTailNode021Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((2706297 : NNReal) / (512 : NNReal))
  | 14 => ((260923069 : NNReal) / (65536 : NNReal))
  | 22 => ((18245487 : NNReal) / (16384 : NNReal))
  | 30 => ((5756505 : NNReal) / (4096 : NNReal))
  | 38 => ((4722957 : NNReal) / (8192 : NNReal))
  | 46 => ((37977417 : NNReal) / (8192 : NNReal))
  | 54 => ((3322485 : NNReal) / (4096 : NNReal))
  | 62 => ((2874741 : NNReal) / (4096 : NNReal))
  | 70 => ((15625 : NNReal) / (256 : NNReal))
  | 78 => ((15625 : NNReal) / (64 : NNReal))
  | 86 => ((1834187 : NNReal) / (4096 : NNReal))
  | 94 => ((15625 : NNReal) / (128 : NNReal))
  | 110 => ((46875 : NNReal) / (256 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 21. -/
def t10j32HighBitTailNode021LhsNum : Nat :=
  1282520713

/-- Exact denominator of `(M v)_i` for generated row 21. -/
def t10j32HighBitTailNode021LhsDen : Nat :=
  65536

/-- Exact vector entry for generated row 21. -/
def t10j32HighBitTailNode021Vector : Nat :=
  1403499

/-- Exact cleared-denominator CW inequality for generated row 21. -/
theorem t10j32HighBitTailNode021Bound :
    t10j32HighBitTailNode021LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode021Vector * t10j32HighBitTailNode021LhsDen := by
  norm_num [t10j32HighBitTailNode021LhsNum, t10j32HighBitTailNode021LhsDen, t10j32HighBitTailNode021Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 21. -/
def t10j32HighBitTailNode021Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode021LhsNum
  lhsDen := t10j32HighBitTailNode021LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode021LhsDen]
  vector := t10j32HighBitTailNode021Vector
  vector_pos := by norm_num [t10j32HighBitTailNode021Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode021Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 21. -/
theorem t10j32HighBitTailNode021MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (21 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode021LhsNum : NNReal) / (t10j32HighBitTailNode021LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode021Support,
      t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) dst *
        t10j32HighBitTailCWBasis.vector dst
  · symm
    refine Finset.sum_subset (by intro dst hdst; simp) ?_
    intro dst _ hdst
    fin_cases dst <;>
      first
      | exact False.elim (hdst (by decide))
      | change (0 : NNReal) * _ = 0
        norm_num
  ·
    have h006 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (6 : T10J32HighBitTailState) := by
      change (((33 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode021Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h014 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (14 : T10J32HighBitTailState) := by
      change (((121 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode021Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h022 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (22 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (16384 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode021Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h030 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (30 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode021Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h038 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (38 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (38 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (38 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode021Term (38 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h046 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (46 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (46 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (46 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode021Term (46 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h054 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (54 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (54 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (54 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode021Term (54 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h062 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (62 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (62 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (62 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode021Term (62 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h070 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (70 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (70 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (70 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode021Term (70 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h078 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (78 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (78 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (78 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode021Term (78 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h086 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (86 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (86 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (86 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode021Term (86 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h094 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (94 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (94 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (94 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode021Term (94 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    have h110 :
        t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) (110 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (110 : T10J32HighBitTailState) =
          t10j32HighBitTailNode021Term (110 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode021Term (110 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode021Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode021Support,
          t10j32HighBitTailMatrix (21 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode021Support, t10j32HighBitTailNode021Term dst := by
        simp [t10j32HighBitTailNode021Support, h006, h014, h022, h030, h038, h046, h054, h062, h070, h078, h086, h094, h110]
      _ = (t10j32HighBitTailNode021LhsNum : NNReal) / (t10j32HighBitTailNode021LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode021Support, t10j32HighBitTailNode021Term]
        norm_num [t10j32HighBitTailNode021LhsNum, t10j32HighBitTailNode021LhsDen]

/-- Evaluated row certificate for generated row 21. -/
def t10j32HighBitTailNode021Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (21 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode021Row
  lhs_eq := by simpa using t10j32HighBitTailNode021MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode021Row]


/-- State label for generated row 22. -/
def t10j32HighBitTailNode022Label : String :=
  "v2=1|odd=1|h=2"

/-- Destination support of generated row 22. -/
def t10j32HighBitTailNode022Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 39, 47, 55, 63, 71, 79, 87, 95, 111}

/-- Exact generated summand values for row 22. -/
noncomputable def t10j32HighBitTailNode022Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((2706297 : NNReal) / (512 : NNReal))
  | 15 => ((260923069 : NNReal) / (65536 : NNReal))
  | 23 => ((18245487 : NNReal) / (16384 : NNReal))
  | 31 => ((5756505 : NNReal) / (4096 : NNReal))
  | 39 => ((4722957 : NNReal) / (8192 : NNReal))
  | 47 => ((37977417 : NNReal) / (8192 : NNReal))
  | 55 => ((3322485 : NNReal) / (4096 : NNReal))
  | 63 => ((2874741 : NNReal) / (4096 : NNReal))
  | 71 => ((15625 : NNReal) / (256 : NNReal))
  | 79 => ((15625 : NNReal) / (64 : NNReal))
  | 87 => ((1834187 : NNReal) / (4096 : NNReal))
  | 95 => ((15625 : NNReal) / (128 : NNReal))
  | 111 => ((46875 : NNReal) / (256 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 22. -/
def t10j32HighBitTailNode022LhsNum : Nat :=
  1282520713

/-- Exact denominator of `(M v)_i` for generated row 22. -/
def t10j32HighBitTailNode022LhsDen : Nat :=
  65536

/-- Exact vector entry for generated row 22. -/
def t10j32HighBitTailNode022Vector : Nat :=
  1403499

/-- Exact cleared-denominator CW inequality for generated row 22. -/
theorem t10j32HighBitTailNode022Bound :
    t10j32HighBitTailNode022LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode022Vector * t10j32HighBitTailNode022LhsDen := by
  norm_num [t10j32HighBitTailNode022LhsNum, t10j32HighBitTailNode022LhsDen, t10j32HighBitTailNode022Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 22. -/
def t10j32HighBitTailNode022Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode022LhsNum
  lhsDen := t10j32HighBitTailNode022LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode022LhsDen]
  vector := t10j32HighBitTailNode022Vector
  vector_pos := by norm_num [t10j32HighBitTailNode022Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode022Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 22. -/
theorem t10j32HighBitTailNode022MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (22 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode022LhsNum : NNReal) / (t10j32HighBitTailNode022LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode022Support,
      t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) dst *
        t10j32HighBitTailCWBasis.vector dst
  · symm
    refine Finset.sum_subset (by intro dst hdst; simp) ?_
    intro dst _ hdst
    fin_cases dst <;>
      first
      | exact False.elim (hdst (by decide))
      | change (0 : NNReal) * _ = 0
        norm_num
  ·
    have h007 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (7 : T10J32HighBitTailState) := by
      change (((33 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode022Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h015 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (15 : T10J32HighBitTailState) := by
      change (((121 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode022Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h023 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (23 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (16384 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode022Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h031 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (31 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode022Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h039 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (39 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (39 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (39 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode022Term (39 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h047 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (47 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (47 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (47 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode022Term (47 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h055 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (55 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (55 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (55 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode022Term (55 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h063 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (63 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (63 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (63 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode022Term (63 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h071 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (71 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (71 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (71 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode022Term (71 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h079 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (79 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (79 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (79 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode022Term (79 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h087 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (87 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (87 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (87 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode022Term (87 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h095 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (95 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (95 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (95 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode022Term (95 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    have h111 :
        t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) (111 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (111 : T10J32HighBitTailState) =
          t10j32HighBitTailNode022Term (111 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode022Term (111 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode022Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode022Support,
          t10j32HighBitTailMatrix (22 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode022Support, t10j32HighBitTailNode022Term dst := by
        simp [t10j32HighBitTailNode022Support, h007, h015, h023, h031, h039, h047, h055, h063, h071, h079, h087, h095, h111]
      _ = (t10j32HighBitTailNode022LhsNum : NNReal) / (t10j32HighBitTailNode022LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode022Support, t10j32HighBitTailNode022Term]
        norm_num [t10j32HighBitTailNode022LhsNum, t10j32HighBitTailNode022LhsDen]

/-- Evaluated row certificate for generated row 22. -/
def t10j32HighBitTailNode022Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (22 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode022Row
  lhs_eq := by simpa using t10j32HighBitTailNode022MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode022Row]


/-- State label for generated row 23. -/
def t10j32HighBitTailNode023Label : String :=
  "v2=1|odd=1|h=3"

/-- Destination support of generated row 23. -/
def t10j32HighBitTailNode023Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 108}

/-- Exact generated summand values for row 23. -/
noncomputable def t10j32HighBitTailNode023Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((2706297 : NNReal) / (512 : NNReal))
  | 12 => ((260923069 : NNReal) / (65536 : NNReal))
  | 20 => ((18245487 : NNReal) / (16384 : NNReal))
  | 28 => ((5756505 : NNReal) / (4096 : NNReal))
  | 36 => ((4722957 : NNReal) / (8192 : NNReal))
  | 44 => ((37977417 : NNReal) / (8192 : NNReal))
  | 52 => ((3322485 : NNReal) / (4096 : NNReal))
  | 60 => ((2874741 : NNReal) / (4096 : NNReal))
  | 68 => ((15625 : NNReal) / (256 : NNReal))
  | 76 => ((15625 : NNReal) / (64 : NNReal))
  | 84 => ((1834187 : NNReal) / (4096 : NNReal))
  | 92 => ((15625 : NNReal) / (128 : NNReal))
  | 108 => ((46875 : NNReal) / (256 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 23. -/
def t10j32HighBitTailNode023LhsNum : Nat :=
  1282520713

/-- Exact denominator of `(M v)_i` for generated row 23. -/
def t10j32HighBitTailNode023LhsDen : Nat :=
  65536

/-- Exact vector entry for generated row 23. -/
def t10j32HighBitTailNode023Vector : Nat :=
  1403499

/-- Exact cleared-denominator CW inequality for generated row 23. -/
theorem t10j32HighBitTailNode023Bound :
    t10j32HighBitTailNode023LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode023Vector * t10j32HighBitTailNode023LhsDen := by
  norm_num [t10j32HighBitTailNode023LhsNum, t10j32HighBitTailNode023LhsDen, t10j32HighBitTailNode023Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 23. -/
def t10j32HighBitTailNode023Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode023LhsNum
  lhsDen := t10j32HighBitTailNode023LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode023LhsDen]
  vector := t10j32HighBitTailNode023Vector
  vector_pos := by norm_num [t10j32HighBitTailNode023Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode023Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 23. -/
theorem t10j32HighBitTailNode023MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (23 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode023LhsNum : NNReal) / (t10j32HighBitTailNode023LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode023Support,
      t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) dst *
        t10j32HighBitTailCWBasis.vector dst
  · symm
    refine Finset.sum_subset (by intro dst hdst; simp) ?_
    intro dst _ hdst
    fin_cases dst <;>
      first
      | exact False.elim (hdst (by decide))
      | change (0 : NNReal) * _ = 0
        norm_num
  ·
    have h004 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (4 : T10J32HighBitTailState) := by
      change (((33 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode023Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h012 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (12 : T10J32HighBitTailState) := by
      change (((121 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode023Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h020 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (20 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (16384 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode023Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h028 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (28 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode023Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h036 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (36 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (36 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (36 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode023Term (36 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h044 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (44 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (44 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (44 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode023Term (44 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h052 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (52 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (52 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (52 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode023Term (52 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h060 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (60 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (60 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (60 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode023Term (60 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h068 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (68 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (68 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (68 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode023Term (68 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h076 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (76 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (76 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (76 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode023Term (76 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h084 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (84 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (84 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (84 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode023Term (84 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h092 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (92 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (92 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (92 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode023Term (92 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    have h108 :
        t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) (108 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (108 : T10J32HighBitTailState) =
          t10j32HighBitTailNode023Term (108 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode023Term (108 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode023Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode023Support,
          t10j32HighBitTailMatrix (23 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode023Support, t10j32HighBitTailNode023Term dst := by
        simp [t10j32HighBitTailNode023Support, h004, h012, h020, h028, h036, h044, h052, h060, h068, h076, h084, h092, h108]
      _ = (t10j32HighBitTailNode023LhsNum : NNReal) / (t10j32HighBitTailNode023LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode023Support, t10j32HighBitTailNode023Term]
        norm_num [t10j32HighBitTailNode023LhsNum, t10j32HighBitTailNode023LhsDen]

/-- Evaluated row certificate for generated row 23. -/
def t10j32HighBitTailNode023Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (23 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode023Row
  lhs_eq := by simpa using t10j32HighBitTailNode023MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode023Row]


/-- State label for generated row 24. -/
def t10j32HighBitTailNode024Label : String :=
  "v2=1|odd=2|h=0"

/-- Destination support of generated row 24. -/
def t10j32HighBitTailNode024Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 24. -/
def t10j32HighBitTailNode024LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 24. -/
def t10j32HighBitTailNode024LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 24. -/
def t10j32HighBitTailNode024Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 24. -/
theorem t10j32HighBitTailNode024Bound :
    t10j32HighBitTailNode024LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode024Vector * t10j32HighBitTailNode024LhsDen := by
  norm_num [t10j32HighBitTailNode024LhsNum, t10j32HighBitTailNode024LhsDen, t10j32HighBitTailNode024Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 24. -/
def t10j32HighBitTailNode024Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode024LhsNum
  lhsDen := t10j32HighBitTailNode024LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode024LhsDen]
  vector := t10j32HighBitTailNode024Vector
  vector_pos := by norm_num [t10j32HighBitTailNode024Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode024Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 24. -/
theorem t10j32HighBitTailNode024MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (24 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode024LhsNum : NNReal) / (t10j32HighBitTailNode024LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode024LhsNum, t10j32HighBitTailNode024LhsDen]

/-- Evaluated row certificate for generated row 24. -/
def t10j32HighBitTailNode024Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (24 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode024Row
  lhs_eq := by simpa using t10j32HighBitTailNode024MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode024Row]


/-- State label for generated row 25. -/
def t10j32HighBitTailNode025Label : String :=
  "v2=1|odd=2|h=1"

/-- Destination support of generated row 25. -/
def t10j32HighBitTailNode025Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 25. -/
def t10j32HighBitTailNode025LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 25. -/
def t10j32HighBitTailNode025LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 25. -/
def t10j32HighBitTailNode025Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 25. -/
theorem t10j32HighBitTailNode025Bound :
    t10j32HighBitTailNode025LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode025Vector * t10j32HighBitTailNode025LhsDen := by
  norm_num [t10j32HighBitTailNode025LhsNum, t10j32HighBitTailNode025LhsDen, t10j32HighBitTailNode025Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 25. -/
def t10j32HighBitTailNode025Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode025LhsNum
  lhsDen := t10j32HighBitTailNode025LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode025LhsDen]
  vector := t10j32HighBitTailNode025Vector
  vector_pos := by norm_num [t10j32HighBitTailNode025Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode025Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 25. -/
theorem t10j32HighBitTailNode025MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (25 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode025LhsNum : NNReal) / (t10j32HighBitTailNode025LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode025LhsNum, t10j32HighBitTailNode025LhsDen]

/-- Evaluated row certificate for generated row 25. -/
def t10j32HighBitTailNode025Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (25 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode025Row
  lhs_eq := by simpa using t10j32HighBitTailNode025MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode025Row]


/-- State label for generated row 26. -/
def t10j32HighBitTailNode026Label : String :=
  "v2=1|odd=2|h=2"

/-- Destination support of generated row 26. -/
def t10j32HighBitTailNode026Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 26. -/
def t10j32HighBitTailNode026LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 26. -/
def t10j32HighBitTailNode026LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 26. -/
def t10j32HighBitTailNode026Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 26. -/
theorem t10j32HighBitTailNode026Bound :
    t10j32HighBitTailNode026LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode026Vector * t10j32HighBitTailNode026LhsDen := by
  norm_num [t10j32HighBitTailNode026LhsNum, t10j32HighBitTailNode026LhsDen, t10j32HighBitTailNode026Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 26. -/
def t10j32HighBitTailNode026Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode026LhsNum
  lhsDen := t10j32HighBitTailNode026LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode026LhsDen]
  vector := t10j32HighBitTailNode026Vector
  vector_pos := by norm_num [t10j32HighBitTailNode026Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode026Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 26. -/
theorem t10j32HighBitTailNode026MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (26 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode026LhsNum : NNReal) / (t10j32HighBitTailNode026LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode026LhsNum, t10j32HighBitTailNode026LhsDen]

/-- Evaluated row certificate for generated row 26. -/
def t10j32HighBitTailNode026Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (26 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode026Row
  lhs_eq := by simpa using t10j32HighBitTailNode026MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode026Row]


/-- State label for generated row 27. -/
def t10j32HighBitTailNode027Label : String :=
  "v2=1|odd=2|h=3"

/-- Destination support of generated row 27. -/
def t10j32HighBitTailNode027Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 27. -/
def t10j32HighBitTailNode027LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 27. -/
def t10j32HighBitTailNode027LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 27. -/
def t10j32HighBitTailNode027Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 27. -/
theorem t10j32HighBitTailNode027Bound :
    t10j32HighBitTailNode027LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode027Vector * t10j32HighBitTailNode027LhsDen := by
  norm_num [t10j32HighBitTailNode027LhsNum, t10j32HighBitTailNode027LhsDen, t10j32HighBitTailNode027Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 27. -/
def t10j32HighBitTailNode027Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode027LhsNum
  lhsDen := t10j32HighBitTailNode027LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode027LhsDen]
  vector := t10j32HighBitTailNode027Vector
  vector_pos := by norm_num [t10j32HighBitTailNode027Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode027Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 27. -/
theorem t10j32HighBitTailNode027MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (27 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode027LhsNum : NNReal) / (t10j32HighBitTailNode027LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode027LhsNum, t10j32HighBitTailNode027LhsDen]

/-- Evaluated row certificate for generated row 27. -/
def t10j32HighBitTailNode027Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (27 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode027Row
  lhs_eq := by simpa using t10j32HighBitTailNode027MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode027Row]


/-- State label for generated row 28. -/
def t10j32HighBitTailNode028Label : String :=
  "v2=1|odd=3|h=0"

/-- Destination support of generated row 28. -/
def t10j32HighBitTailNode028Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 37, 45, 53, 61, 77, 85, 93, 101, 125, 133, 165}

/-- Exact generated summand values for row 28. -/
noncomputable def t10j32HighBitTailNode028Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((9102999 : NNReal) / (1024 : NNReal))
  | 13 => ((524002527 : NNReal) / (65536 : NNReal))
  | 21 => ((195086361 : NNReal) / (65536 : NNReal))
  | 29 => ((120886605 : NNReal) / (32768 : NNReal))
  | 37 => ((392005431 : NNReal) / (262144 : NNReal))
  | 45 => ((2240667603 : NNReal) / (131072 : NNReal))
  | 53 => ((12182445 : NNReal) / (16384 : NNReal))
  | 61 => ((958247 : NNReal) / (4096 : NNReal))
  | 77 => ((15625 : NNReal) / (64 : NNReal))
  | 85 => ((9170935 : NNReal) / (32768 : NNReal))
  | 93 => ((46875 : NNReal) / (128 : NNReal))
  | 101 => ((239597 : NNReal) / (1024 : NNReal))
  | 125 => ((1915527 : NNReal) / (32768 : NNReal))
  | 133 => ((15625 : NNReal) / (128 : NNReal))
  | 165 => ((572165 : NNReal) / (4096 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 28. -/
def t10j32HighBitTailNode028LhsNum : Nat :=
  11682050789

/-- Exact denominator of `(M v)_i` for generated row 28. -/
def t10j32HighBitTailNode028LhsDen : Nat :=
  262144

/-- Exact vector entry for generated row 28. -/
def t10j32HighBitTailNode028Vector : Nat :=
  1918835

/-- Exact cleared-denominator CW inequality for generated row 28. -/
theorem t10j32HighBitTailNode028Bound :
    t10j32HighBitTailNode028LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode028Vector * t10j32HighBitTailNode028LhsDen := by
  norm_num [t10j32HighBitTailNode028LhsNum, t10j32HighBitTailNode028LhsDen, t10j32HighBitTailNode028Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 28. -/
def t10j32HighBitTailNode028Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode028LhsNum
  lhsDen := t10j32HighBitTailNode028LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode028LhsDen]
  vector := t10j32HighBitTailNode028Vector
  vector_pos := by norm_num [t10j32HighBitTailNode028Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode028Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 28. -/
theorem t10j32HighBitTailNode028MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (28 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode028LhsNum : NNReal) / (t10j32HighBitTailNode028LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode028Support,
      t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) dst *
        t10j32HighBitTailCWBasis.vector dst
  · symm
    refine Finset.sum_subset (by intro dst hdst; simp) ?_
    intro dst _ hdst
    fin_cases dst <;>
      first
      | exact False.elim (hdst (by decide))
      | change (0 : NNReal) * _ = 0
        norm_num
  ·
    have h005 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (5 : T10J32HighBitTailState) := by
      change (((111 : NNReal) / (32768 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode028Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h013 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (13 : T10J32HighBitTailState) := by
      change (((243 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode028Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h021 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (21 : T10J32HighBitTailState) := by
      change (((139 : NNReal) / (65536 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode028Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h029 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (29 : T10J32HighBitTailState) := by
      change (((63 : NNReal) / (32768 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode028Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h037 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (37 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (37 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (37 : T10J32HighBitTailState) := by
      change (((249 : NNReal) / (262144 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode028Term (37 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h045 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (45 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (45 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (45 : T10J32HighBitTailState) := by
      change (((177 : NNReal) / (131072 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode028Term (45 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h053 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (53 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (53 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (53 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (32768 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode028Term (53 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h061 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (61 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (61 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (61 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode028Term (61 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h077 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (77 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (77 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (77 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode028Term (77 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h085 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (85 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (85 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (85 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (32768 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode028Term (85 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h093 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (93 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (93 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (93 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode028Term (93 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h101 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (101 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (101 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (101 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode028Term (101 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h125 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (125 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (125 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (125 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode028Term (125 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h133 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (133 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (133 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (133 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode028Term (133 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    have h165 :
        t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) (165 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (165 : T10J32HighBitTailState) =
          t10j32HighBitTailNode028Term (165 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16384 : NNReal)) * (2288660 : NNReal)) =
        t10j32HighBitTailNode028Term (165 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode028Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode028Support,
          t10j32HighBitTailMatrix (28 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode028Support, t10j32HighBitTailNode028Term dst := by
        simp [t10j32HighBitTailNode028Support, h005, h013, h021, h029, h037, h045, h053, h061, h077, h085, h093, h101, h125, h133, h165]
      _ = (t10j32HighBitTailNode028LhsNum : NNReal) / (t10j32HighBitTailNode028LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode028Support, t10j32HighBitTailNode028Term]
        norm_num [t10j32HighBitTailNode028LhsNum, t10j32HighBitTailNode028LhsDen]

/-- Evaluated row certificate for generated row 28. -/
def t10j32HighBitTailNode028Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (28 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode028Row
  lhs_eq := by simpa using t10j32HighBitTailNode028MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode028Row]


/-- State label for generated row 29. -/
def t10j32HighBitTailNode029Label : String :=
  "v2=1|odd=3|h=1"

/-- Destination support of generated row 29. -/
def t10j32HighBitTailNode029Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 38, 46, 54, 62, 78, 86, 94, 102, 126, 134, 166}

/-- Exact generated summand values for row 29. -/
noncomputable def t10j32HighBitTailNode029Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((9102999 : NNReal) / (1024 : NNReal))
  | 14 => ((524002527 : NNReal) / (65536 : NNReal))
  | 22 => ((195086361 : NNReal) / (65536 : NNReal))
  | 30 => ((120886605 : NNReal) / (32768 : NNReal))
  | 38 => ((392005431 : NNReal) / (262144 : NNReal))
  | 46 => ((2240667603 : NNReal) / (131072 : NNReal))
  | 54 => ((12182445 : NNReal) / (16384 : NNReal))
  | 62 => ((958247 : NNReal) / (4096 : NNReal))
  | 78 => ((15625 : NNReal) / (64 : NNReal))
  | 86 => ((9170935 : NNReal) / (32768 : NNReal))
  | 94 => ((46875 : NNReal) / (128 : NNReal))
  | 102 => ((239597 : NNReal) / (1024 : NNReal))
  | 126 => ((1915527 : NNReal) / (32768 : NNReal))
  | 134 => ((15625 : NNReal) / (128 : NNReal))
  | 166 => ((572165 : NNReal) / (4096 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 29. -/
def t10j32HighBitTailNode029LhsNum : Nat :=
  11682050789

/-- Exact denominator of `(M v)_i` for generated row 29. -/
def t10j32HighBitTailNode029LhsDen : Nat :=
  262144

/-- Exact vector entry for generated row 29. -/
def t10j32HighBitTailNode029Vector : Nat :=
  1918835

/-- Exact cleared-denominator CW inequality for generated row 29. -/
theorem t10j32HighBitTailNode029Bound :
    t10j32HighBitTailNode029LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode029Vector * t10j32HighBitTailNode029LhsDen := by
  norm_num [t10j32HighBitTailNode029LhsNum, t10j32HighBitTailNode029LhsDen, t10j32HighBitTailNode029Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 29. -/
def t10j32HighBitTailNode029Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode029LhsNum
  lhsDen := t10j32HighBitTailNode029LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode029LhsDen]
  vector := t10j32HighBitTailNode029Vector
  vector_pos := by norm_num [t10j32HighBitTailNode029Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode029Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 29. -/
theorem t10j32HighBitTailNode029MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (29 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode029LhsNum : NNReal) / (t10j32HighBitTailNode029LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode029Support,
      t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) dst *
        t10j32HighBitTailCWBasis.vector dst
  · symm
    refine Finset.sum_subset (by intro dst hdst; simp) ?_
    intro dst _ hdst
    fin_cases dst <;>
      first
      | exact False.elim (hdst (by decide))
      | change (0 : NNReal) * _ = 0
        norm_num
  ·
    have h006 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (6 : T10J32HighBitTailState) := by
      change (((111 : NNReal) / (32768 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode029Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h014 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (14 : T10J32HighBitTailState) := by
      change (((243 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode029Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h022 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (22 : T10J32HighBitTailState) := by
      change (((139 : NNReal) / (65536 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode029Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h030 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (30 : T10J32HighBitTailState) := by
      change (((63 : NNReal) / (32768 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode029Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h038 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (38 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (38 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (38 : T10J32HighBitTailState) := by
      change (((249 : NNReal) / (262144 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode029Term (38 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h046 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (46 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (46 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (46 : T10J32HighBitTailState) := by
      change (((177 : NNReal) / (131072 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode029Term (46 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h054 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (54 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (54 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (54 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (32768 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode029Term (54 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h062 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (62 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (62 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (62 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode029Term (62 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h078 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (78 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (78 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (78 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode029Term (78 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h086 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (86 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (86 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (86 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (32768 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode029Term (86 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h094 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (94 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (94 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (94 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode029Term (94 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h102 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (102 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (102 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (102 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode029Term (102 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h126 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (126 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (126 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (126 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode029Term (126 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h134 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (134 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (134 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (134 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode029Term (134 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    have h166 :
        t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) (166 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (166 : T10J32HighBitTailState) =
          t10j32HighBitTailNode029Term (166 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16384 : NNReal)) * (2288660 : NNReal)) =
        t10j32HighBitTailNode029Term (166 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode029Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode029Support,
          t10j32HighBitTailMatrix (29 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode029Support, t10j32HighBitTailNode029Term dst := by
        simp [t10j32HighBitTailNode029Support, h006, h014, h022, h030, h038, h046, h054, h062, h078, h086, h094, h102, h126, h134, h166]
      _ = (t10j32HighBitTailNode029LhsNum : NNReal) / (t10j32HighBitTailNode029LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode029Support, t10j32HighBitTailNode029Term]
        norm_num [t10j32HighBitTailNode029LhsNum, t10j32HighBitTailNode029LhsDen]

/-- Evaluated row certificate for generated row 29. -/
def t10j32HighBitTailNode029Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (29 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode029Row
  lhs_eq := by simpa using t10j32HighBitTailNode029MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode029Row]


/-- State label for generated row 30. -/
def t10j32HighBitTailNode030Label : String :=
  "v2=1|odd=3|h=2"

/-- Destination support of generated row 30. -/
def t10j32HighBitTailNode030Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 39, 47, 55, 63, 79, 87, 95, 103, 127, 135, 167}

/-- Exact generated summand values for row 30. -/
noncomputable def t10j32HighBitTailNode030Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((9102999 : NNReal) / (1024 : NNReal))
  | 15 => ((524002527 : NNReal) / (65536 : NNReal))
  | 23 => ((195086361 : NNReal) / (65536 : NNReal))
  | 31 => ((120886605 : NNReal) / (32768 : NNReal))
  | 39 => ((392005431 : NNReal) / (262144 : NNReal))
  | 47 => ((2240667603 : NNReal) / (131072 : NNReal))
  | 55 => ((12182445 : NNReal) / (16384 : NNReal))
  | 63 => ((958247 : NNReal) / (4096 : NNReal))
  | 79 => ((15625 : NNReal) / (64 : NNReal))
  | 87 => ((9170935 : NNReal) / (32768 : NNReal))
  | 95 => ((46875 : NNReal) / (128 : NNReal))
  | 103 => ((239597 : NNReal) / (1024 : NNReal))
  | 127 => ((1915527 : NNReal) / (32768 : NNReal))
  | 135 => ((15625 : NNReal) / (128 : NNReal))
  | 167 => ((572165 : NNReal) / (4096 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 30. -/
def t10j32HighBitTailNode030LhsNum : Nat :=
  11682050789

/-- Exact denominator of `(M v)_i` for generated row 30. -/
def t10j32HighBitTailNode030LhsDen : Nat :=
  262144

/-- Exact vector entry for generated row 30. -/
def t10j32HighBitTailNode030Vector : Nat :=
  1918835

/-- Exact cleared-denominator CW inequality for generated row 30. -/
theorem t10j32HighBitTailNode030Bound :
    t10j32HighBitTailNode030LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode030Vector * t10j32HighBitTailNode030LhsDen := by
  norm_num [t10j32HighBitTailNode030LhsNum, t10j32HighBitTailNode030LhsDen, t10j32HighBitTailNode030Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 30. -/
def t10j32HighBitTailNode030Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode030LhsNum
  lhsDen := t10j32HighBitTailNode030LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode030LhsDen]
  vector := t10j32HighBitTailNode030Vector
  vector_pos := by norm_num [t10j32HighBitTailNode030Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode030Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 30. -/
theorem t10j32HighBitTailNode030MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (30 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode030LhsNum : NNReal) / (t10j32HighBitTailNode030LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode030Support,
      t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) dst *
        t10j32HighBitTailCWBasis.vector dst
  · symm
    refine Finset.sum_subset (by intro dst hdst; simp) ?_
    intro dst _ hdst
    fin_cases dst <;>
      first
      | exact False.elim (hdst (by decide))
      | change (0 : NNReal) * _ = 0
        norm_num
  ·
    have h007 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (7 : T10J32HighBitTailState) := by
      change (((111 : NNReal) / (32768 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode030Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h015 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (15 : T10J32HighBitTailState) := by
      change (((243 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode030Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h023 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (23 : T10J32HighBitTailState) := by
      change (((139 : NNReal) / (65536 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode030Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h031 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (31 : T10J32HighBitTailState) := by
      change (((63 : NNReal) / (32768 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode030Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h039 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (39 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (39 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (39 : T10J32HighBitTailState) := by
      change (((249 : NNReal) / (262144 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode030Term (39 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h047 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (47 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (47 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (47 : T10J32HighBitTailState) := by
      change (((177 : NNReal) / (131072 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode030Term (47 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h055 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (55 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (55 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (55 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (32768 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode030Term (55 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h063 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (63 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (63 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (63 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode030Term (63 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h079 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (79 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (79 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (79 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode030Term (79 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h087 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (87 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (87 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (87 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (32768 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode030Term (87 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h095 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (95 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (95 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (95 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode030Term (95 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h103 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (103 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (103 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (103 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode030Term (103 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h127 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (127 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (127 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (127 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode030Term (127 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h135 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (135 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (135 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (135 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode030Term (135 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    have h167 :
        t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) (167 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (167 : T10J32HighBitTailState) =
          t10j32HighBitTailNode030Term (167 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16384 : NNReal)) * (2288660 : NNReal)) =
        t10j32HighBitTailNode030Term (167 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode030Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode030Support,
          t10j32HighBitTailMatrix (30 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode030Support, t10j32HighBitTailNode030Term dst := by
        simp [t10j32HighBitTailNode030Support, h007, h015, h023, h031, h039, h047, h055, h063, h079, h087, h095, h103, h127, h135, h167]
      _ = (t10j32HighBitTailNode030LhsNum : NNReal) / (t10j32HighBitTailNode030LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode030Support, t10j32HighBitTailNode030Term]
        norm_num [t10j32HighBitTailNode030LhsNum, t10j32HighBitTailNode030LhsDen]

/-- Evaluated row certificate for generated row 30. -/
def t10j32HighBitTailNode030Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (30 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode030Row
  lhs_eq := by simpa using t10j32HighBitTailNode030MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode030Row]


/-- State label for generated row 31. -/
def t10j32HighBitTailNode031Label : String :=
  "v2=1|odd=3|h=3"

/-- Destination support of generated row 31. -/
def t10j32HighBitTailNode031Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 36, 44, 52, 60, 76, 84, 92, 100, 124, 132, 164}

/-- Exact generated summand values for row 31. -/
noncomputable def t10j32HighBitTailNode031Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((9102999 : NNReal) / (1024 : NNReal))
  | 12 => ((524002527 : NNReal) / (65536 : NNReal))
  | 20 => ((195086361 : NNReal) / (65536 : NNReal))
  | 28 => ((120886605 : NNReal) / (32768 : NNReal))
  | 36 => ((392005431 : NNReal) / (262144 : NNReal))
  | 44 => ((2240667603 : NNReal) / (131072 : NNReal))
  | 52 => ((12182445 : NNReal) / (16384 : NNReal))
  | 60 => ((958247 : NNReal) / (4096 : NNReal))
  | 76 => ((15625 : NNReal) / (64 : NNReal))
  | 84 => ((9170935 : NNReal) / (32768 : NNReal))
  | 92 => ((46875 : NNReal) / (128 : NNReal))
  | 100 => ((239597 : NNReal) / (1024 : NNReal))
  | 124 => ((1915527 : NNReal) / (32768 : NNReal))
  | 132 => ((15625 : NNReal) / (128 : NNReal))
  | 164 => ((572165 : NNReal) / (4096 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 31. -/
def t10j32HighBitTailNode031LhsNum : Nat :=
  11682050789

/-- Exact denominator of `(M v)_i` for generated row 31. -/
def t10j32HighBitTailNode031LhsDen : Nat :=
  262144

/-- Exact vector entry for generated row 31. -/
def t10j32HighBitTailNode031Vector : Nat :=
  1918835

/-- Exact cleared-denominator CW inequality for generated row 31. -/
theorem t10j32HighBitTailNode031Bound :
    t10j32HighBitTailNode031LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode031Vector * t10j32HighBitTailNode031LhsDen := by
  norm_num [t10j32HighBitTailNode031LhsNum, t10j32HighBitTailNode031LhsDen, t10j32HighBitTailNode031Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 31. -/
def t10j32HighBitTailNode031Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode031LhsNum
  lhsDen := t10j32HighBitTailNode031LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode031LhsDen]
  vector := t10j32HighBitTailNode031Vector
  vector_pos := by norm_num [t10j32HighBitTailNode031Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode031Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 31. -/
theorem t10j32HighBitTailNode031MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (31 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode031LhsNum : NNReal) / (t10j32HighBitTailNode031LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode031Support,
      t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) dst *
        t10j32HighBitTailCWBasis.vector dst
  · symm
    refine Finset.sum_subset (by intro dst hdst; simp) ?_
    intro dst _ hdst
    fin_cases dst <;>
      first
      | exact False.elim (hdst (by decide))
      | change (0 : NNReal) * _ = 0
        norm_num
  ·
    have h004 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (4 : T10J32HighBitTailState) := by
      change (((111 : NNReal) / (32768 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode031Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h012 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (12 : T10J32HighBitTailState) := by
      change (((243 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode031Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h020 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (20 : T10J32HighBitTailState) := by
      change (((139 : NNReal) / (65536 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode031Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h028 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (28 : T10J32HighBitTailState) := by
      change (((63 : NNReal) / (32768 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode031Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h036 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (36 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (36 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (36 : T10J32HighBitTailState) := by
      change (((249 : NNReal) / (262144 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode031Term (36 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h044 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (44 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (44 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (44 : T10J32HighBitTailState) := by
      change (((177 : NNReal) / (131072 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode031Term (44 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h052 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (52 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (52 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (52 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (32768 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode031Term (52 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h060 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (60 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (60 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (60 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode031Term (60 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h076 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (76 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (76 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (76 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode031Term (76 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h084 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (84 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (84 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (84 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (32768 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode031Term (84 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h092 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (92 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (92 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (92 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode031Term (92 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h100 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (100 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (100 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (100 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode031Term (100 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h124 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (124 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (124 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (124 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode031Term (124 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h132 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (132 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (132 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (132 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode031Term (132 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    have h164 :
        t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) (164 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (164 : T10J32HighBitTailState) =
          t10j32HighBitTailNode031Term (164 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16384 : NNReal)) * (2288660 : NNReal)) =
        t10j32HighBitTailNode031Term (164 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode031Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode031Support,
          t10j32HighBitTailMatrix (31 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode031Support, t10j32HighBitTailNode031Term dst := by
        simp [t10j32HighBitTailNode031Support, h004, h012, h020, h028, h036, h044, h052, h060, h076, h084, h092, h100, h124, h132, h164]
      _ = (t10j32HighBitTailNode031LhsNum : NNReal) / (t10j32HighBitTailNode031LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode031Support, t10j32HighBitTailNode031Term]
        norm_num [t10j32HighBitTailNode031LhsNum, t10j32HighBitTailNode031LhsDen]

/-- Evaluated row certificate for generated row 31. -/
def t10j32HighBitTailNode031Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (31 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode031Row
  lhs_eq := by simpa using t10j32HighBitTailNode031MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode031Row]

end Generated
end CollatzShadowing
