import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 48. -/
def t10j32HighBitTailNode048Label : String :=
  "v2=3|odd=0|h=0"

/-- Destination support of generated row 48. -/
def t10j32HighBitTailNode048Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 48. -/
def t10j32HighBitTailNode048LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 48. -/
def t10j32HighBitTailNode048LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 48. -/
def t10j32HighBitTailNode048Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 48. -/
theorem t10j32HighBitTailNode048Bound :
    t10j32HighBitTailNode048LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode048Vector * t10j32HighBitTailNode048LhsDen := by
  norm_num [t10j32HighBitTailNode048LhsNum, t10j32HighBitTailNode048LhsDen, t10j32HighBitTailNode048Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 48. -/
def t10j32HighBitTailNode048Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode048LhsNum
  lhsDen := t10j32HighBitTailNode048LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode048LhsDen]
  vector := t10j32HighBitTailNode048Vector
  vector_pos := by norm_num [t10j32HighBitTailNode048Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode048Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 48. -/
theorem t10j32HighBitTailNode048MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (48 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode048LhsNum : NNReal) / (t10j32HighBitTailNode048LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode048LhsNum, t10j32HighBitTailNode048LhsDen]

/-- Evaluated row certificate for generated row 48. -/
def t10j32HighBitTailNode048Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (48 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode048Row
  lhs_eq := by simpa using t10j32HighBitTailNode048MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode048Row]


/-- State label for generated row 49. -/
def t10j32HighBitTailNode049Label : String :=
  "v2=3|odd=0|h=1"

/-- Destination support of generated row 49. -/
def t10j32HighBitTailNode049Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 49. -/
def t10j32HighBitTailNode049LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 49. -/
def t10j32HighBitTailNode049LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 49. -/
def t10j32HighBitTailNode049Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 49. -/
theorem t10j32HighBitTailNode049Bound :
    t10j32HighBitTailNode049LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode049Vector * t10j32HighBitTailNode049LhsDen := by
  norm_num [t10j32HighBitTailNode049LhsNum, t10j32HighBitTailNode049LhsDen, t10j32HighBitTailNode049Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 49. -/
def t10j32HighBitTailNode049Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode049LhsNum
  lhsDen := t10j32HighBitTailNode049LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode049LhsDen]
  vector := t10j32HighBitTailNode049Vector
  vector_pos := by norm_num [t10j32HighBitTailNode049Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode049Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 49. -/
theorem t10j32HighBitTailNode049MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (49 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode049LhsNum : NNReal) / (t10j32HighBitTailNode049LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode049LhsNum, t10j32HighBitTailNode049LhsDen]

/-- Evaluated row certificate for generated row 49. -/
def t10j32HighBitTailNode049Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (49 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode049Row
  lhs_eq := by simpa using t10j32HighBitTailNode049MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode049Row]


/-- State label for generated row 50. -/
def t10j32HighBitTailNode050Label : String :=
  "v2=3|odd=0|h=2"

/-- Destination support of generated row 50. -/
def t10j32HighBitTailNode050Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 50. -/
def t10j32HighBitTailNode050LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 50. -/
def t10j32HighBitTailNode050LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 50. -/
def t10j32HighBitTailNode050Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 50. -/
theorem t10j32HighBitTailNode050Bound :
    t10j32HighBitTailNode050LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode050Vector * t10j32HighBitTailNode050LhsDen := by
  norm_num [t10j32HighBitTailNode050LhsNum, t10j32HighBitTailNode050LhsDen, t10j32HighBitTailNode050Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 50. -/
def t10j32HighBitTailNode050Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode050LhsNum
  lhsDen := t10j32HighBitTailNode050LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode050LhsDen]
  vector := t10j32HighBitTailNode050Vector
  vector_pos := by norm_num [t10j32HighBitTailNode050Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode050Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 50. -/
theorem t10j32HighBitTailNode050MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (50 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode050LhsNum : NNReal) / (t10j32HighBitTailNode050LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode050LhsNum, t10j32HighBitTailNode050LhsDen]

/-- Evaluated row certificate for generated row 50. -/
def t10j32HighBitTailNode050Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (50 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode050Row
  lhs_eq := by simpa using t10j32HighBitTailNode050MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode050Row]


/-- State label for generated row 51. -/
def t10j32HighBitTailNode051Label : String :=
  "v2=3|odd=0|h=3"

/-- Destination support of generated row 51. -/
def t10j32HighBitTailNode051Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 51. -/
def t10j32HighBitTailNode051LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 51. -/
def t10j32HighBitTailNode051LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 51. -/
def t10j32HighBitTailNode051Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 51. -/
theorem t10j32HighBitTailNode051Bound :
    t10j32HighBitTailNode051LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode051Vector * t10j32HighBitTailNode051LhsDen := by
  norm_num [t10j32HighBitTailNode051LhsNum, t10j32HighBitTailNode051LhsDen, t10j32HighBitTailNode051Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 51. -/
def t10j32HighBitTailNode051Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode051LhsNum
  lhsDen := t10j32HighBitTailNode051LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode051LhsDen]
  vector := t10j32HighBitTailNode051Vector
  vector_pos := by norm_num [t10j32HighBitTailNode051Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode051Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 51. -/
theorem t10j32HighBitTailNode051MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (51 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode051LhsNum : NNReal) / (t10j32HighBitTailNode051LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode051LhsNum, t10j32HighBitTailNode051LhsDen]

/-- Evaluated row certificate for generated row 51. -/
def t10j32HighBitTailNode051Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (51 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode051Row
  lhs_eq := by simpa using t10j32HighBitTailNode051MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode051Row]


/-- State label for generated row 52. -/
def t10j32HighBitTailNode052Label : String :=
  "v2=3|odd=1|h=0"

/-- Destination support of generated row 52. -/
def t10j32HighBitTailNode052Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 37, 45, 53, 61, 69, 77, 93}

/-- Exact generated summand values for row 52. -/
noncomputable def t10j32HighBitTailNode052Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((8282909 : NNReal) / (512 : NNReal))
  | 13 => ((769830873 : NNReal) / (65536 : NNReal))
  | 21 => ((122104413 : NNReal) / (32768 : NNReal))
  | 29 => ((1022739055 : NNReal) / (262144 : NNReal))
  | 37 => ((4722957 : NNReal) / (4096 : NNReal))
  | 45 => ((1227936483 : NNReal) / (65536 : NNReal))
  | 53 => ((9967455 : NNReal) / (8192 : NNReal))
  | 61 => ((4791235 : NNReal) / (4096 : NNReal))
  | 69 => ((15625 : NNReal) / (128 : NNReal))
  | 77 => ((15625 : NNReal) / (64 : NNReal))
  | 93 => ((46875 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 52. -/
def t10j32HighBitTailNode052LhsNum : Nat :=
  15447360039

/-- Exact denominator of `(M v)_i` for generated row 52. -/
def t10j32HighBitTailNode052LhsDen : Nat :=
  262144

/-- Exact vector entry for generated row 52. -/
def t10j32HighBitTailNode052Vector : Nat :=
  2214990

/-- Exact cleared-denominator CW inequality for generated row 52. -/
theorem t10j32HighBitTailNode052Bound :
    t10j32HighBitTailNode052LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode052Vector * t10j32HighBitTailNode052LhsDen := by
  norm_num [t10j32HighBitTailNode052LhsNum, t10j32HighBitTailNode052LhsDen, t10j32HighBitTailNode052Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 52. -/
def t10j32HighBitTailNode052Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode052LhsNum
  lhsDen := t10j32HighBitTailNode052LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode052LhsDen]
  vector := t10j32HighBitTailNode052Vector
  vector_pos := by norm_num [t10j32HighBitTailNode052Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode052Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 52. -/
theorem t10j32HighBitTailNode052MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (52 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode052LhsNum : NNReal) / (t10j32HighBitTailNode052LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode052Support,
      t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (5 : T10J32HighBitTailState) := by
      change (((101 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode052Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h013 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (13 : T10J32HighBitTailState) := by
      change (((357 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode052Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h021 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (21 : T10J32HighBitTailState) := by
      change (((87 : NNReal) / (32768 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode052Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h029 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (29 : T10J32HighBitTailState) := by
      change (((533 : NNReal) / (262144 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode052Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h037 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (37 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (37 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (37 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode052Term (37 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h045 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (45 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (45 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (45 : T10J32HighBitTailState) := by
      change (((97 : NNReal) / (65536 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode052Term (45 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h053 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (53 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (53 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (53 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (16384 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode052Term (53 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h061 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (61 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (61 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (61 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode052Term (61 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h069 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (69 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (69 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (69 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode052Term (69 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h077 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (77 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (77 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (77 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode052Term (77 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    have h093 :
        t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) (93 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (93 : T10J32HighBitTailState) =
          t10j32HighBitTailNode052Term (93 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode052Term (93 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode052Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode052Support,
          t10j32HighBitTailMatrix (52 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode052Support, t10j32HighBitTailNode052Term dst := by
        simp [t10j32HighBitTailNode052Support, h005, h013, h021, h029, h037, h045, h053, h061, h069, h077, h093]
      _ = (t10j32HighBitTailNode052LhsNum : NNReal) / (t10j32HighBitTailNode052LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode052Support, t10j32HighBitTailNode052Term]
        norm_num [t10j32HighBitTailNode052LhsNum, t10j32HighBitTailNode052LhsDen]

/-- Evaluated row certificate for generated row 52. -/
def t10j32HighBitTailNode052Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (52 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode052Row
  lhs_eq := by simpa using t10j32HighBitTailNode052MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode052Row]


/-- State label for generated row 53. -/
def t10j32HighBitTailNode053Label : String :=
  "v2=3|odd=1|h=1"

/-- Destination support of generated row 53. -/
def t10j32HighBitTailNode053Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 38, 46, 54, 62, 70, 78, 94}

/-- Exact generated summand values for row 53. -/
noncomputable def t10j32HighBitTailNode053Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((8282909 : NNReal) / (512 : NNReal))
  | 14 => ((769830873 : NNReal) / (65536 : NNReal))
  | 22 => ((122104413 : NNReal) / (32768 : NNReal))
  | 30 => ((1022739055 : NNReal) / (262144 : NNReal))
  | 38 => ((4722957 : NNReal) / (4096 : NNReal))
  | 46 => ((1227936483 : NNReal) / (65536 : NNReal))
  | 54 => ((9967455 : NNReal) / (8192 : NNReal))
  | 62 => ((4791235 : NNReal) / (4096 : NNReal))
  | 70 => ((15625 : NNReal) / (128 : NNReal))
  | 78 => ((15625 : NNReal) / (64 : NNReal))
  | 94 => ((46875 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 53. -/
def t10j32HighBitTailNode053LhsNum : Nat :=
  15447360039

/-- Exact denominator of `(M v)_i` for generated row 53. -/
def t10j32HighBitTailNode053LhsDen : Nat :=
  262144

/-- Exact vector entry for generated row 53. -/
def t10j32HighBitTailNode053Vector : Nat :=
  2214990

/-- Exact cleared-denominator CW inequality for generated row 53. -/
theorem t10j32HighBitTailNode053Bound :
    t10j32HighBitTailNode053LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode053Vector * t10j32HighBitTailNode053LhsDen := by
  norm_num [t10j32HighBitTailNode053LhsNum, t10j32HighBitTailNode053LhsDen, t10j32HighBitTailNode053Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 53. -/
def t10j32HighBitTailNode053Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode053LhsNum
  lhsDen := t10j32HighBitTailNode053LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode053LhsDen]
  vector := t10j32HighBitTailNode053Vector
  vector_pos := by norm_num [t10j32HighBitTailNode053Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode053Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 53. -/
theorem t10j32HighBitTailNode053MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (53 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode053LhsNum : NNReal) / (t10j32HighBitTailNode053LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode053Support,
      t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (6 : T10J32HighBitTailState) := by
      change (((101 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode053Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h014 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (14 : T10J32HighBitTailState) := by
      change (((357 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode053Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h022 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (22 : T10J32HighBitTailState) := by
      change (((87 : NNReal) / (32768 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode053Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h030 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (30 : T10J32HighBitTailState) := by
      change (((533 : NNReal) / (262144 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode053Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h038 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (38 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (38 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (38 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode053Term (38 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h046 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (46 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (46 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (46 : T10J32HighBitTailState) := by
      change (((97 : NNReal) / (65536 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode053Term (46 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h054 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (54 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (54 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (54 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (16384 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode053Term (54 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h062 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (62 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (62 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (62 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode053Term (62 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h070 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (70 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (70 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (70 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode053Term (70 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h078 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (78 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (78 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (78 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode053Term (78 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    have h094 :
        t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) (94 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (94 : T10J32HighBitTailState) =
          t10j32HighBitTailNode053Term (94 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode053Term (94 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode053Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode053Support,
          t10j32HighBitTailMatrix (53 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode053Support, t10j32HighBitTailNode053Term dst := by
        simp [t10j32HighBitTailNode053Support, h006, h014, h022, h030, h038, h046, h054, h062, h070, h078, h094]
      _ = (t10j32HighBitTailNode053LhsNum : NNReal) / (t10j32HighBitTailNode053LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode053Support, t10j32HighBitTailNode053Term]
        norm_num [t10j32HighBitTailNode053LhsNum, t10j32HighBitTailNode053LhsDen]

/-- Evaluated row certificate for generated row 53. -/
def t10j32HighBitTailNode053Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (53 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode053Row
  lhs_eq := by simpa using t10j32HighBitTailNode053MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode053Row]


/-- State label for generated row 54. -/
def t10j32HighBitTailNode054Label : String :=
  "v2=3|odd=1|h=2"

/-- Destination support of generated row 54. -/
def t10j32HighBitTailNode054Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 39, 47, 55, 63, 71, 79, 95}

/-- Exact generated summand values for row 54. -/
noncomputable def t10j32HighBitTailNode054Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((8282909 : NNReal) / (512 : NNReal))
  | 15 => ((769830873 : NNReal) / (65536 : NNReal))
  | 23 => ((122104413 : NNReal) / (32768 : NNReal))
  | 31 => ((1022739055 : NNReal) / (262144 : NNReal))
  | 39 => ((4722957 : NNReal) / (4096 : NNReal))
  | 47 => ((1227936483 : NNReal) / (65536 : NNReal))
  | 55 => ((9967455 : NNReal) / (8192 : NNReal))
  | 63 => ((4791235 : NNReal) / (4096 : NNReal))
  | 71 => ((15625 : NNReal) / (128 : NNReal))
  | 79 => ((15625 : NNReal) / (64 : NNReal))
  | 95 => ((46875 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 54. -/
def t10j32HighBitTailNode054LhsNum : Nat :=
  15447360039

/-- Exact denominator of `(M v)_i` for generated row 54. -/
def t10j32HighBitTailNode054LhsDen : Nat :=
  262144

/-- Exact vector entry for generated row 54. -/
def t10j32HighBitTailNode054Vector : Nat :=
  2214990

/-- Exact cleared-denominator CW inequality for generated row 54. -/
theorem t10j32HighBitTailNode054Bound :
    t10j32HighBitTailNode054LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode054Vector * t10j32HighBitTailNode054LhsDen := by
  norm_num [t10j32HighBitTailNode054LhsNum, t10j32HighBitTailNode054LhsDen, t10j32HighBitTailNode054Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 54. -/
def t10j32HighBitTailNode054Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode054LhsNum
  lhsDen := t10j32HighBitTailNode054LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode054LhsDen]
  vector := t10j32HighBitTailNode054Vector
  vector_pos := by norm_num [t10j32HighBitTailNode054Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode054Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 54. -/
theorem t10j32HighBitTailNode054MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (54 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode054LhsNum : NNReal) / (t10j32HighBitTailNode054LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode054Support,
      t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (7 : T10J32HighBitTailState) := by
      change (((101 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode054Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h015 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (15 : T10J32HighBitTailState) := by
      change (((357 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode054Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h023 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (23 : T10J32HighBitTailState) := by
      change (((87 : NNReal) / (32768 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode054Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h031 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (31 : T10J32HighBitTailState) := by
      change (((533 : NNReal) / (262144 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode054Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h039 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (39 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (39 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (39 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode054Term (39 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h047 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (47 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (47 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (47 : T10J32HighBitTailState) := by
      change (((97 : NNReal) / (65536 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode054Term (47 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h055 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (55 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (55 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (55 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (16384 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode054Term (55 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h063 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (63 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (63 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (63 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode054Term (63 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h071 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (71 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (71 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (71 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode054Term (71 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h079 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (79 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (79 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (79 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode054Term (79 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    have h095 :
        t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) (95 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (95 : T10J32HighBitTailState) =
          t10j32HighBitTailNode054Term (95 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode054Term (95 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode054Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode054Support,
          t10j32HighBitTailMatrix (54 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode054Support, t10j32HighBitTailNode054Term dst := by
        simp [t10j32HighBitTailNode054Support, h007, h015, h023, h031, h039, h047, h055, h063, h071, h079, h095]
      _ = (t10j32HighBitTailNode054LhsNum : NNReal) / (t10j32HighBitTailNode054LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode054Support, t10j32HighBitTailNode054Term]
        norm_num [t10j32HighBitTailNode054LhsNum, t10j32HighBitTailNode054LhsDen]

/-- Evaluated row certificate for generated row 54. -/
def t10j32HighBitTailNode054Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (54 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode054Row
  lhs_eq := by simpa using t10j32HighBitTailNode054MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode054Row]


/-- State label for generated row 55. -/
def t10j32HighBitTailNode055Label : String :=
  "v2=3|odd=1|h=3"

/-- Destination support of generated row 55. -/
def t10j32HighBitTailNode055Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 36, 44, 52, 60, 68, 76, 92}

/-- Exact generated summand values for row 55. -/
noncomputable def t10j32HighBitTailNode055Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((8282909 : NNReal) / (512 : NNReal))
  | 12 => ((769830873 : NNReal) / (65536 : NNReal))
  | 20 => ((122104413 : NNReal) / (32768 : NNReal))
  | 28 => ((1022739055 : NNReal) / (262144 : NNReal))
  | 36 => ((4722957 : NNReal) / (4096 : NNReal))
  | 44 => ((1227936483 : NNReal) / (65536 : NNReal))
  | 52 => ((9967455 : NNReal) / (8192 : NNReal))
  | 60 => ((4791235 : NNReal) / (4096 : NNReal))
  | 68 => ((15625 : NNReal) / (128 : NNReal))
  | 76 => ((15625 : NNReal) / (64 : NNReal))
  | 92 => ((46875 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 55. -/
def t10j32HighBitTailNode055LhsNum : Nat :=
  15447360039

/-- Exact denominator of `(M v)_i` for generated row 55. -/
def t10j32HighBitTailNode055LhsDen : Nat :=
  262144

/-- Exact vector entry for generated row 55. -/
def t10j32HighBitTailNode055Vector : Nat :=
  2214990

/-- Exact cleared-denominator CW inequality for generated row 55. -/
theorem t10j32HighBitTailNode055Bound :
    t10j32HighBitTailNode055LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode055Vector * t10j32HighBitTailNode055LhsDen := by
  norm_num [t10j32HighBitTailNode055LhsNum, t10j32HighBitTailNode055LhsDen, t10j32HighBitTailNode055Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 55. -/
def t10j32HighBitTailNode055Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode055LhsNum
  lhsDen := t10j32HighBitTailNode055LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode055LhsDen]
  vector := t10j32HighBitTailNode055Vector
  vector_pos := by norm_num [t10j32HighBitTailNode055Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode055Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 55. -/
theorem t10j32HighBitTailNode055MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (55 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode055LhsNum : NNReal) / (t10j32HighBitTailNode055LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode055Support,
      t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (4 : T10J32HighBitTailState) := by
      change (((101 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode055Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h012 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (12 : T10J32HighBitTailState) := by
      change (((357 : NNReal) / (65536 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode055Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h020 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (20 : T10J32HighBitTailState) := by
      change (((87 : NNReal) / (32768 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode055Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h028 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (28 : T10J32HighBitTailState) := by
      change (((533 : NNReal) / (262144 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode055Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h036 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (36 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (36 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (36 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode055Term (36 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h044 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (44 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (44 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (44 : T10J32HighBitTailState) := by
      change (((97 : NNReal) / (65536 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode055Term (44 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h052 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (52 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (52 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (52 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (16384 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode055Term (52 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h060 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (60 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (60 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (60 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode055Term (60 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h068 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (68 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (68 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (68 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode055Term (68 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h076 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (76 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (76 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (76 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode055Term (76 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    have h092 :
        t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) (92 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (92 : T10J32HighBitTailState) =
          t10j32HighBitTailNode055Term (92 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode055Term (92 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode055Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode055Support,
          t10j32HighBitTailMatrix (55 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode055Support, t10j32HighBitTailNode055Term dst := by
        simp [t10j32HighBitTailNode055Support, h004, h012, h020, h028, h036, h044, h052, h060, h068, h076, h092]
      _ = (t10j32HighBitTailNode055LhsNum : NNReal) / (t10j32HighBitTailNode055LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode055Support, t10j32HighBitTailNode055Term]
        norm_num [t10j32HighBitTailNode055LhsNum, t10j32HighBitTailNode055LhsDen]

/-- Evaluated row certificate for generated row 55. -/
def t10j32HighBitTailNode055Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (55 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode055Row
  lhs_eq := by simpa using t10j32HighBitTailNode055MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode055Row]


/-- State label for generated row 56. -/
def t10j32HighBitTailNode056Label : String :=
  "v2=3|odd=2|h=0"

/-- Destination support of generated row 56. -/
def t10j32HighBitTailNode056Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 56. -/
def t10j32HighBitTailNode056LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 56. -/
def t10j32HighBitTailNode056LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 56. -/
def t10j32HighBitTailNode056Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 56. -/
theorem t10j32HighBitTailNode056Bound :
    t10j32HighBitTailNode056LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode056Vector * t10j32HighBitTailNode056LhsDen := by
  norm_num [t10j32HighBitTailNode056LhsNum, t10j32HighBitTailNode056LhsDen, t10j32HighBitTailNode056Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 56. -/
def t10j32HighBitTailNode056Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode056LhsNum
  lhsDen := t10j32HighBitTailNode056LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode056LhsDen]
  vector := t10j32HighBitTailNode056Vector
  vector_pos := by norm_num [t10j32HighBitTailNode056Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode056Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 56. -/
theorem t10j32HighBitTailNode056MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (56 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode056LhsNum : NNReal) / (t10j32HighBitTailNode056LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode056LhsNum, t10j32HighBitTailNode056LhsDen]

/-- Evaluated row certificate for generated row 56. -/
def t10j32HighBitTailNode056Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (56 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode056Row
  lhs_eq := by simpa using t10j32HighBitTailNode056MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode056Row]


/-- State label for generated row 57. -/
def t10j32HighBitTailNode057Label : String :=
  "v2=3|odd=2|h=1"

/-- Destination support of generated row 57. -/
def t10j32HighBitTailNode057Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 57. -/
def t10j32HighBitTailNode057LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 57. -/
def t10j32HighBitTailNode057LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 57. -/
def t10j32HighBitTailNode057Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 57. -/
theorem t10j32HighBitTailNode057Bound :
    t10j32HighBitTailNode057LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode057Vector * t10j32HighBitTailNode057LhsDen := by
  norm_num [t10j32HighBitTailNode057LhsNum, t10j32HighBitTailNode057LhsDen, t10j32HighBitTailNode057Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 57. -/
def t10j32HighBitTailNode057Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode057LhsNum
  lhsDen := t10j32HighBitTailNode057LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode057LhsDen]
  vector := t10j32HighBitTailNode057Vector
  vector_pos := by norm_num [t10j32HighBitTailNode057Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode057Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 57. -/
theorem t10j32HighBitTailNode057MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (57 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode057LhsNum : NNReal) / (t10j32HighBitTailNode057LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode057LhsNum, t10j32HighBitTailNode057LhsDen]

/-- Evaluated row certificate for generated row 57. -/
def t10j32HighBitTailNode057Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (57 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode057Row
  lhs_eq := by simpa using t10j32HighBitTailNode057MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode057Row]


/-- State label for generated row 58. -/
def t10j32HighBitTailNode058Label : String :=
  "v2=3|odd=2|h=2"

/-- Destination support of generated row 58. -/
def t10j32HighBitTailNode058Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 58. -/
def t10j32HighBitTailNode058LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 58. -/
def t10j32HighBitTailNode058LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 58. -/
def t10j32HighBitTailNode058Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 58. -/
theorem t10j32HighBitTailNode058Bound :
    t10j32HighBitTailNode058LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode058Vector * t10j32HighBitTailNode058LhsDen := by
  norm_num [t10j32HighBitTailNode058LhsNum, t10j32HighBitTailNode058LhsDen, t10j32HighBitTailNode058Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 58. -/
def t10j32HighBitTailNode058Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode058LhsNum
  lhsDen := t10j32HighBitTailNode058LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode058LhsDen]
  vector := t10j32HighBitTailNode058Vector
  vector_pos := by norm_num [t10j32HighBitTailNode058Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode058Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 58. -/
theorem t10j32HighBitTailNode058MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (58 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode058LhsNum : NNReal) / (t10j32HighBitTailNode058LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode058LhsNum, t10j32HighBitTailNode058LhsDen]

/-- Evaluated row certificate for generated row 58. -/
def t10j32HighBitTailNode058Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (58 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode058Row
  lhs_eq := by simpa using t10j32HighBitTailNode058MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode058Row]


/-- State label for generated row 59. -/
def t10j32HighBitTailNode059Label : String :=
  "v2=3|odd=2|h=3"

/-- Destination support of generated row 59. -/
def t10j32HighBitTailNode059Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 59. -/
def t10j32HighBitTailNode059LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 59. -/
def t10j32HighBitTailNode059LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 59. -/
def t10j32HighBitTailNode059Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 59. -/
theorem t10j32HighBitTailNode059Bound :
    t10j32HighBitTailNode059LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode059Vector * t10j32HighBitTailNode059LhsDen := by
  norm_num [t10j32HighBitTailNode059LhsNum, t10j32HighBitTailNode059LhsDen, t10j32HighBitTailNode059Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 59. -/
def t10j32HighBitTailNode059Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode059LhsNum
  lhsDen := t10j32HighBitTailNode059LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode059LhsDen]
  vector := t10j32HighBitTailNode059Vector
  vector_pos := by norm_num [t10j32HighBitTailNode059Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode059Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 59. -/
theorem t10j32HighBitTailNode059MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (59 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode059LhsNum : NNReal) / (t10j32HighBitTailNode059LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode059LhsNum, t10j32HighBitTailNode059LhsDen]

/-- Evaluated row certificate for generated row 59. -/
def t10j32HighBitTailNode059Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (59 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode059Row
  lhs_eq := by simpa using t10j32HighBitTailNode059MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode059Row]


/-- State label for generated row 60. -/
def t10j32HighBitTailNode060Label : String :=
  "v2=3|odd=3|h=0"

/-- Destination support of generated row 60. -/
def t10j32HighBitTailNode060Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 37, 45, 53, 61, 117}

/-- Exact generated summand values for row 60. -/
noncomputable def t10j32HighBitTailNode060Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((4674513 : NNReal) / (512 : NNReal))
  | 13 => ((109975839 : NNReal) / (16384 : NNReal))
  | 21 => ((7017495 : NNReal) / (4096 : NNReal))
  | 29 => ((5756505 : NNReal) / (1024 : NNReal))
  | 37 => ((1574319 : NNReal) / (4096 : NNReal))
  | 45 => ((37977417 : NNReal) / (2048 : NNReal))
  | 53 => ((3322485 : NNReal) / (4096 : NNReal))
  | 61 => ((958247 : NNReal) / (1024 : NNReal))
  | 117 => ((2448779 : NNReal) / (4096 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 60. -/
def t10j32HighBitTailNode060LhsNum : Nat :=
  728267935

/-- Exact denominator of `(M v)_i` for generated row 60. -/
def t10j32HighBitTailNode060LhsDen : Nat :=
  16384

/-- Exact vector entry for generated row 60. -/
def t10j32HighBitTailNode060Vector : Nat :=
  1916494

/-- Exact cleared-denominator CW inequality for generated row 60. -/
theorem t10j32HighBitTailNode060Bound :
    t10j32HighBitTailNode060LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode060Vector * t10j32HighBitTailNode060LhsDen := by
  norm_num [t10j32HighBitTailNode060LhsNum, t10j32HighBitTailNode060LhsDen, t10j32HighBitTailNode060Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 60. -/
def t10j32HighBitTailNode060Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode060LhsNum
  lhsDen := t10j32HighBitTailNode060LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode060LhsDen]
  vector := t10j32HighBitTailNode060Vector
  vector_pos := by norm_num [t10j32HighBitTailNode060Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode060Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 60. -/
theorem t10j32HighBitTailNode060MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (60 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode060LhsNum : NNReal) / (t10j32HighBitTailNode060LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode060Support,
      t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode060Term (5 : T10J32HighBitTailState) := by
      change (((57 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode060Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode060Term]
    have h013 :
        t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode060Term (13 : T10J32HighBitTailState) := by
      change (((51 : NNReal) / (16384 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode060Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode060Term]
    have h021 :
        t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode060Term (21 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (4096 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode060Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode060Term]
    have h029 :
        t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode060Term (29 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (1024 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode060Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode060Term]
    have h037 :
        t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) (37 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (37 : T10J32HighBitTailState) =
          t10j32HighBitTailNode060Term (37 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode060Term (37 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode060Term]
    have h045 :
        t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) (45 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (45 : T10J32HighBitTailState) =
          t10j32HighBitTailNode060Term (45 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (2048 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode060Term (45 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode060Term]
    have h053 :
        t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) (53 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (53 : T10J32HighBitTailState) =
          t10j32HighBitTailNode060Term (53 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode060Term (53 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode060Term]
    have h061 :
        t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) (61 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (61 : T10J32HighBitTailState) =
          t10j32HighBitTailNode060Term (61 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (2048 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode060Term (61 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode060Term]
    have h117 :
        t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) (117 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (117 : T10J32HighBitTailState) =
          t10j32HighBitTailNode060Term (117 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode060Term (117 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode060Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode060Support,
          t10j32HighBitTailMatrix (60 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode060Support, t10j32HighBitTailNode060Term dst := by
        simp [t10j32HighBitTailNode060Support, h005, h013, h021, h029, h037, h045, h053, h061, h117]
      _ = (t10j32HighBitTailNode060LhsNum : NNReal) / (t10j32HighBitTailNode060LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode060Support, t10j32HighBitTailNode060Term]
        norm_num [t10j32HighBitTailNode060LhsNum, t10j32HighBitTailNode060LhsDen]

/-- Evaluated row certificate for generated row 60. -/
def t10j32HighBitTailNode060Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (60 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode060Row
  lhs_eq := by simpa using t10j32HighBitTailNode060MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode060Row]


/-- State label for generated row 61. -/
def t10j32HighBitTailNode061Label : String :=
  "v2=3|odd=3|h=1"

/-- Destination support of generated row 61. -/
def t10j32HighBitTailNode061Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 38, 46, 54, 62, 118}

/-- Exact generated summand values for row 61. -/
noncomputable def t10j32HighBitTailNode061Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((4674513 : NNReal) / (512 : NNReal))
  | 14 => ((109975839 : NNReal) / (16384 : NNReal))
  | 22 => ((7017495 : NNReal) / (4096 : NNReal))
  | 30 => ((5756505 : NNReal) / (1024 : NNReal))
  | 38 => ((1574319 : NNReal) / (4096 : NNReal))
  | 46 => ((37977417 : NNReal) / (2048 : NNReal))
  | 54 => ((3322485 : NNReal) / (4096 : NNReal))
  | 62 => ((958247 : NNReal) / (1024 : NNReal))
  | 118 => ((2448779 : NNReal) / (4096 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 61. -/
def t10j32HighBitTailNode061LhsNum : Nat :=
  728267935

/-- Exact denominator of `(M v)_i` for generated row 61. -/
def t10j32HighBitTailNode061LhsDen : Nat :=
  16384

/-- Exact vector entry for generated row 61. -/
def t10j32HighBitTailNode061Vector : Nat :=
  1916494

/-- Exact cleared-denominator CW inequality for generated row 61. -/
theorem t10j32HighBitTailNode061Bound :
    t10j32HighBitTailNode061LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode061Vector * t10j32HighBitTailNode061LhsDen := by
  norm_num [t10j32HighBitTailNode061LhsNum, t10j32HighBitTailNode061LhsDen, t10j32HighBitTailNode061Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 61. -/
def t10j32HighBitTailNode061Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode061LhsNum
  lhsDen := t10j32HighBitTailNode061LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode061LhsDen]
  vector := t10j32HighBitTailNode061Vector
  vector_pos := by norm_num [t10j32HighBitTailNode061Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode061Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 61. -/
theorem t10j32HighBitTailNode061MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (61 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode061LhsNum : NNReal) / (t10j32HighBitTailNode061LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode061Support,
      t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode061Term (6 : T10J32HighBitTailState) := by
      change (((57 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode061Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode061Term]
    have h014 :
        t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode061Term (14 : T10J32HighBitTailState) := by
      change (((51 : NNReal) / (16384 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode061Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode061Term]
    have h022 :
        t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode061Term (22 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (4096 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode061Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode061Term]
    have h030 :
        t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode061Term (30 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (1024 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode061Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode061Term]
    have h038 :
        t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) (38 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (38 : T10J32HighBitTailState) =
          t10j32HighBitTailNode061Term (38 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode061Term (38 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode061Term]
    have h046 :
        t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) (46 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (46 : T10J32HighBitTailState) =
          t10j32HighBitTailNode061Term (46 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (2048 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode061Term (46 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode061Term]
    have h054 :
        t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) (54 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (54 : T10J32HighBitTailState) =
          t10j32HighBitTailNode061Term (54 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode061Term (54 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode061Term]
    have h062 :
        t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) (62 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (62 : T10J32HighBitTailState) =
          t10j32HighBitTailNode061Term (62 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (2048 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode061Term (62 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode061Term]
    have h118 :
        t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) (118 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (118 : T10J32HighBitTailState) =
          t10j32HighBitTailNode061Term (118 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode061Term (118 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode061Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode061Support,
          t10j32HighBitTailMatrix (61 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode061Support, t10j32HighBitTailNode061Term dst := by
        simp [t10j32HighBitTailNode061Support, h006, h014, h022, h030, h038, h046, h054, h062, h118]
      _ = (t10j32HighBitTailNode061LhsNum : NNReal) / (t10j32HighBitTailNode061LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode061Support, t10j32HighBitTailNode061Term]
        norm_num [t10j32HighBitTailNode061LhsNum, t10j32HighBitTailNode061LhsDen]

/-- Evaluated row certificate for generated row 61. -/
def t10j32HighBitTailNode061Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (61 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode061Row
  lhs_eq := by simpa using t10j32HighBitTailNode061MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode061Row]


/-- State label for generated row 62. -/
def t10j32HighBitTailNode062Label : String :=
  "v2=3|odd=3|h=2"

/-- Destination support of generated row 62. -/
def t10j32HighBitTailNode062Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 39, 47, 55, 63, 119}

/-- Exact generated summand values for row 62. -/
noncomputable def t10j32HighBitTailNode062Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((4674513 : NNReal) / (512 : NNReal))
  | 15 => ((109975839 : NNReal) / (16384 : NNReal))
  | 23 => ((7017495 : NNReal) / (4096 : NNReal))
  | 31 => ((5756505 : NNReal) / (1024 : NNReal))
  | 39 => ((1574319 : NNReal) / (4096 : NNReal))
  | 47 => ((37977417 : NNReal) / (2048 : NNReal))
  | 55 => ((3322485 : NNReal) / (4096 : NNReal))
  | 63 => ((958247 : NNReal) / (1024 : NNReal))
  | 119 => ((2448779 : NNReal) / (4096 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 62. -/
def t10j32HighBitTailNode062LhsNum : Nat :=
  728267935

/-- Exact denominator of `(M v)_i` for generated row 62. -/
def t10j32HighBitTailNode062LhsDen : Nat :=
  16384

/-- Exact vector entry for generated row 62. -/
def t10j32HighBitTailNode062Vector : Nat :=
  1916494

/-- Exact cleared-denominator CW inequality for generated row 62. -/
theorem t10j32HighBitTailNode062Bound :
    t10j32HighBitTailNode062LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode062Vector * t10j32HighBitTailNode062LhsDen := by
  norm_num [t10j32HighBitTailNode062LhsNum, t10j32HighBitTailNode062LhsDen, t10j32HighBitTailNode062Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 62. -/
def t10j32HighBitTailNode062Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode062LhsNum
  lhsDen := t10j32HighBitTailNode062LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode062LhsDen]
  vector := t10j32HighBitTailNode062Vector
  vector_pos := by norm_num [t10j32HighBitTailNode062Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode062Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 62. -/
theorem t10j32HighBitTailNode062MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (62 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode062LhsNum : NNReal) / (t10j32HighBitTailNode062LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode062Support,
      t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode062Term (7 : T10J32HighBitTailState) := by
      change (((57 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode062Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode062Term]
    have h015 :
        t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode062Term (15 : T10J32HighBitTailState) := by
      change (((51 : NNReal) / (16384 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode062Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode062Term]
    have h023 :
        t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode062Term (23 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (4096 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode062Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode062Term]
    have h031 :
        t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode062Term (31 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (1024 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode062Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode062Term]
    have h039 :
        t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) (39 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (39 : T10J32HighBitTailState) =
          t10j32HighBitTailNode062Term (39 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode062Term (39 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode062Term]
    have h047 :
        t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) (47 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (47 : T10J32HighBitTailState) =
          t10j32HighBitTailNode062Term (47 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (2048 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode062Term (47 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode062Term]
    have h055 :
        t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) (55 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (55 : T10J32HighBitTailState) =
          t10j32HighBitTailNode062Term (55 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode062Term (55 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode062Term]
    have h063 :
        t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) (63 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (63 : T10J32HighBitTailState) =
          t10j32HighBitTailNode062Term (63 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (2048 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode062Term (63 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode062Term]
    have h119 :
        t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) (119 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (119 : T10J32HighBitTailState) =
          t10j32HighBitTailNode062Term (119 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode062Term (119 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode062Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode062Support,
          t10j32HighBitTailMatrix (62 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode062Support, t10j32HighBitTailNode062Term dst := by
        simp [t10j32HighBitTailNode062Support, h007, h015, h023, h031, h039, h047, h055, h063, h119]
      _ = (t10j32HighBitTailNode062LhsNum : NNReal) / (t10j32HighBitTailNode062LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode062Support, t10j32HighBitTailNode062Term]
        norm_num [t10j32HighBitTailNode062LhsNum, t10j32HighBitTailNode062LhsDen]

/-- Evaluated row certificate for generated row 62. -/
def t10j32HighBitTailNode062Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (62 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode062Row
  lhs_eq := by simpa using t10j32HighBitTailNode062MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode062Row]


/-- State label for generated row 63. -/
def t10j32HighBitTailNode063Label : String :=
  "v2=3|odd=3|h=3"

/-- Destination support of generated row 63. -/
def t10j32HighBitTailNode063Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 36, 44, 52, 60, 116}

/-- Exact generated summand values for row 63. -/
noncomputable def t10j32HighBitTailNode063Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((4674513 : NNReal) / (512 : NNReal))
  | 12 => ((109975839 : NNReal) / (16384 : NNReal))
  | 20 => ((7017495 : NNReal) / (4096 : NNReal))
  | 28 => ((5756505 : NNReal) / (1024 : NNReal))
  | 36 => ((1574319 : NNReal) / (4096 : NNReal))
  | 44 => ((37977417 : NNReal) / (2048 : NNReal))
  | 52 => ((3322485 : NNReal) / (4096 : NNReal))
  | 60 => ((958247 : NNReal) / (1024 : NNReal))
  | 116 => ((2448779 : NNReal) / (4096 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 63. -/
def t10j32HighBitTailNode063LhsNum : Nat :=
  728267935

/-- Exact denominator of `(M v)_i` for generated row 63. -/
def t10j32HighBitTailNode063LhsDen : Nat :=
  16384

/-- Exact vector entry for generated row 63. -/
def t10j32HighBitTailNode063Vector : Nat :=
  1916494

/-- Exact cleared-denominator CW inequality for generated row 63. -/
theorem t10j32HighBitTailNode063Bound :
    t10j32HighBitTailNode063LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode063Vector * t10j32HighBitTailNode063LhsDen := by
  norm_num [t10j32HighBitTailNode063LhsNum, t10j32HighBitTailNode063LhsDen, t10j32HighBitTailNode063Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 63. -/
def t10j32HighBitTailNode063Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode063LhsNum
  lhsDen := t10j32HighBitTailNode063LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode063LhsDen]
  vector := t10j32HighBitTailNode063Vector
  vector_pos := by norm_num [t10j32HighBitTailNode063Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode063Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 63. -/
theorem t10j32HighBitTailNode063MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (63 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode063LhsNum : NNReal) / (t10j32HighBitTailNode063LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode063Support,
      t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode063Term (4 : T10J32HighBitTailState) := by
      change (((57 : NNReal) / (16384 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode063Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode063Term]
    have h012 :
        t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode063Term (12 : T10J32HighBitTailState) := by
      change (((51 : NNReal) / (16384 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode063Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode063Term]
    have h020 :
        t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode063Term (20 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (4096 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode063Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode063Term]
    have h028 :
        t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode063Term (28 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (1024 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode063Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode063Term]
    have h036 :
        t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) (36 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (36 : T10J32HighBitTailState) =
          t10j32HighBitTailNode063Term (36 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode063Term (36 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode063Term]
    have h044 :
        t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) (44 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (44 : T10J32HighBitTailState) =
          t10j32HighBitTailNode063Term (44 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (2048 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode063Term (44 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode063Term]
    have h052 :
        t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) (52 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (52 : T10J32HighBitTailState) =
          t10j32HighBitTailNode063Term (52 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode063Term (52 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode063Term]
    have h060 :
        t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) (60 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (60 : T10J32HighBitTailState) =
          t10j32HighBitTailNode063Term (60 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (2048 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode063Term (60 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode063Term]
    have h116 :
        t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) (116 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (116 : T10J32HighBitTailState) =
          t10j32HighBitTailNode063Term (116 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode063Term (116 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode063Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode063Support,
          t10j32HighBitTailMatrix (63 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode063Support, t10j32HighBitTailNode063Term dst := by
        simp [t10j32HighBitTailNode063Support, h004, h012, h020, h028, h036, h044, h052, h060, h116]
      _ = (t10j32HighBitTailNode063LhsNum : NNReal) / (t10j32HighBitTailNode063LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode063Support, t10j32HighBitTailNode063Term]
        norm_num [t10j32HighBitTailNode063LhsNum, t10j32HighBitTailNode063LhsDen]

/-- Evaluated row certificate for generated row 63. -/
def t10j32HighBitTailNode063Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (63 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode063Row
  lhs_eq := by simpa using t10j32HighBitTailNode063MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode063Row]

end Generated
end CollatzShadowing
