import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 64. -/
def t10j32HighBitTailNode064Label : String :=
  "v2=4|odd=0|h=0"

/-- Destination support of generated row 64. -/
def t10j32HighBitTailNode064Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 64. -/
def t10j32HighBitTailNode064LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 64. -/
def t10j32HighBitTailNode064LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 64. -/
def t10j32HighBitTailNode064Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 64. -/
theorem t10j32HighBitTailNode064Bound :
    t10j32HighBitTailNode064LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode064Vector * t10j32HighBitTailNode064LhsDen := by
  norm_num [t10j32HighBitTailNode064LhsNum, t10j32HighBitTailNode064LhsDen, t10j32HighBitTailNode064Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 64. -/
def t10j32HighBitTailNode064Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode064LhsNum
  lhsDen := t10j32HighBitTailNode064LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode064LhsDen]
  vector := t10j32HighBitTailNode064Vector
  vector_pos := by norm_num [t10j32HighBitTailNode064Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode064Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 64. -/
theorem t10j32HighBitTailNode064MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (64 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode064LhsNum : NNReal) / (t10j32HighBitTailNode064LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode064LhsNum, t10j32HighBitTailNode064LhsDen]

/-- Evaluated row certificate for generated row 64. -/
def t10j32HighBitTailNode064Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (64 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode064Row
  lhs_eq := by simpa using t10j32HighBitTailNode064MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode064Row]


/-- State label for generated row 65. -/
def t10j32HighBitTailNode065Label : String :=
  "v2=4|odd=0|h=1"

/-- Destination support of generated row 65. -/
def t10j32HighBitTailNode065Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 65. -/
def t10j32HighBitTailNode065LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 65. -/
def t10j32HighBitTailNode065LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 65. -/
def t10j32HighBitTailNode065Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 65. -/
theorem t10j32HighBitTailNode065Bound :
    t10j32HighBitTailNode065LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode065Vector * t10j32HighBitTailNode065LhsDen := by
  norm_num [t10j32HighBitTailNode065LhsNum, t10j32HighBitTailNode065LhsDen, t10j32HighBitTailNode065Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 65. -/
def t10j32HighBitTailNode065Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode065LhsNum
  lhsDen := t10j32HighBitTailNode065LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode065LhsDen]
  vector := t10j32HighBitTailNode065Vector
  vector_pos := by norm_num [t10j32HighBitTailNode065Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode065Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 65. -/
theorem t10j32HighBitTailNode065MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (65 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode065LhsNum : NNReal) / (t10j32HighBitTailNode065LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode065LhsNum, t10j32HighBitTailNode065LhsDen]

/-- Evaluated row certificate for generated row 65. -/
def t10j32HighBitTailNode065Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (65 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode065Row
  lhs_eq := by simpa using t10j32HighBitTailNode065MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode065Row]


/-- State label for generated row 66. -/
def t10j32HighBitTailNode066Label : String :=
  "v2=4|odd=0|h=2"

/-- Destination support of generated row 66. -/
def t10j32HighBitTailNode066Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 66. -/
def t10j32HighBitTailNode066LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 66. -/
def t10j32HighBitTailNode066LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 66. -/
def t10j32HighBitTailNode066Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 66. -/
theorem t10j32HighBitTailNode066Bound :
    t10j32HighBitTailNode066LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode066Vector * t10j32HighBitTailNode066LhsDen := by
  norm_num [t10j32HighBitTailNode066LhsNum, t10j32HighBitTailNode066LhsDen, t10j32HighBitTailNode066Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 66. -/
def t10j32HighBitTailNode066Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode066LhsNum
  lhsDen := t10j32HighBitTailNode066LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode066LhsDen]
  vector := t10j32HighBitTailNode066Vector
  vector_pos := by norm_num [t10j32HighBitTailNode066Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode066Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 66. -/
theorem t10j32HighBitTailNode066MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (66 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode066LhsNum : NNReal) / (t10j32HighBitTailNode066LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode066LhsNum, t10j32HighBitTailNode066LhsDen]

/-- Evaluated row certificate for generated row 66. -/
def t10j32HighBitTailNode066Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (66 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode066Row
  lhs_eq := by simpa using t10j32HighBitTailNode066MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode066Row]


/-- State label for generated row 67. -/
def t10j32HighBitTailNode067Label : String :=
  "v2=4|odd=0|h=3"

/-- Destination support of generated row 67. -/
def t10j32HighBitTailNode067Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 67. -/
def t10j32HighBitTailNode067LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 67. -/
def t10j32HighBitTailNode067LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 67. -/
def t10j32HighBitTailNode067Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 67. -/
theorem t10j32HighBitTailNode067Bound :
    t10j32HighBitTailNode067LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode067Vector * t10j32HighBitTailNode067LhsDen := by
  norm_num [t10j32HighBitTailNode067LhsNum, t10j32HighBitTailNode067LhsDen, t10j32HighBitTailNode067Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 67. -/
def t10j32HighBitTailNode067Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode067LhsNum
  lhsDen := t10j32HighBitTailNode067LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode067LhsDen]
  vector := t10j32HighBitTailNode067Vector
  vector_pos := by norm_num [t10j32HighBitTailNode067Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode067Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 67. -/
theorem t10j32HighBitTailNode067MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (67 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode067LhsNum : NNReal) / (t10j32HighBitTailNode067LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode067LhsNum, t10j32HighBitTailNode067LhsDen]

/-- Evaluated row certificate for generated row 67. -/
def t10j32HighBitTailNode067Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (67 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode067Row
  lhs_eq := by simpa using t10j32HighBitTailNode067MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode067Row]


/-- State label for generated row 68. -/
def t10j32HighBitTailNode068Label : String :=
  "v2=4|odd=1|h=0"

/-- Destination support of generated row 68. -/
def t10j32HighBitTailNode068Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 68. -/
def t10j32HighBitTailNode068LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 68. -/
def t10j32HighBitTailNode068LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 68. -/
def t10j32HighBitTailNode068Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 68. -/
theorem t10j32HighBitTailNode068Bound :
    t10j32HighBitTailNode068LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode068Vector * t10j32HighBitTailNode068LhsDen := by
  norm_num [t10j32HighBitTailNode068LhsNum, t10j32HighBitTailNode068LhsDen, t10j32HighBitTailNode068Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 68. -/
def t10j32HighBitTailNode068Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode068LhsNum
  lhsDen := t10j32HighBitTailNode068LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode068LhsDen]
  vector := t10j32HighBitTailNode068Vector
  vector_pos := by norm_num [t10j32HighBitTailNode068Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode068Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 68. -/
theorem t10j32HighBitTailNode068MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (68 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode068LhsNum : NNReal) / (t10j32HighBitTailNode068LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode068LhsNum, t10j32HighBitTailNode068LhsDen]

/-- Evaluated row certificate for generated row 68. -/
def t10j32HighBitTailNode068Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (68 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode068Row
  lhs_eq := by simpa using t10j32HighBitTailNode068MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode068Row]


/-- State label for generated row 69. -/
def t10j32HighBitTailNode069Label : String :=
  "v2=4|odd=1|h=1"

/-- Destination support of generated row 69. -/
def t10j32HighBitTailNode069Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 69. -/
def t10j32HighBitTailNode069LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 69. -/
def t10j32HighBitTailNode069LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 69. -/
def t10j32HighBitTailNode069Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 69. -/
theorem t10j32HighBitTailNode069Bound :
    t10j32HighBitTailNode069LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode069Vector * t10j32HighBitTailNode069LhsDen := by
  norm_num [t10j32HighBitTailNode069LhsNum, t10j32HighBitTailNode069LhsDen, t10j32HighBitTailNode069Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 69. -/
def t10j32HighBitTailNode069Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode069LhsNum
  lhsDen := t10j32HighBitTailNode069LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode069LhsDen]
  vector := t10j32HighBitTailNode069Vector
  vector_pos := by norm_num [t10j32HighBitTailNode069Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode069Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 69. -/
theorem t10j32HighBitTailNode069MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (69 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode069LhsNum : NNReal) / (t10j32HighBitTailNode069LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode069LhsNum, t10j32HighBitTailNode069LhsDen]

/-- Evaluated row certificate for generated row 69. -/
def t10j32HighBitTailNode069Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (69 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode069Row
  lhs_eq := by simpa using t10j32HighBitTailNode069MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode069Row]


/-- State label for generated row 70. -/
def t10j32HighBitTailNode070Label : String :=
  "v2=4|odd=1|h=2"

/-- Destination support of generated row 70. -/
def t10j32HighBitTailNode070Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 70. -/
def t10j32HighBitTailNode070LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 70. -/
def t10j32HighBitTailNode070LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 70. -/
def t10j32HighBitTailNode070Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 70. -/
theorem t10j32HighBitTailNode070Bound :
    t10j32HighBitTailNode070LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode070Vector * t10j32HighBitTailNode070LhsDen := by
  norm_num [t10j32HighBitTailNode070LhsNum, t10j32HighBitTailNode070LhsDen, t10j32HighBitTailNode070Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 70. -/
def t10j32HighBitTailNode070Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode070LhsNum
  lhsDen := t10j32HighBitTailNode070LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode070LhsDen]
  vector := t10j32HighBitTailNode070Vector
  vector_pos := by norm_num [t10j32HighBitTailNode070Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode070Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 70. -/
theorem t10j32HighBitTailNode070MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (70 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode070LhsNum : NNReal) / (t10j32HighBitTailNode070LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode070LhsNum, t10j32HighBitTailNode070LhsDen]

/-- Evaluated row certificate for generated row 70. -/
def t10j32HighBitTailNode070Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (70 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode070Row
  lhs_eq := by simpa using t10j32HighBitTailNode070MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode070Row]


/-- State label for generated row 71. -/
def t10j32HighBitTailNode071Label : String :=
  "v2=4|odd=1|h=3"

/-- Destination support of generated row 71. -/
def t10j32HighBitTailNode071Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 71. -/
def t10j32HighBitTailNode071LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 71. -/
def t10j32HighBitTailNode071LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 71. -/
def t10j32HighBitTailNode071Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 71. -/
theorem t10j32HighBitTailNode071Bound :
    t10j32HighBitTailNode071LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode071Vector * t10j32HighBitTailNode071LhsDen := by
  norm_num [t10j32HighBitTailNode071LhsNum, t10j32HighBitTailNode071LhsDen, t10j32HighBitTailNode071Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 71. -/
def t10j32HighBitTailNode071Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode071LhsNum
  lhsDen := t10j32HighBitTailNode071LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode071LhsDen]
  vector := t10j32HighBitTailNode071Vector
  vector_pos := by norm_num [t10j32HighBitTailNode071Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode071Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 71. -/
theorem t10j32HighBitTailNode071MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (71 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode071LhsNum : NNReal) / (t10j32HighBitTailNode071LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode071LhsNum, t10j32HighBitTailNode071LhsDen]

/-- Evaluated row certificate for generated row 71. -/
def t10j32HighBitTailNode071Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (71 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode071Row
  lhs_eq := by simpa using t10j32HighBitTailNode071MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode071Row]


/-- State label for generated row 72. -/
def t10j32HighBitTailNode072Label : String :=
  "v2=4|odd=2|h=0"

/-- Destination support of generated row 72. -/
def t10j32HighBitTailNode072Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 72. -/
def t10j32HighBitTailNode072LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 72. -/
def t10j32HighBitTailNode072LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 72. -/
def t10j32HighBitTailNode072Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 72. -/
theorem t10j32HighBitTailNode072Bound :
    t10j32HighBitTailNode072LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode072Vector * t10j32HighBitTailNode072LhsDen := by
  norm_num [t10j32HighBitTailNode072LhsNum, t10j32HighBitTailNode072LhsDen, t10j32HighBitTailNode072Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 72. -/
def t10j32HighBitTailNode072Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode072LhsNum
  lhsDen := t10j32HighBitTailNode072LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode072LhsDen]
  vector := t10j32HighBitTailNode072Vector
  vector_pos := by norm_num [t10j32HighBitTailNode072Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode072Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 72. -/
theorem t10j32HighBitTailNode072MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (72 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode072LhsNum : NNReal) / (t10j32HighBitTailNode072LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode072LhsNum, t10j32HighBitTailNode072LhsDen]

/-- Evaluated row certificate for generated row 72. -/
def t10j32HighBitTailNode072Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (72 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode072Row
  lhs_eq := by simpa using t10j32HighBitTailNode072MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode072Row]


/-- State label for generated row 73. -/
def t10j32HighBitTailNode073Label : String :=
  "v2=4|odd=2|h=1"

/-- Destination support of generated row 73. -/
def t10j32HighBitTailNode073Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 73. -/
def t10j32HighBitTailNode073LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 73. -/
def t10j32HighBitTailNode073LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 73. -/
def t10j32HighBitTailNode073Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 73. -/
theorem t10j32HighBitTailNode073Bound :
    t10j32HighBitTailNode073LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode073Vector * t10j32HighBitTailNode073LhsDen := by
  norm_num [t10j32HighBitTailNode073LhsNum, t10j32HighBitTailNode073LhsDen, t10j32HighBitTailNode073Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 73. -/
def t10j32HighBitTailNode073Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode073LhsNum
  lhsDen := t10j32HighBitTailNode073LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode073LhsDen]
  vector := t10j32HighBitTailNode073Vector
  vector_pos := by norm_num [t10j32HighBitTailNode073Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode073Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 73. -/
theorem t10j32HighBitTailNode073MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (73 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode073LhsNum : NNReal) / (t10j32HighBitTailNode073LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode073LhsNum, t10j32HighBitTailNode073LhsDen]

/-- Evaluated row certificate for generated row 73. -/
def t10j32HighBitTailNode073Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (73 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode073Row
  lhs_eq := by simpa using t10j32HighBitTailNode073MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode073Row]


/-- State label for generated row 74. -/
def t10j32HighBitTailNode074Label : String :=
  "v2=4|odd=2|h=2"

/-- Destination support of generated row 74. -/
def t10j32HighBitTailNode074Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 74. -/
def t10j32HighBitTailNode074LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 74. -/
def t10j32HighBitTailNode074LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 74. -/
def t10j32HighBitTailNode074Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 74. -/
theorem t10j32HighBitTailNode074Bound :
    t10j32HighBitTailNode074LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode074Vector * t10j32HighBitTailNode074LhsDen := by
  norm_num [t10j32HighBitTailNode074LhsNum, t10j32HighBitTailNode074LhsDen, t10j32HighBitTailNode074Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 74. -/
def t10j32HighBitTailNode074Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode074LhsNum
  lhsDen := t10j32HighBitTailNode074LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode074LhsDen]
  vector := t10j32HighBitTailNode074Vector
  vector_pos := by norm_num [t10j32HighBitTailNode074Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode074Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 74. -/
theorem t10j32HighBitTailNode074MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (74 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode074LhsNum : NNReal) / (t10j32HighBitTailNode074LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode074LhsNum, t10j32HighBitTailNode074LhsDen]

/-- Evaluated row certificate for generated row 74. -/
def t10j32HighBitTailNode074Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (74 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode074Row
  lhs_eq := by simpa using t10j32HighBitTailNode074MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode074Row]


/-- State label for generated row 75. -/
def t10j32HighBitTailNode075Label : String :=
  "v2=4|odd=2|h=3"

/-- Destination support of generated row 75. -/
def t10j32HighBitTailNode075Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 75. -/
def t10j32HighBitTailNode075LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 75. -/
def t10j32HighBitTailNode075LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 75. -/
def t10j32HighBitTailNode075Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 75. -/
theorem t10j32HighBitTailNode075Bound :
    t10j32HighBitTailNode075LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode075Vector * t10j32HighBitTailNode075LhsDen := by
  norm_num [t10j32HighBitTailNode075LhsNum, t10j32HighBitTailNode075LhsDen, t10j32HighBitTailNode075Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 75. -/
def t10j32HighBitTailNode075Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode075LhsNum
  lhsDen := t10j32HighBitTailNode075LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode075LhsDen]
  vector := t10j32HighBitTailNode075Vector
  vector_pos := by norm_num [t10j32HighBitTailNode075Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode075Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 75. -/
theorem t10j32HighBitTailNode075MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (75 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode075LhsNum : NNReal) / (t10j32HighBitTailNode075LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode075LhsNum, t10j32HighBitTailNode075LhsDen]

/-- Evaluated row certificate for generated row 75. -/
def t10j32HighBitTailNode075Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (75 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode075Row
  lhs_eq := by simpa using t10j32HighBitTailNode075MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode075Row]


/-- State label for generated row 76. -/
def t10j32HighBitTailNode076Label : String :=
  "v2=4|odd=3|h=0"

/-- Destination support of generated row 76. -/
def t10j32HighBitTailNode076Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 76. -/
def t10j32HighBitTailNode076LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 76. -/
def t10j32HighBitTailNode076LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 76. -/
def t10j32HighBitTailNode076Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 76. -/
theorem t10j32HighBitTailNode076Bound :
    t10j32HighBitTailNode076LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode076Vector * t10j32HighBitTailNode076LhsDen := by
  norm_num [t10j32HighBitTailNode076LhsNum, t10j32HighBitTailNode076LhsDen, t10j32HighBitTailNode076Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 76. -/
def t10j32HighBitTailNode076Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode076LhsNum
  lhsDen := t10j32HighBitTailNode076LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode076LhsDen]
  vector := t10j32HighBitTailNode076Vector
  vector_pos := by norm_num [t10j32HighBitTailNode076Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode076Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 76. -/
theorem t10j32HighBitTailNode076MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (76 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode076LhsNum : NNReal) / (t10j32HighBitTailNode076LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode076LhsNum, t10j32HighBitTailNode076LhsDen]

/-- Evaluated row certificate for generated row 76. -/
def t10j32HighBitTailNode076Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (76 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode076Row
  lhs_eq := by simpa using t10j32HighBitTailNode076MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode076Row]


/-- State label for generated row 77. -/
def t10j32HighBitTailNode077Label : String :=
  "v2=4|odd=3|h=1"

/-- Destination support of generated row 77. -/
def t10j32HighBitTailNode077Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 77. -/
def t10j32HighBitTailNode077LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 77. -/
def t10j32HighBitTailNode077LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 77. -/
def t10j32HighBitTailNode077Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 77. -/
theorem t10j32HighBitTailNode077Bound :
    t10j32HighBitTailNode077LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode077Vector * t10j32HighBitTailNode077LhsDen := by
  norm_num [t10j32HighBitTailNode077LhsNum, t10j32HighBitTailNode077LhsDen, t10j32HighBitTailNode077Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 77. -/
def t10j32HighBitTailNode077Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode077LhsNum
  lhsDen := t10j32HighBitTailNode077LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode077LhsDen]
  vector := t10j32HighBitTailNode077Vector
  vector_pos := by norm_num [t10j32HighBitTailNode077Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode077Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 77. -/
theorem t10j32HighBitTailNode077MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (77 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode077LhsNum : NNReal) / (t10j32HighBitTailNode077LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode077LhsNum, t10j32HighBitTailNode077LhsDen]

/-- Evaluated row certificate for generated row 77. -/
def t10j32HighBitTailNode077Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (77 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode077Row
  lhs_eq := by simpa using t10j32HighBitTailNode077MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode077Row]


/-- State label for generated row 78. -/
def t10j32HighBitTailNode078Label : String :=
  "v2=4|odd=3|h=2"

/-- Destination support of generated row 78. -/
def t10j32HighBitTailNode078Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 78. -/
def t10j32HighBitTailNode078LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 78. -/
def t10j32HighBitTailNode078LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 78. -/
def t10j32HighBitTailNode078Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 78. -/
theorem t10j32HighBitTailNode078Bound :
    t10j32HighBitTailNode078LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode078Vector * t10j32HighBitTailNode078LhsDen := by
  norm_num [t10j32HighBitTailNode078LhsNum, t10j32HighBitTailNode078LhsDen, t10j32HighBitTailNode078Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 78. -/
def t10j32HighBitTailNode078Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode078LhsNum
  lhsDen := t10j32HighBitTailNode078LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode078LhsDen]
  vector := t10j32HighBitTailNode078Vector
  vector_pos := by norm_num [t10j32HighBitTailNode078Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode078Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 78. -/
theorem t10j32HighBitTailNode078MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (78 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode078LhsNum : NNReal) / (t10j32HighBitTailNode078LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode078LhsNum, t10j32HighBitTailNode078LhsDen]

/-- Evaluated row certificate for generated row 78. -/
def t10j32HighBitTailNode078Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (78 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode078Row
  lhs_eq := by simpa using t10j32HighBitTailNode078MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode078Row]


/-- State label for generated row 79. -/
def t10j32HighBitTailNode079Label : String :=
  "v2=4|odd=3|h=3"

/-- Destination support of generated row 79. -/
def t10j32HighBitTailNode079Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 79. -/
def t10j32HighBitTailNode079LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 79. -/
def t10j32HighBitTailNode079LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 79. -/
def t10j32HighBitTailNode079Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 79. -/
theorem t10j32HighBitTailNode079Bound :
    t10j32HighBitTailNode079LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode079Vector * t10j32HighBitTailNode079LhsDen := by
  norm_num [t10j32HighBitTailNode079LhsNum, t10j32HighBitTailNode079LhsDen, t10j32HighBitTailNode079Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 79. -/
def t10j32HighBitTailNode079Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode079LhsNum
  lhsDen := t10j32HighBitTailNode079LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode079LhsDen]
  vector := t10j32HighBitTailNode079Vector
  vector_pos := by norm_num [t10j32HighBitTailNode079Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode079Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 79. -/
theorem t10j32HighBitTailNode079MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (79 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode079LhsNum : NNReal) / (t10j32HighBitTailNode079LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode079LhsNum, t10j32HighBitTailNode079LhsDen]

/-- Evaluated row certificate for generated row 79. -/
def t10j32HighBitTailNode079Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (79 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode079Row
  lhs_eq := by simpa using t10j32HighBitTailNode079MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode079Row]

end Generated
end CollatzShadowing
