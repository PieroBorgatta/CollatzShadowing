import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 176. -/
def t10j32HighBitTailNode176Label : String :=
  "v2=11|odd=0|h=0"

/-- Destination support of generated row 176. -/
def t10j32HighBitTailNode176Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 176. -/
def t10j32HighBitTailNode176LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 176. -/
def t10j32HighBitTailNode176LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 176. -/
def t10j32HighBitTailNode176Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 176. -/
theorem t10j32HighBitTailNode176Bound :
    t10j32HighBitTailNode176LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode176Vector * t10j32HighBitTailNode176LhsDen := by
  norm_num [t10j32HighBitTailNode176LhsNum, t10j32HighBitTailNode176LhsDen, t10j32HighBitTailNode176Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 176. -/
def t10j32HighBitTailNode176Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode176LhsNum
  lhsDen := t10j32HighBitTailNode176LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode176LhsDen]
  vector := t10j32HighBitTailNode176Vector
  vector_pos := by norm_num [t10j32HighBitTailNode176Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode176Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 176. -/
theorem t10j32HighBitTailNode176MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (176 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode176LhsNum : NNReal) / (t10j32HighBitTailNode176LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode176LhsNum, t10j32HighBitTailNode176LhsDen]

/-- Evaluated row certificate for generated row 176. -/
def t10j32HighBitTailNode176Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (176 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode176Row
  lhs_eq := by simpa using t10j32HighBitTailNode176MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode176Row]


/-- State label for generated row 177. -/
def t10j32HighBitTailNode177Label : String :=
  "v2=11|odd=0|h=1"

/-- Destination support of generated row 177. -/
def t10j32HighBitTailNode177Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 177. -/
def t10j32HighBitTailNode177LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 177. -/
def t10j32HighBitTailNode177LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 177. -/
def t10j32HighBitTailNode177Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 177. -/
theorem t10j32HighBitTailNode177Bound :
    t10j32HighBitTailNode177LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode177Vector * t10j32HighBitTailNode177LhsDen := by
  norm_num [t10j32HighBitTailNode177LhsNum, t10j32HighBitTailNode177LhsDen, t10j32HighBitTailNode177Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 177. -/
def t10j32HighBitTailNode177Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode177LhsNum
  lhsDen := t10j32HighBitTailNode177LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode177LhsDen]
  vector := t10j32HighBitTailNode177Vector
  vector_pos := by norm_num [t10j32HighBitTailNode177Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode177Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 177. -/
theorem t10j32HighBitTailNode177MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (177 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode177LhsNum : NNReal) / (t10j32HighBitTailNode177LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode177LhsNum, t10j32HighBitTailNode177LhsDen]

/-- Evaluated row certificate for generated row 177. -/
def t10j32HighBitTailNode177Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (177 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode177Row
  lhs_eq := by simpa using t10j32HighBitTailNode177MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode177Row]


/-- State label for generated row 178. -/
def t10j32HighBitTailNode178Label : String :=
  "v2=11|odd=0|h=2"

/-- Destination support of generated row 178. -/
def t10j32HighBitTailNode178Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 178. -/
def t10j32HighBitTailNode178LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 178. -/
def t10j32HighBitTailNode178LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 178. -/
def t10j32HighBitTailNode178Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 178. -/
theorem t10j32HighBitTailNode178Bound :
    t10j32HighBitTailNode178LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode178Vector * t10j32HighBitTailNode178LhsDen := by
  norm_num [t10j32HighBitTailNode178LhsNum, t10j32HighBitTailNode178LhsDen, t10j32HighBitTailNode178Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 178. -/
def t10j32HighBitTailNode178Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode178LhsNum
  lhsDen := t10j32HighBitTailNode178LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode178LhsDen]
  vector := t10j32HighBitTailNode178Vector
  vector_pos := by norm_num [t10j32HighBitTailNode178Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode178Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 178. -/
theorem t10j32HighBitTailNode178MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (178 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode178LhsNum : NNReal) / (t10j32HighBitTailNode178LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode178LhsNum, t10j32HighBitTailNode178LhsDen]

/-- Evaluated row certificate for generated row 178. -/
def t10j32HighBitTailNode178Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (178 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode178Row
  lhs_eq := by simpa using t10j32HighBitTailNode178MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode178Row]


/-- State label for generated row 179. -/
def t10j32HighBitTailNode179Label : String :=
  "v2=11|odd=0|h=3"

/-- Destination support of generated row 179. -/
def t10j32HighBitTailNode179Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 179. -/
def t10j32HighBitTailNode179LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 179. -/
def t10j32HighBitTailNode179LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 179. -/
def t10j32HighBitTailNode179Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 179. -/
theorem t10j32HighBitTailNode179Bound :
    t10j32HighBitTailNode179LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode179Vector * t10j32HighBitTailNode179LhsDen := by
  norm_num [t10j32HighBitTailNode179LhsNum, t10j32HighBitTailNode179LhsDen, t10j32HighBitTailNode179Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 179. -/
def t10j32HighBitTailNode179Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode179LhsNum
  lhsDen := t10j32HighBitTailNode179LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode179LhsDen]
  vector := t10j32HighBitTailNode179Vector
  vector_pos := by norm_num [t10j32HighBitTailNode179Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode179Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 179. -/
theorem t10j32HighBitTailNode179MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (179 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode179LhsNum : NNReal) / (t10j32HighBitTailNode179LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode179LhsNum, t10j32HighBitTailNode179LhsDen]

/-- Evaluated row certificate for generated row 179. -/
def t10j32HighBitTailNode179Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (179 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode179Row
  lhs_eq := by simpa using t10j32HighBitTailNode179MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode179Row]


/-- State label for generated row 180. -/
def t10j32HighBitTailNode180Label : String :=
  "v2=11|odd=1|h=0"

/-- Destination support of generated row 180. -/
def t10j32HighBitTailNode180Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 180. -/
def t10j32HighBitTailNode180LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 180. -/
def t10j32HighBitTailNode180LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 180. -/
def t10j32HighBitTailNode180Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 180. -/
theorem t10j32HighBitTailNode180Bound :
    t10j32HighBitTailNode180LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode180Vector * t10j32HighBitTailNode180LhsDen := by
  norm_num [t10j32HighBitTailNode180LhsNum, t10j32HighBitTailNode180LhsDen, t10j32HighBitTailNode180Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 180. -/
def t10j32HighBitTailNode180Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode180LhsNum
  lhsDen := t10j32HighBitTailNode180LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode180LhsDen]
  vector := t10j32HighBitTailNode180Vector
  vector_pos := by norm_num [t10j32HighBitTailNode180Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode180Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 180. -/
theorem t10j32HighBitTailNode180MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (180 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode180LhsNum : NNReal) / (t10j32HighBitTailNode180LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode180LhsNum, t10j32HighBitTailNode180LhsDen]

/-- Evaluated row certificate for generated row 180. -/
def t10j32HighBitTailNode180Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (180 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode180Row
  lhs_eq := by simpa using t10j32HighBitTailNode180MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode180Row]


/-- State label for generated row 181. -/
def t10j32HighBitTailNode181Label : String :=
  "v2=11|odd=1|h=1"

/-- Destination support of generated row 181. -/
def t10j32HighBitTailNode181Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 181. -/
def t10j32HighBitTailNode181LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 181. -/
def t10j32HighBitTailNode181LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 181. -/
def t10j32HighBitTailNode181Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 181. -/
theorem t10j32HighBitTailNode181Bound :
    t10j32HighBitTailNode181LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode181Vector * t10j32HighBitTailNode181LhsDen := by
  norm_num [t10j32HighBitTailNode181LhsNum, t10j32HighBitTailNode181LhsDen, t10j32HighBitTailNode181Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 181. -/
def t10j32HighBitTailNode181Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode181LhsNum
  lhsDen := t10j32HighBitTailNode181LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode181LhsDen]
  vector := t10j32HighBitTailNode181Vector
  vector_pos := by norm_num [t10j32HighBitTailNode181Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode181Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 181. -/
theorem t10j32HighBitTailNode181MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (181 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode181LhsNum : NNReal) / (t10j32HighBitTailNode181LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode181LhsNum, t10j32HighBitTailNode181LhsDen]

/-- Evaluated row certificate for generated row 181. -/
def t10j32HighBitTailNode181Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (181 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode181Row
  lhs_eq := by simpa using t10j32HighBitTailNode181MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode181Row]


/-- State label for generated row 182. -/
def t10j32HighBitTailNode182Label : String :=
  "v2=11|odd=1|h=2"

/-- Destination support of generated row 182. -/
def t10j32HighBitTailNode182Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 182. -/
def t10j32HighBitTailNode182LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 182. -/
def t10j32HighBitTailNode182LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 182. -/
def t10j32HighBitTailNode182Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 182. -/
theorem t10j32HighBitTailNode182Bound :
    t10j32HighBitTailNode182LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode182Vector * t10j32HighBitTailNode182LhsDen := by
  norm_num [t10j32HighBitTailNode182LhsNum, t10j32HighBitTailNode182LhsDen, t10j32HighBitTailNode182Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 182. -/
def t10j32HighBitTailNode182Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode182LhsNum
  lhsDen := t10j32HighBitTailNode182LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode182LhsDen]
  vector := t10j32HighBitTailNode182Vector
  vector_pos := by norm_num [t10j32HighBitTailNode182Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode182Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 182. -/
theorem t10j32HighBitTailNode182MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (182 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode182LhsNum : NNReal) / (t10j32HighBitTailNode182LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode182LhsNum, t10j32HighBitTailNode182LhsDen]

/-- Evaluated row certificate for generated row 182. -/
def t10j32HighBitTailNode182Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (182 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode182Row
  lhs_eq := by simpa using t10j32HighBitTailNode182MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode182Row]


/-- State label for generated row 183. -/
def t10j32HighBitTailNode183Label : String :=
  "v2=11|odd=1|h=3"

/-- Destination support of generated row 183. -/
def t10j32HighBitTailNode183Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 183. -/
def t10j32HighBitTailNode183LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 183. -/
def t10j32HighBitTailNode183LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 183. -/
def t10j32HighBitTailNode183Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 183. -/
theorem t10j32HighBitTailNode183Bound :
    t10j32HighBitTailNode183LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode183Vector * t10j32HighBitTailNode183LhsDen := by
  norm_num [t10j32HighBitTailNode183LhsNum, t10j32HighBitTailNode183LhsDen, t10j32HighBitTailNode183Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 183. -/
def t10j32HighBitTailNode183Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode183LhsNum
  lhsDen := t10j32HighBitTailNode183LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode183LhsDen]
  vector := t10j32HighBitTailNode183Vector
  vector_pos := by norm_num [t10j32HighBitTailNode183Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode183Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 183. -/
theorem t10j32HighBitTailNode183MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (183 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode183LhsNum : NNReal) / (t10j32HighBitTailNode183LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode183LhsNum, t10j32HighBitTailNode183LhsDen]

/-- Evaluated row certificate for generated row 183. -/
def t10j32HighBitTailNode183Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (183 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode183Row
  lhs_eq := by simpa using t10j32HighBitTailNode183MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode183Row]


/-- State label for generated row 184. -/
def t10j32HighBitTailNode184Label : String :=
  "v2=11|odd=2|h=0"

/-- Destination support of generated row 184. -/
def t10j32HighBitTailNode184Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 184. -/
def t10j32HighBitTailNode184LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 184. -/
def t10j32HighBitTailNode184LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 184. -/
def t10j32HighBitTailNode184Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 184. -/
theorem t10j32HighBitTailNode184Bound :
    t10j32HighBitTailNode184LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode184Vector * t10j32HighBitTailNode184LhsDen := by
  norm_num [t10j32HighBitTailNode184LhsNum, t10j32HighBitTailNode184LhsDen, t10j32HighBitTailNode184Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 184. -/
def t10j32HighBitTailNode184Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode184LhsNum
  lhsDen := t10j32HighBitTailNode184LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode184LhsDen]
  vector := t10j32HighBitTailNode184Vector
  vector_pos := by norm_num [t10j32HighBitTailNode184Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode184Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 184. -/
theorem t10j32HighBitTailNode184MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (184 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode184LhsNum : NNReal) / (t10j32HighBitTailNode184LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode184LhsNum, t10j32HighBitTailNode184LhsDen]

/-- Evaluated row certificate for generated row 184. -/
def t10j32HighBitTailNode184Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (184 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode184Row
  lhs_eq := by simpa using t10j32HighBitTailNode184MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode184Row]


/-- State label for generated row 185. -/
def t10j32HighBitTailNode185Label : String :=
  "v2=11|odd=2|h=1"

/-- Destination support of generated row 185. -/
def t10j32HighBitTailNode185Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 185. -/
def t10j32HighBitTailNode185LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 185. -/
def t10j32HighBitTailNode185LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 185. -/
def t10j32HighBitTailNode185Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 185. -/
theorem t10j32HighBitTailNode185Bound :
    t10j32HighBitTailNode185LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode185Vector * t10j32HighBitTailNode185LhsDen := by
  norm_num [t10j32HighBitTailNode185LhsNum, t10j32HighBitTailNode185LhsDen, t10j32HighBitTailNode185Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 185. -/
def t10j32HighBitTailNode185Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode185LhsNum
  lhsDen := t10j32HighBitTailNode185LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode185LhsDen]
  vector := t10j32HighBitTailNode185Vector
  vector_pos := by norm_num [t10j32HighBitTailNode185Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode185Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 185. -/
theorem t10j32HighBitTailNode185MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (185 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode185LhsNum : NNReal) / (t10j32HighBitTailNode185LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode185LhsNum, t10j32HighBitTailNode185LhsDen]

/-- Evaluated row certificate for generated row 185. -/
def t10j32HighBitTailNode185Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (185 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode185Row
  lhs_eq := by simpa using t10j32HighBitTailNode185MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode185Row]


/-- State label for generated row 186. -/
def t10j32HighBitTailNode186Label : String :=
  "v2=11|odd=2|h=2"

/-- Destination support of generated row 186. -/
def t10j32HighBitTailNode186Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 186. -/
def t10j32HighBitTailNode186LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 186. -/
def t10j32HighBitTailNode186LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 186. -/
def t10j32HighBitTailNode186Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 186. -/
theorem t10j32HighBitTailNode186Bound :
    t10j32HighBitTailNode186LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode186Vector * t10j32HighBitTailNode186LhsDen := by
  norm_num [t10j32HighBitTailNode186LhsNum, t10j32HighBitTailNode186LhsDen, t10j32HighBitTailNode186Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 186. -/
def t10j32HighBitTailNode186Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode186LhsNum
  lhsDen := t10j32HighBitTailNode186LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode186LhsDen]
  vector := t10j32HighBitTailNode186Vector
  vector_pos := by norm_num [t10j32HighBitTailNode186Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode186Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 186. -/
theorem t10j32HighBitTailNode186MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (186 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode186LhsNum : NNReal) / (t10j32HighBitTailNode186LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode186LhsNum, t10j32HighBitTailNode186LhsDen]

/-- Evaluated row certificate for generated row 186. -/
def t10j32HighBitTailNode186Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (186 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode186Row
  lhs_eq := by simpa using t10j32HighBitTailNode186MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode186Row]


/-- State label for generated row 187. -/
def t10j32HighBitTailNode187Label : String :=
  "v2=11|odd=2|h=3"

/-- Destination support of generated row 187. -/
def t10j32HighBitTailNode187Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 187. -/
def t10j32HighBitTailNode187LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 187. -/
def t10j32HighBitTailNode187LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 187. -/
def t10j32HighBitTailNode187Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 187. -/
theorem t10j32HighBitTailNode187Bound :
    t10j32HighBitTailNode187LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode187Vector * t10j32HighBitTailNode187LhsDen := by
  norm_num [t10j32HighBitTailNode187LhsNum, t10j32HighBitTailNode187LhsDen, t10j32HighBitTailNode187Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 187. -/
def t10j32HighBitTailNode187Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode187LhsNum
  lhsDen := t10j32HighBitTailNode187LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode187LhsDen]
  vector := t10j32HighBitTailNode187Vector
  vector_pos := by norm_num [t10j32HighBitTailNode187Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode187Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 187. -/
theorem t10j32HighBitTailNode187MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (187 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode187LhsNum : NNReal) / (t10j32HighBitTailNode187LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode187LhsNum, t10j32HighBitTailNode187LhsDen]

/-- Evaluated row certificate for generated row 187. -/
def t10j32HighBitTailNode187Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (187 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode187Row
  lhs_eq := by simpa using t10j32HighBitTailNode187MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode187Row]


/-- State label for generated row 188. -/
def t10j32HighBitTailNode188Label : String :=
  "v2=11|odd=3|h=0"

/-- Destination support of generated row 188. -/
def t10j32HighBitTailNode188Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 188. -/
def t10j32HighBitTailNode188LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 188. -/
def t10j32HighBitTailNode188LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 188. -/
def t10j32HighBitTailNode188Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 188. -/
theorem t10j32HighBitTailNode188Bound :
    t10j32HighBitTailNode188LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode188Vector * t10j32HighBitTailNode188LhsDen := by
  norm_num [t10j32HighBitTailNode188LhsNum, t10j32HighBitTailNode188LhsDen, t10j32HighBitTailNode188Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 188. -/
def t10j32HighBitTailNode188Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode188LhsNum
  lhsDen := t10j32HighBitTailNode188LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode188LhsDen]
  vector := t10j32HighBitTailNode188Vector
  vector_pos := by norm_num [t10j32HighBitTailNode188Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode188Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 188. -/
theorem t10j32HighBitTailNode188MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (188 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode188LhsNum : NNReal) / (t10j32HighBitTailNode188LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode188LhsNum, t10j32HighBitTailNode188LhsDen]

/-- Evaluated row certificate for generated row 188. -/
def t10j32HighBitTailNode188Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (188 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode188Row
  lhs_eq := by simpa using t10j32HighBitTailNode188MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode188Row]


/-- State label for generated row 189. -/
def t10j32HighBitTailNode189Label : String :=
  "v2=11|odd=3|h=1"

/-- Destination support of generated row 189. -/
def t10j32HighBitTailNode189Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 189. -/
def t10j32HighBitTailNode189LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 189. -/
def t10j32HighBitTailNode189LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 189. -/
def t10j32HighBitTailNode189Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 189. -/
theorem t10j32HighBitTailNode189Bound :
    t10j32HighBitTailNode189LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode189Vector * t10j32HighBitTailNode189LhsDen := by
  norm_num [t10j32HighBitTailNode189LhsNum, t10j32HighBitTailNode189LhsDen, t10j32HighBitTailNode189Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 189. -/
def t10j32HighBitTailNode189Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode189LhsNum
  lhsDen := t10j32HighBitTailNode189LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode189LhsDen]
  vector := t10j32HighBitTailNode189Vector
  vector_pos := by norm_num [t10j32HighBitTailNode189Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode189Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 189. -/
theorem t10j32HighBitTailNode189MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (189 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode189LhsNum : NNReal) / (t10j32HighBitTailNode189LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode189LhsNum, t10j32HighBitTailNode189LhsDen]

/-- Evaluated row certificate for generated row 189. -/
def t10j32HighBitTailNode189Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (189 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode189Row
  lhs_eq := by simpa using t10j32HighBitTailNode189MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode189Row]


/-- State label for generated row 190. -/
def t10j32HighBitTailNode190Label : String :=
  "v2=11|odd=3|h=2"

/-- Destination support of generated row 190. -/
def t10j32HighBitTailNode190Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 190. -/
def t10j32HighBitTailNode190LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 190. -/
def t10j32HighBitTailNode190LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 190. -/
def t10j32HighBitTailNode190Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 190. -/
theorem t10j32HighBitTailNode190Bound :
    t10j32HighBitTailNode190LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode190Vector * t10j32HighBitTailNode190LhsDen := by
  norm_num [t10j32HighBitTailNode190LhsNum, t10j32HighBitTailNode190LhsDen, t10j32HighBitTailNode190Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 190. -/
def t10j32HighBitTailNode190Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode190LhsNum
  lhsDen := t10j32HighBitTailNode190LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode190LhsDen]
  vector := t10j32HighBitTailNode190Vector
  vector_pos := by norm_num [t10j32HighBitTailNode190Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode190Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 190. -/
theorem t10j32HighBitTailNode190MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (190 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode190LhsNum : NNReal) / (t10j32HighBitTailNode190LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode190LhsNum, t10j32HighBitTailNode190LhsDen]

/-- Evaluated row certificate for generated row 190. -/
def t10j32HighBitTailNode190Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (190 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode190Row
  lhs_eq := by simpa using t10j32HighBitTailNode190MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode190Row]


/-- State label for generated row 191. -/
def t10j32HighBitTailNode191Label : String :=
  "v2=11|odd=3|h=3"

/-- Destination support of generated row 191. -/
def t10j32HighBitTailNode191Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 191. -/
def t10j32HighBitTailNode191LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 191. -/
def t10j32HighBitTailNode191LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 191. -/
def t10j32HighBitTailNode191Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 191. -/
theorem t10j32HighBitTailNode191Bound :
    t10j32HighBitTailNode191LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode191Vector * t10j32HighBitTailNode191LhsDen := by
  norm_num [t10j32HighBitTailNode191LhsNum, t10j32HighBitTailNode191LhsDen, t10j32HighBitTailNode191Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 191. -/
def t10j32HighBitTailNode191Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode191LhsNum
  lhsDen := t10j32HighBitTailNode191LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode191LhsDen]
  vector := t10j32HighBitTailNode191Vector
  vector_pos := by norm_num [t10j32HighBitTailNode191Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode191Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 191. -/
theorem t10j32HighBitTailNode191MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (191 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode191LhsNum : NNReal) / (t10j32HighBitTailNode191LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode191LhsNum, t10j32HighBitTailNode191LhsDen]

/-- Evaluated row certificate for generated row 191. -/
def t10j32HighBitTailNode191Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (191 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode191Row
  lhs_eq := by simpa using t10j32HighBitTailNode191MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode191Row]

end Generated
end CollatzShadowing
