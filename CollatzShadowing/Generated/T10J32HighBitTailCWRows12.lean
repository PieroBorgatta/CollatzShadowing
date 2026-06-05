import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 192. -/
def t10j32HighBitTailNode192Label : String :=
  "v2=12|odd=0|h=0"

/-- Destination support of generated row 192. -/
def t10j32HighBitTailNode192Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 192. -/
def t10j32HighBitTailNode192LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 192. -/
def t10j32HighBitTailNode192LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 192. -/
def t10j32HighBitTailNode192Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 192. -/
theorem t10j32HighBitTailNode192Bound :
    t10j32HighBitTailNode192LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode192Vector * t10j32HighBitTailNode192LhsDen := by
  norm_num [t10j32HighBitTailNode192LhsNum, t10j32HighBitTailNode192LhsDen, t10j32HighBitTailNode192Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 192. -/
def t10j32HighBitTailNode192Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode192LhsNum
  lhsDen := t10j32HighBitTailNode192LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode192LhsDen]
  vector := t10j32HighBitTailNode192Vector
  vector_pos := by norm_num [t10j32HighBitTailNode192Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode192Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 192. -/
theorem t10j32HighBitTailNode192MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (192 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode192LhsNum : NNReal) / (t10j32HighBitTailNode192LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode192LhsNum, t10j32HighBitTailNode192LhsDen]

/-- Evaluated row certificate for generated row 192. -/
def t10j32HighBitTailNode192Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (192 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode192Row
  lhs_eq := by simpa using t10j32HighBitTailNode192MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode192Row]


/-- State label for generated row 193. -/
def t10j32HighBitTailNode193Label : String :=
  "v2=12|odd=0|h=1"

/-- Destination support of generated row 193. -/
def t10j32HighBitTailNode193Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 193. -/
def t10j32HighBitTailNode193LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 193. -/
def t10j32HighBitTailNode193LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 193. -/
def t10j32HighBitTailNode193Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 193. -/
theorem t10j32HighBitTailNode193Bound :
    t10j32HighBitTailNode193LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode193Vector * t10j32HighBitTailNode193LhsDen := by
  norm_num [t10j32HighBitTailNode193LhsNum, t10j32HighBitTailNode193LhsDen, t10j32HighBitTailNode193Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 193. -/
def t10j32HighBitTailNode193Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode193LhsNum
  lhsDen := t10j32HighBitTailNode193LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode193LhsDen]
  vector := t10j32HighBitTailNode193Vector
  vector_pos := by norm_num [t10j32HighBitTailNode193Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode193Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 193. -/
theorem t10j32HighBitTailNode193MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (193 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode193LhsNum : NNReal) / (t10j32HighBitTailNode193LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode193LhsNum, t10j32HighBitTailNode193LhsDen]

/-- Evaluated row certificate for generated row 193. -/
def t10j32HighBitTailNode193Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (193 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode193Row
  lhs_eq := by simpa using t10j32HighBitTailNode193MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode193Row]


/-- State label for generated row 194. -/
def t10j32HighBitTailNode194Label : String :=
  "v2=12|odd=0|h=2"

/-- Destination support of generated row 194. -/
def t10j32HighBitTailNode194Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 194. -/
def t10j32HighBitTailNode194LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 194. -/
def t10j32HighBitTailNode194LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 194. -/
def t10j32HighBitTailNode194Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 194. -/
theorem t10j32HighBitTailNode194Bound :
    t10j32HighBitTailNode194LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode194Vector * t10j32HighBitTailNode194LhsDen := by
  norm_num [t10j32HighBitTailNode194LhsNum, t10j32HighBitTailNode194LhsDen, t10j32HighBitTailNode194Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 194. -/
def t10j32HighBitTailNode194Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode194LhsNum
  lhsDen := t10j32HighBitTailNode194LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode194LhsDen]
  vector := t10j32HighBitTailNode194Vector
  vector_pos := by norm_num [t10j32HighBitTailNode194Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode194Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 194. -/
theorem t10j32HighBitTailNode194MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (194 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode194LhsNum : NNReal) / (t10j32HighBitTailNode194LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode194LhsNum, t10j32HighBitTailNode194LhsDen]

/-- Evaluated row certificate for generated row 194. -/
def t10j32HighBitTailNode194Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (194 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode194Row
  lhs_eq := by simpa using t10j32HighBitTailNode194MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode194Row]


/-- State label for generated row 195. -/
def t10j32HighBitTailNode195Label : String :=
  "v2=12|odd=0|h=3"

/-- Destination support of generated row 195. -/
def t10j32HighBitTailNode195Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 195. -/
def t10j32HighBitTailNode195LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 195. -/
def t10j32HighBitTailNode195LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 195. -/
def t10j32HighBitTailNode195Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 195. -/
theorem t10j32HighBitTailNode195Bound :
    t10j32HighBitTailNode195LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode195Vector * t10j32HighBitTailNode195LhsDen := by
  norm_num [t10j32HighBitTailNode195LhsNum, t10j32HighBitTailNode195LhsDen, t10j32HighBitTailNode195Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 195. -/
def t10j32HighBitTailNode195Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode195LhsNum
  lhsDen := t10j32HighBitTailNode195LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode195LhsDen]
  vector := t10j32HighBitTailNode195Vector
  vector_pos := by norm_num [t10j32HighBitTailNode195Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode195Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 195. -/
theorem t10j32HighBitTailNode195MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (195 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode195LhsNum : NNReal) / (t10j32HighBitTailNode195LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode195LhsNum, t10j32HighBitTailNode195LhsDen]

/-- Evaluated row certificate for generated row 195. -/
def t10j32HighBitTailNode195Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (195 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode195Row
  lhs_eq := by simpa using t10j32HighBitTailNode195MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode195Row]


/-- State label for generated row 196. -/
def t10j32HighBitTailNode196Label : String :=
  "v2=12|odd=1|h=0"

/-- Destination support of generated row 196. -/
def t10j32HighBitTailNode196Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 196. -/
def t10j32HighBitTailNode196LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 196. -/
def t10j32HighBitTailNode196LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 196. -/
def t10j32HighBitTailNode196Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 196. -/
theorem t10j32HighBitTailNode196Bound :
    t10j32HighBitTailNode196LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode196Vector * t10j32HighBitTailNode196LhsDen := by
  norm_num [t10j32HighBitTailNode196LhsNum, t10j32HighBitTailNode196LhsDen, t10j32HighBitTailNode196Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 196. -/
def t10j32HighBitTailNode196Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode196LhsNum
  lhsDen := t10j32HighBitTailNode196LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode196LhsDen]
  vector := t10j32HighBitTailNode196Vector
  vector_pos := by norm_num [t10j32HighBitTailNode196Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode196Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 196. -/
theorem t10j32HighBitTailNode196MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (196 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode196LhsNum : NNReal) / (t10j32HighBitTailNode196LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode196LhsNum, t10j32HighBitTailNode196LhsDen]

/-- Evaluated row certificate for generated row 196. -/
def t10j32HighBitTailNode196Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (196 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode196Row
  lhs_eq := by simpa using t10j32HighBitTailNode196MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode196Row]


/-- State label for generated row 197. -/
def t10j32HighBitTailNode197Label : String :=
  "v2=12|odd=1|h=1"

/-- Destination support of generated row 197. -/
def t10j32HighBitTailNode197Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 197. -/
def t10j32HighBitTailNode197LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 197. -/
def t10j32HighBitTailNode197LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 197. -/
def t10j32HighBitTailNode197Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 197. -/
theorem t10j32HighBitTailNode197Bound :
    t10j32HighBitTailNode197LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode197Vector * t10j32HighBitTailNode197LhsDen := by
  norm_num [t10j32HighBitTailNode197LhsNum, t10j32HighBitTailNode197LhsDen, t10j32HighBitTailNode197Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 197. -/
def t10j32HighBitTailNode197Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode197LhsNum
  lhsDen := t10j32HighBitTailNode197LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode197LhsDen]
  vector := t10j32HighBitTailNode197Vector
  vector_pos := by norm_num [t10j32HighBitTailNode197Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode197Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 197. -/
theorem t10j32HighBitTailNode197MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (197 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode197LhsNum : NNReal) / (t10j32HighBitTailNode197LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode197LhsNum, t10j32HighBitTailNode197LhsDen]

/-- Evaluated row certificate for generated row 197. -/
def t10j32HighBitTailNode197Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (197 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode197Row
  lhs_eq := by simpa using t10j32HighBitTailNode197MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode197Row]


/-- State label for generated row 198. -/
def t10j32HighBitTailNode198Label : String :=
  "v2=12|odd=1|h=2"

/-- Destination support of generated row 198. -/
def t10j32HighBitTailNode198Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 198. -/
def t10j32HighBitTailNode198LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 198. -/
def t10j32HighBitTailNode198LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 198. -/
def t10j32HighBitTailNode198Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 198. -/
theorem t10j32HighBitTailNode198Bound :
    t10j32HighBitTailNode198LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode198Vector * t10j32HighBitTailNode198LhsDen := by
  norm_num [t10j32HighBitTailNode198LhsNum, t10j32HighBitTailNode198LhsDen, t10j32HighBitTailNode198Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 198. -/
def t10j32HighBitTailNode198Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode198LhsNum
  lhsDen := t10j32HighBitTailNode198LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode198LhsDen]
  vector := t10j32HighBitTailNode198Vector
  vector_pos := by norm_num [t10j32HighBitTailNode198Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode198Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 198. -/
theorem t10j32HighBitTailNode198MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (198 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode198LhsNum : NNReal) / (t10j32HighBitTailNode198LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode198LhsNum, t10j32HighBitTailNode198LhsDen]

/-- Evaluated row certificate for generated row 198. -/
def t10j32HighBitTailNode198Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (198 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode198Row
  lhs_eq := by simpa using t10j32HighBitTailNode198MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode198Row]


/-- State label for generated row 199. -/
def t10j32HighBitTailNode199Label : String :=
  "v2=12|odd=1|h=3"

/-- Destination support of generated row 199. -/
def t10j32HighBitTailNode199Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 199. -/
def t10j32HighBitTailNode199LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 199. -/
def t10j32HighBitTailNode199LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 199. -/
def t10j32HighBitTailNode199Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 199. -/
theorem t10j32HighBitTailNode199Bound :
    t10j32HighBitTailNode199LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode199Vector * t10j32HighBitTailNode199LhsDen := by
  norm_num [t10j32HighBitTailNode199LhsNum, t10j32HighBitTailNode199LhsDen, t10j32HighBitTailNode199Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 199. -/
def t10j32HighBitTailNode199Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode199LhsNum
  lhsDen := t10j32HighBitTailNode199LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode199LhsDen]
  vector := t10j32HighBitTailNode199Vector
  vector_pos := by norm_num [t10j32HighBitTailNode199Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode199Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 199. -/
theorem t10j32HighBitTailNode199MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (199 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode199LhsNum : NNReal) / (t10j32HighBitTailNode199LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode199LhsNum, t10j32HighBitTailNode199LhsDen]

/-- Evaluated row certificate for generated row 199. -/
def t10j32HighBitTailNode199Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (199 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode199Row
  lhs_eq := by simpa using t10j32HighBitTailNode199MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode199Row]


/-- State label for generated row 200. -/
def t10j32HighBitTailNode200Label : String :=
  "v2=12|odd=2|h=0"

/-- Destination support of generated row 200. -/
def t10j32HighBitTailNode200Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 200. -/
def t10j32HighBitTailNode200LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 200. -/
def t10j32HighBitTailNode200LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 200. -/
def t10j32HighBitTailNode200Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 200. -/
theorem t10j32HighBitTailNode200Bound :
    t10j32HighBitTailNode200LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode200Vector * t10j32HighBitTailNode200LhsDen := by
  norm_num [t10j32HighBitTailNode200LhsNum, t10j32HighBitTailNode200LhsDen, t10j32HighBitTailNode200Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 200. -/
def t10j32HighBitTailNode200Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode200LhsNum
  lhsDen := t10j32HighBitTailNode200LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode200LhsDen]
  vector := t10j32HighBitTailNode200Vector
  vector_pos := by norm_num [t10j32HighBitTailNode200Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode200Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 200. -/
theorem t10j32HighBitTailNode200MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (200 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode200LhsNum : NNReal) / (t10j32HighBitTailNode200LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode200LhsNum, t10j32HighBitTailNode200LhsDen]

/-- Evaluated row certificate for generated row 200. -/
def t10j32HighBitTailNode200Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (200 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode200Row
  lhs_eq := by simpa using t10j32HighBitTailNode200MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode200Row]


/-- State label for generated row 201. -/
def t10j32HighBitTailNode201Label : String :=
  "v2=12|odd=2|h=1"

/-- Destination support of generated row 201. -/
def t10j32HighBitTailNode201Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 201. -/
def t10j32HighBitTailNode201LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 201. -/
def t10j32HighBitTailNode201LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 201. -/
def t10j32HighBitTailNode201Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 201. -/
theorem t10j32HighBitTailNode201Bound :
    t10j32HighBitTailNode201LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode201Vector * t10j32HighBitTailNode201LhsDen := by
  norm_num [t10j32HighBitTailNode201LhsNum, t10j32HighBitTailNode201LhsDen, t10j32HighBitTailNode201Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 201. -/
def t10j32HighBitTailNode201Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode201LhsNum
  lhsDen := t10j32HighBitTailNode201LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode201LhsDen]
  vector := t10j32HighBitTailNode201Vector
  vector_pos := by norm_num [t10j32HighBitTailNode201Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode201Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 201. -/
theorem t10j32HighBitTailNode201MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (201 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode201LhsNum : NNReal) / (t10j32HighBitTailNode201LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode201LhsNum, t10j32HighBitTailNode201LhsDen]

/-- Evaluated row certificate for generated row 201. -/
def t10j32HighBitTailNode201Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (201 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode201Row
  lhs_eq := by simpa using t10j32HighBitTailNode201MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode201Row]


/-- State label for generated row 202. -/
def t10j32HighBitTailNode202Label : String :=
  "v2=12|odd=2|h=2"

/-- Destination support of generated row 202. -/
def t10j32HighBitTailNode202Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 202. -/
def t10j32HighBitTailNode202LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 202. -/
def t10j32HighBitTailNode202LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 202. -/
def t10j32HighBitTailNode202Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 202. -/
theorem t10j32HighBitTailNode202Bound :
    t10j32HighBitTailNode202LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode202Vector * t10j32HighBitTailNode202LhsDen := by
  norm_num [t10j32HighBitTailNode202LhsNum, t10j32HighBitTailNode202LhsDen, t10j32HighBitTailNode202Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 202. -/
def t10j32HighBitTailNode202Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode202LhsNum
  lhsDen := t10j32HighBitTailNode202LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode202LhsDen]
  vector := t10j32HighBitTailNode202Vector
  vector_pos := by norm_num [t10j32HighBitTailNode202Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode202Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 202. -/
theorem t10j32HighBitTailNode202MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (202 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode202LhsNum : NNReal) / (t10j32HighBitTailNode202LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode202LhsNum, t10j32HighBitTailNode202LhsDen]

/-- Evaluated row certificate for generated row 202. -/
def t10j32HighBitTailNode202Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (202 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode202Row
  lhs_eq := by simpa using t10j32HighBitTailNode202MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode202Row]


/-- State label for generated row 203. -/
def t10j32HighBitTailNode203Label : String :=
  "v2=12|odd=2|h=3"

/-- Destination support of generated row 203. -/
def t10j32HighBitTailNode203Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 203. -/
def t10j32HighBitTailNode203LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 203. -/
def t10j32HighBitTailNode203LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 203. -/
def t10j32HighBitTailNode203Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 203. -/
theorem t10j32HighBitTailNode203Bound :
    t10j32HighBitTailNode203LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode203Vector * t10j32HighBitTailNode203LhsDen := by
  norm_num [t10j32HighBitTailNode203LhsNum, t10j32HighBitTailNode203LhsDen, t10j32HighBitTailNode203Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 203. -/
def t10j32HighBitTailNode203Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode203LhsNum
  lhsDen := t10j32HighBitTailNode203LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode203LhsDen]
  vector := t10j32HighBitTailNode203Vector
  vector_pos := by norm_num [t10j32HighBitTailNode203Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode203Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 203. -/
theorem t10j32HighBitTailNode203MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (203 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode203LhsNum : NNReal) / (t10j32HighBitTailNode203LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode203LhsNum, t10j32HighBitTailNode203LhsDen]

/-- Evaluated row certificate for generated row 203. -/
def t10j32HighBitTailNode203Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (203 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode203Row
  lhs_eq := by simpa using t10j32HighBitTailNode203MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode203Row]


/-- State label for generated row 204. -/
def t10j32HighBitTailNode204Label : String :=
  "v2=12|odd=3|h=0"

/-- Destination support of generated row 204. -/
def t10j32HighBitTailNode204Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 204. -/
def t10j32HighBitTailNode204LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 204. -/
def t10j32HighBitTailNode204LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 204. -/
def t10j32HighBitTailNode204Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 204. -/
theorem t10j32HighBitTailNode204Bound :
    t10j32HighBitTailNode204LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode204Vector * t10j32HighBitTailNode204LhsDen := by
  norm_num [t10j32HighBitTailNode204LhsNum, t10j32HighBitTailNode204LhsDen, t10j32HighBitTailNode204Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 204. -/
def t10j32HighBitTailNode204Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode204LhsNum
  lhsDen := t10j32HighBitTailNode204LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode204LhsDen]
  vector := t10j32HighBitTailNode204Vector
  vector_pos := by norm_num [t10j32HighBitTailNode204Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode204Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 204. -/
theorem t10j32HighBitTailNode204MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (204 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode204LhsNum : NNReal) / (t10j32HighBitTailNode204LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode204LhsNum, t10j32HighBitTailNode204LhsDen]

/-- Evaluated row certificate for generated row 204. -/
def t10j32HighBitTailNode204Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (204 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode204Row
  lhs_eq := by simpa using t10j32HighBitTailNode204MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode204Row]


/-- State label for generated row 205. -/
def t10j32HighBitTailNode205Label : String :=
  "v2=12|odd=3|h=1"

/-- Destination support of generated row 205. -/
def t10j32HighBitTailNode205Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 205. -/
def t10j32HighBitTailNode205LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 205. -/
def t10j32HighBitTailNode205LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 205. -/
def t10j32HighBitTailNode205Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 205. -/
theorem t10j32HighBitTailNode205Bound :
    t10j32HighBitTailNode205LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode205Vector * t10j32HighBitTailNode205LhsDen := by
  norm_num [t10j32HighBitTailNode205LhsNum, t10j32HighBitTailNode205LhsDen, t10j32HighBitTailNode205Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 205. -/
def t10j32HighBitTailNode205Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode205LhsNum
  lhsDen := t10j32HighBitTailNode205LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode205LhsDen]
  vector := t10j32HighBitTailNode205Vector
  vector_pos := by norm_num [t10j32HighBitTailNode205Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode205Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 205. -/
theorem t10j32HighBitTailNode205MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (205 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode205LhsNum : NNReal) / (t10j32HighBitTailNode205LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode205LhsNum, t10j32HighBitTailNode205LhsDen]

/-- Evaluated row certificate for generated row 205. -/
def t10j32HighBitTailNode205Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (205 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode205Row
  lhs_eq := by simpa using t10j32HighBitTailNode205MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode205Row]


/-- State label for generated row 206. -/
def t10j32HighBitTailNode206Label : String :=
  "v2=12|odd=3|h=2"

/-- Destination support of generated row 206. -/
def t10j32HighBitTailNode206Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 206. -/
def t10j32HighBitTailNode206LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 206. -/
def t10j32HighBitTailNode206LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 206. -/
def t10j32HighBitTailNode206Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 206. -/
theorem t10j32HighBitTailNode206Bound :
    t10j32HighBitTailNode206LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode206Vector * t10j32HighBitTailNode206LhsDen := by
  norm_num [t10j32HighBitTailNode206LhsNum, t10j32HighBitTailNode206LhsDen, t10j32HighBitTailNode206Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 206. -/
def t10j32HighBitTailNode206Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode206LhsNum
  lhsDen := t10j32HighBitTailNode206LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode206LhsDen]
  vector := t10j32HighBitTailNode206Vector
  vector_pos := by norm_num [t10j32HighBitTailNode206Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode206Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 206. -/
theorem t10j32HighBitTailNode206MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (206 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode206LhsNum : NNReal) / (t10j32HighBitTailNode206LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode206LhsNum, t10j32HighBitTailNode206LhsDen]

/-- Evaluated row certificate for generated row 206. -/
def t10j32HighBitTailNode206Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (206 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode206Row
  lhs_eq := by simpa using t10j32HighBitTailNode206MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode206Row]


/-- State label for generated row 207. -/
def t10j32HighBitTailNode207Label : String :=
  "v2=12|odd=3|h=3"

/-- Destination support of generated row 207. -/
def t10j32HighBitTailNode207Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 207. -/
def t10j32HighBitTailNode207LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 207. -/
def t10j32HighBitTailNode207LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 207. -/
def t10j32HighBitTailNode207Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 207. -/
theorem t10j32HighBitTailNode207Bound :
    t10j32HighBitTailNode207LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode207Vector * t10j32HighBitTailNode207LhsDen := by
  norm_num [t10j32HighBitTailNode207LhsNum, t10j32HighBitTailNode207LhsDen, t10j32HighBitTailNode207Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 207. -/
def t10j32HighBitTailNode207Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode207LhsNum
  lhsDen := t10j32HighBitTailNode207LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode207LhsDen]
  vector := t10j32HighBitTailNode207Vector
  vector_pos := by norm_num [t10j32HighBitTailNode207Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode207Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 207. -/
theorem t10j32HighBitTailNode207MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (207 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode207LhsNum : NNReal) / (t10j32HighBitTailNode207LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode207LhsNum, t10j32HighBitTailNode207LhsDen]

/-- Evaluated row certificate for generated row 207. -/
def t10j32HighBitTailNode207Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (207 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode207Row
  lhs_eq := by simpa using t10j32HighBitTailNode207MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode207Row]

end Generated
end CollatzShadowing
