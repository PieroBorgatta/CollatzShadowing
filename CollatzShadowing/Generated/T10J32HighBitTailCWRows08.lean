import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 128. -/
def t10j32HighBitTailNode128Label : String :=
  "v2=8|odd=0|h=0"

/-- Destination support of generated row 128. -/
def t10j32HighBitTailNode128Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 128. -/
def t10j32HighBitTailNode128LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 128. -/
def t10j32HighBitTailNode128LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 128. -/
def t10j32HighBitTailNode128Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 128. -/
theorem t10j32HighBitTailNode128Bound :
    t10j32HighBitTailNode128LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode128Vector * t10j32HighBitTailNode128LhsDen := by
  norm_num [t10j32HighBitTailNode128LhsNum, t10j32HighBitTailNode128LhsDen, t10j32HighBitTailNode128Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 128. -/
def t10j32HighBitTailNode128Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode128LhsNum
  lhsDen := t10j32HighBitTailNode128LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode128LhsDen]
  vector := t10j32HighBitTailNode128Vector
  vector_pos := by norm_num [t10j32HighBitTailNode128Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode128Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 128. -/
theorem t10j32HighBitTailNode128MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (128 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode128LhsNum : NNReal) / (t10j32HighBitTailNode128LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode128LhsNum, t10j32HighBitTailNode128LhsDen]

/-- Evaluated row certificate for generated row 128. -/
def t10j32HighBitTailNode128Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (128 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode128Row
  lhs_eq := by simpa using t10j32HighBitTailNode128MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode128Row]


/-- State label for generated row 129. -/
def t10j32HighBitTailNode129Label : String :=
  "v2=8|odd=0|h=1"

/-- Destination support of generated row 129. -/
def t10j32HighBitTailNode129Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 129. -/
def t10j32HighBitTailNode129LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 129. -/
def t10j32HighBitTailNode129LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 129. -/
def t10j32HighBitTailNode129Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 129. -/
theorem t10j32HighBitTailNode129Bound :
    t10j32HighBitTailNode129LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode129Vector * t10j32HighBitTailNode129LhsDen := by
  norm_num [t10j32HighBitTailNode129LhsNum, t10j32HighBitTailNode129LhsDen, t10j32HighBitTailNode129Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 129. -/
def t10j32HighBitTailNode129Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode129LhsNum
  lhsDen := t10j32HighBitTailNode129LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode129LhsDen]
  vector := t10j32HighBitTailNode129Vector
  vector_pos := by norm_num [t10j32HighBitTailNode129Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode129Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 129. -/
theorem t10j32HighBitTailNode129MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (129 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode129LhsNum : NNReal) / (t10j32HighBitTailNode129LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode129LhsNum, t10j32HighBitTailNode129LhsDen]

/-- Evaluated row certificate for generated row 129. -/
def t10j32HighBitTailNode129Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (129 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode129Row
  lhs_eq := by simpa using t10j32HighBitTailNode129MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode129Row]


/-- State label for generated row 130. -/
def t10j32HighBitTailNode130Label : String :=
  "v2=8|odd=0|h=2"

/-- Destination support of generated row 130. -/
def t10j32HighBitTailNode130Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 130. -/
def t10j32HighBitTailNode130LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 130. -/
def t10j32HighBitTailNode130LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 130. -/
def t10j32HighBitTailNode130Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 130. -/
theorem t10j32HighBitTailNode130Bound :
    t10j32HighBitTailNode130LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode130Vector * t10j32HighBitTailNode130LhsDen := by
  norm_num [t10j32HighBitTailNode130LhsNum, t10j32HighBitTailNode130LhsDen, t10j32HighBitTailNode130Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 130. -/
def t10j32HighBitTailNode130Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode130LhsNum
  lhsDen := t10j32HighBitTailNode130LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode130LhsDen]
  vector := t10j32HighBitTailNode130Vector
  vector_pos := by norm_num [t10j32HighBitTailNode130Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode130Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 130. -/
theorem t10j32HighBitTailNode130MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (130 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode130LhsNum : NNReal) / (t10j32HighBitTailNode130LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode130LhsNum, t10j32HighBitTailNode130LhsDen]

/-- Evaluated row certificate for generated row 130. -/
def t10j32HighBitTailNode130Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (130 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode130Row
  lhs_eq := by simpa using t10j32HighBitTailNode130MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode130Row]


/-- State label for generated row 131. -/
def t10j32HighBitTailNode131Label : String :=
  "v2=8|odd=0|h=3"

/-- Destination support of generated row 131. -/
def t10j32HighBitTailNode131Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 131. -/
def t10j32HighBitTailNode131LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 131. -/
def t10j32HighBitTailNode131LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 131. -/
def t10j32HighBitTailNode131Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 131. -/
theorem t10j32HighBitTailNode131Bound :
    t10j32HighBitTailNode131LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode131Vector * t10j32HighBitTailNode131LhsDen := by
  norm_num [t10j32HighBitTailNode131LhsNum, t10j32HighBitTailNode131LhsDen, t10j32HighBitTailNode131Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 131. -/
def t10j32HighBitTailNode131Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode131LhsNum
  lhsDen := t10j32HighBitTailNode131LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode131LhsDen]
  vector := t10j32HighBitTailNode131Vector
  vector_pos := by norm_num [t10j32HighBitTailNode131Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode131Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 131. -/
theorem t10j32HighBitTailNode131MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (131 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode131LhsNum : NNReal) / (t10j32HighBitTailNode131LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode131LhsNum, t10j32HighBitTailNode131LhsDen]

/-- Evaluated row certificate for generated row 131. -/
def t10j32HighBitTailNode131Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (131 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode131Row
  lhs_eq := by simpa using t10j32HighBitTailNode131MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode131Row]


/-- State label for generated row 132. -/
def t10j32HighBitTailNode132Label : String :=
  "v2=8|odd=1|h=0"

/-- Destination support of generated row 132. -/
def t10j32HighBitTailNode132Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 132. -/
def t10j32HighBitTailNode132LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 132. -/
def t10j32HighBitTailNode132LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 132. -/
def t10j32HighBitTailNode132Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 132. -/
theorem t10j32HighBitTailNode132Bound :
    t10j32HighBitTailNode132LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode132Vector * t10j32HighBitTailNode132LhsDen := by
  norm_num [t10j32HighBitTailNode132LhsNum, t10j32HighBitTailNode132LhsDen, t10j32HighBitTailNode132Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 132. -/
def t10j32HighBitTailNode132Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode132LhsNum
  lhsDen := t10j32HighBitTailNode132LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode132LhsDen]
  vector := t10j32HighBitTailNode132Vector
  vector_pos := by norm_num [t10j32HighBitTailNode132Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode132Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 132. -/
theorem t10j32HighBitTailNode132MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (132 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode132LhsNum : NNReal) / (t10j32HighBitTailNode132LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode132LhsNum, t10j32HighBitTailNode132LhsDen]

/-- Evaluated row certificate for generated row 132. -/
def t10j32HighBitTailNode132Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (132 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode132Row
  lhs_eq := by simpa using t10j32HighBitTailNode132MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode132Row]


/-- State label for generated row 133. -/
def t10j32HighBitTailNode133Label : String :=
  "v2=8|odd=1|h=1"

/-- Destination support of generated row 133. -/
def t10j32HighBitTailNode133Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 133. -/
def t10j32HighBitTailNode133LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 133. -/
def t10j32HighBitTailNode133LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 133. -/
def t10j32HighBitTailNode133Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 133. -/
theorem t10j32HighBitTailNode133Bound :
    t10j32HighBitTailNode133LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode133Vector * t10j32HighBitTailNode133LhsDen := by
  norm_num [t10j32HighBitTailNode133LhsNum, t10j32HighBitTailNode133LhsDen, t10j32HighBitTailNode133Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 133. -/
def t10j32HighBitTailNode133Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode133LhsNum
  lhsDen := t10j32HighBitTailNode133LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode133LhsDen]
  vector := t10j32HighBitTailNode133Vector
  vector_pos := by norm_num [t10j32HighBitTailNode133Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode133Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 133. -/
theorem t10j32HighBitTailNode133MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (133 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode133LhsNum : NNReal) / (t10j32HighBitTailNode133LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode133LhsNum, t10j32HighBitTailNode133LhsDen]

/-- Evaluated row certificate for generated row 133. -/
def t10j32HighBitTailNode133Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (133 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode133Row
  lhs_eq := by simpa using t10j32HighBitTailNode133MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode133Row]


/-- State label for generated row 134. -/
def t10j32HighBitTailNode134Label : String :=
  "v2=8|odd=1|h=2"

/-- Destination support of generated row 134. -/
def t10j32HighBitTailNode134Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 134. -/
def t10j32HighBitTailNode134LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 134. -/
def t10j32HighBitTailNode134LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 134. -/
def t10j32HighBitTailNode134Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 134. -/
theorem t10j32HighBitTailNode134Bound :
    t10j32HighBitTailNode134LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode134Vector * t10j32HighBitTailNode134LhsDen := by
  norm_num [t10j32HighBitTailNode134LhsNum, t10j32HighBitTailNode134LhsDen, t10j32HighBitTailNode134Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 134. -/
def t10j32HighBitTailNode134Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode134LhsNum
  lhsDen := t10j32HighBitTailNode134LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode134LhsDen]
  vector := t10j32HighBitTailNode134Vector
  vector_pos := by norm_num [t10j32HighBitTailNode134Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode134Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 134. -/
theorem t10j32HighBitTailNode134MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (134 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode134LhsNum : NNReal) / (t10j32HighBitTailNode134LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode134LhsNum, t10j32HighBitTailNode134LhsDen]

/-- Evaluated row certificate for generated row 134. -/
def t10j32HighBitTailNode134Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (134 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode134Row
  lhs_eq := by simpa using t10j32HighBitTailNode134MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode134Row]


/-- State label for generated row 135. -/
def t10j32HighBitTailNode135Label : String :=
  "v2=8|odd=1|h=3"

/-- Destination support of generated row 135. -/
def t10j32HighBitTailNode135Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 135. -/
def t10j32HighBitTailNode135LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 135. -/
def t10j32HighBitTailNode135LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 135. -/
def t10j32HighBitTailNode135Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 135. -/
theorem t10j32HighBitTailNode135Bound :
    t10j32HighBitTailNode135LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode135Vector * t10j32HighBitTailNode135LhsDen := by
  norm_num [t10j32HighBitTailNode135LhsNum, t10j32HighBitTailNode135LhsDen, t10j32HighBitTailNode135Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 135. -/
def t10j32HighBitTailNode135Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode135LhsNum
  lhsDen := t10j32HighBitTailNode135LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode135LhsDen]
  vector := t10j32HighBitTailNode135Vector
  vector_pos := by norm_num [t10j32HighBitTailNode135Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode135Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 135. -/
theorem t10j32HighBitTailNode135MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (135 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode135LhsNum : NNReal) / (t10j32HighBitTailNode135LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode135LhsNum, t10j32HighBitTailNode135LhsDen]

/-- Evaluated row certificate for generated row 135. -/
def t10j32HighBitTailNode135Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (135 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode135Row
  lhs_eq := by simpa using t10j32HighBitTailNode135MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode135Row]


/-- State label for generated row 136. -/
def t10j32HighBitTailNode136Label : String :=
  "v2=8|odd=2|h=0"

/-- Destination support of generated row 136. -/
def t10j32HighBitTailNode136Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 136. -/
def t10j32HighBitTailNode136LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 136. -/
def t10j32HighBitTailNode136LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 136. -/
def t10j32HighBitTailNode136Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 136. -/
theorem t10j32HighBitTailNode136Bound :
    t10j32HighBitTailNode136LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode136Vector * t10j32HighBitTailNode136LhsDen := by
  norm_num [t10j32HighBitTailNode136LhsNum, t10j32HighBitTailNode136LhsDen, t10j32HighBitTailNode136Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 136. -/
def t10j32HighBitTailNode136Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode136LhsNum
  lhsDen := t10j32HighBitTailNode136LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode136LhsDen]
  vector := t10j32HighBitTailNode136Vector
  vector_pos := by norm_num [t10j32HighBitTailNode136Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode136Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 136. -/
theorem t10j32HighBitTailNode136MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (136 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode136LhsNum : NNReal) / (t10j32HighBitTailNode136LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode136LhsNum, t10j32HighBitTailNode136LhsDen]

/-- Evaluated row certificate for generated row 136. -/
def t10j32HighBitTailNode136Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (136 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode136Row
  lhs_eq := by simpa using t10j32HighBitTailNode136MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode136Row]


/-- State label for generated row 137. -/
def t10j32HighBitTailNode137Label : String :=
  "v2=8|odd=2|h=1"

/-- Destination support of generated row 137. -/
def t10j32HighBitTailNode137Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 137. -/
def t10j32HighBitTailNode137LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 137. -/
def t10j32HighBitTailNode137LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 137. -/
def t10j32HighBitTailNode137Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 137. -/
theorem t10j32HighBitTailNode137Bound :
    t10j32HighBitTailNode137LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode137Vector * t10j32HighBitTailNode137LhsDen := by
  norm_num [t10j32HighBitTailNode137LhsNum, t10j32HighBitTailNode137LhsDen, t10j32HighBitTailNode137Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 137. -/
def t10j32HighBitTailNode137Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode137LhsNum
  lhsDen := t10j32HighBitTailNode137LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode137LhsDen]
  vector := t10j32HighBitTailNode137Vector
  vector_pos := by norm_num [t10j32HighBitTailNode137Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode137Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 137. -/
theorem t10j32HighBitTailNode137MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (137 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode137LhsNum : NNReal) / (t10j32HighBitTailNode137LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode137LhsNum, t10j32HighBitTailNode137LhsDen]

/-- Evaluated row certificate for generated row 137. -/
def t10j32HighBitTailNode137Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (137 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode137Row
  lhs_eq := by simpa using t10j32HighBitTailNode137MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode137Row]


/-- State label for generated row 138. -/
def t10j32HighBitTailNode138Label : String :=
  "v2=8|odd=2|h=2"

/-- Destination support of generated row 138. -/
def t10j32HighBitTailNode138Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 138. -/
def t10j32HighBitTailNode138LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 138. -/
def t10j32HighBitTailNode138LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 138. -/
def t10j32HighBitTailNode138Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 138. -/
theorem t10j32HighBitTailNode138Bound :
    t10j32HighBitTailNode138LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode138Vector * t10j32HighBitTailNode138LhsDen := by
  norm_num [t10j32HighBitTailNode138LhsNum, t10j32HighBitTailNode138LhsDen, t10j32HighBitTailNode138Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 138. -/
def t10j32HighBitTailNode138Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode138LhsNum
  lhsDen := t10j32HighBitTailNode138LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode138LhsDen]
  vector := t10j32HighBitTailNode138Vector
  vector_pos := by norm_num [t10j32HighBitTailNode138Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode138Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 138. -/
theorem t10j32HighBitTailNode138MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (138 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode138LhsNum : NNReal) / (t10j32HighBitTailNode138LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode138LhsNum, t10j32HighBitTailNode138LhsDen]

/-- Evaluated row certificate for generated row 138. -/
def t10j32HighBitTailNode138Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (138 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode138Row
  lhs_eq := by simpa using t10j32HighBitTailNode138MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode138Row]


/-- State label for generated row 139. -/
def t10j32HighBitTailNode139Label : String :=
  "v2=8|odd=2|h=3"

/-- Destination support of generated row 139. -/
def t10j32HighBitTailNode139Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 139. -/
def t10j32HighBitTailNode139LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 139. -/
def t10j32HighBitTailNode139LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 139. -/
def t10j32HighBitTailNode139Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 139. -/
theorem t10j32HighBitTailNode139Bound :
    t10j32HighBitTailNode139LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode139Vector * t10j32HighBitTailNode139LhsDen := by
  norm_num [t10j32HighBitTailNode139LhsNum, t10j32HighBitTailNode139LhsDen, t10j32HighBitTailNode139Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 139. -/
def t10j32HighBitTailNode139Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode139LhsNum
  lhsDen := t10j32HighBitTailNode139LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode139LhsDen]
  vector := t10j32HighBitTailNode139Vector
  vector_pos := by norm_num [t10j32HighBitTailNode139Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode139Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 139. -/
theorem t10j32HighBitTailNode139MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (139 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode139LhsNum : NNReal) / (t10j32HighBitTailNode139LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode139LhsNum, t10j32HighBitTailNode139LhsDen]

/-- Evaluated row certificate for generated row 139. -/
def t10j32HighBitTailNode139Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (139 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode139Row
  lhs_eq := by simpa using t10j32HighBitTailNode139MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode139Row]


/-- State label for generated row 140. -/
def t10j32HighBitTailNode140Label : String :=
  "v2=8|odd=3|h=0"

/-- Destination support of generated row 140. -/
def t10j32HighBitTailNode140Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 140. -/
def t10j32HighBitTailNode140LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 140. -/
def t10j32HighBitTailNode140LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 140. -/
def t10j32HighBitTailNode140Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 140. -/
theorem t10j32HighBitTailNode140Bound :
    t10j32HighBitTailNode140LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode140Vector * t10j32HighBitTailNode140LhsDen := by
  norm_num [t10j32HighBitTailNode140LhsNum, t10j32HighBitTailNode140LhsDen, t10j32HighBitTailNode140Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 140. -/
def t10j32HighBitTailNode140Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode140LhsNum
  lhsDen := t10j32HighBitTailNode140LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode140LhsDen]
  vector := t10j32HighBitTailNode140Vector
  vector_pos := by norm_num [t10j32HighBitTailNode140Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode140Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 140. -/
theorem t10j32HighBitTailNode140MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (140 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode140LhsNum : NNReal) / (t10j32HighBitTailNode140LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode140LhsNum, t10j32HighBitTailNode140LhsDen]

/-- Evaluated row certificate for generated row 140. -/
def t10j32HighBitTailNode140Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (140 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode140Row
  lhs_eq := by simpa using t10j32HighBitTailNode140MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode140Row]


/-- State label for generated row 141. -/
def t10j32HighBitTailNode141Label : String :=
  "v2=8|odd=3|h=1"

/-- Destination support of generated row 141. -/
def t10j32HighBitTailNode141Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 141. -/
def t10j32HighBitTailNode141LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 141. -/
def t10j32HighBitTailNode141LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 141. -/
def t10j32HighBitTailNode141Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 141. -/
theorem t10j32HighBitTailNode141Bound :
    t10j32HighBitTailNode141LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode141Vector * t10j32HighBitTailNode141LhsDen := by
  norm_num [t10j32HighBitTailNode141LhsNum, t10j32HighBitTailNode141LhsDen, t10j32HighBitTailNode141Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 141. -/
def t10j32HighBitTailNode141Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode141LhsNum
  lhsDen := t10j32HighBitTailNode141LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode141LhsDen]
  vector := t10j32HighBitTailNode141Vector
  vector_pos := by norm_num [t10j32HighBitTailNode141Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode141Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 141. -/
theorem t10j32HighBitTailNode141MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (141 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode141LhsNum : NNReal) / (t10j32HighBitTailNode141LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode141LhsNum, t10j32HighBitTailNode141LhsDen]

/-- Evaluated row certificate for generated row 141. -/
def t10j32HighBitTailNode141Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (141 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode141Row
  lhs_eq := by simpa using t10j32HighBitTailNode141MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode141Row]


/-- State label for generated row 142. -/
def t10j32HighBitTailNode142Label : String :=
  "v2=8|odd=3|h=2"

/-- Destination support of generated row 142. -/
def t10j32HighBitTailNode142Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 142. -/
def t10j32HighBitTailNode142LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 142. -/
def t10j32HighBitTailNode142LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 142. -/
def t10j32HighBitTailNode142Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 142. -/
theorem t10j32HighBitTailNode142Bound :
    t10j32HighBitTailNode142LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode142Vector * t10j32HighBitTailNode142LhsDen := by
  norm_num [t10j32HighBitTailNode142LhsNum, t10j32HighBitTailNode142LhsDen, t10j32HighBitTailNode142Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 142. -/
def t10j32HighBitTailNode142Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode142LhsNum
  lhsDen := t10j32HighBitTailNode142LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode142LhsDen]
  vector := t10j32HighBitTailNode142Vector
  vector_pos := by norm_num [t10j32HighBitTailNode142Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode142Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 142. -/
theorem t10j32HighBitTailNode142MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (142 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode142LhsNum : NNReal) / (t10j32HighBitTailNode142LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode142LhsNum, t10j32HighBitTailNode142LhsDen]

/-- Evaluated row certificate for generated row 142. -/
def t10j32HighBitTailNode142Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (142 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode142Row
  lhs_eq := by simpa using t10j32HighBitTailNode142MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode142Row]


/-- State label for generated row 143. -/
def t10j32HighBitTailNode143Label : String :=
  "v2=8|odd=3|h=3"

/-- Destination support of generated row 143. -/
def t10j32HighBitTailNode143Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 143. -/
def t10j32HighBitTailNode143LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 143. -/
def t10j32HighBitTailNode143LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 143. -/
def t10j32HighBitTailNode143Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 143. -/
theorem t10j32HighBitTailNode143Bound :
    t10j32HighBitTailNode143LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode143Vector * t10j32HighBitTailNode143LhsDen := by
  norm_num [t10j32HighBitTailNode143LhsNum, t10j32HighBitTailNode143LhsDen, t10j32HighBitTailNode143Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 143. -/
def t10j32HighBitTailNode143Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode143LhsNum
  lhsDen := t10j32HighBitTailNode143LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode143LhsDen]
  vector := t10j32HighBitTailNode143Vector
  vector_pos := by norm_num [t10j32HighBitTailNode143Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode143Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 143. -/
theorem t10j32HighBitTailNode143MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (143 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode143LhsNum : NNReal) / (t10j32HighBitTailNode143LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode143LhsNum, t10j32HighBitTailNode143LhsDen]

/-- Evaluated row certificate for generated row 143. -/
def t10j32HighBitTailNode143Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (143 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode143Row
  lhs_eq := by simpa using t10j32HighBitTailNode143MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode143Row]

end Generated
end CollatzShadowing
