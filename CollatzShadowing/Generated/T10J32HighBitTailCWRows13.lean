import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 208. -/
def t10j32HighBitTailNode208Label : String :=
  "v2=13|odd=0|h=0"

/-- Destination support of generated row 208. -/
def t10j32HighBitTailNode208Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 208. -/
def t10j32HighBitTailNode208LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 208. -/
def t10j32HighBitTailNode208LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 208. -/
def t10j32HighBitTailNode208Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 208. -/
theorem t10j32HighBitTailNode208Bound :
    t10j32HighBitTailNode208LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode208Vector * t10j32HighBitTailNode208LhsDen := by
  norm_num [t10j32HighBitTailNode208LhsNum, t10j32HighBitTailNode208LhsDen, t10j32HighBitTailNode208Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 208. -/
def t10j32HighBitTailNode208Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode208LhsNum
  lhsDen := t10j32HighBitTailNode208LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode208LhsDen]
  vector := t10j32HighBitTailNode208Vector
  vector_pos := by norm_num [t10j32HighBitTailNode208Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode208Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 208. -/
theorem t10j32HighBitTailNode208MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (208 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode208LhsNum : NNReal) / (t10j32HighBitTailNode208LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode208LhsNum, t10j32HighBitTailNode208LhsDen]

/-- Evaluated row certificate for generated row 208. -/
def t10j32HighBitTailNode208Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (208 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode208Row
  lhs_eq := by simpa using t10j32HighBitTailNode208MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode208Row]


/-- State label for generated row 209. -/
def t10j32HighBitTailNode209Label : String :=
  "v2=13|odd=0|h=1"

/-- Destination support of generated row 209. -/
def t10j32HighBitTailNode209Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 209. -/
def t10j32HighBitTailNode209LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 209. -/
def t10j32HighBitTailNode209LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 209. -/
def t10j32HighBitTailNode209Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 209. -/
theorem t10j32HighBitTailNode209Bound :
    t10j32HighBitTailNode209LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode209Vector * t10j32HighBitTailNode209LhsDen := by
  norm_num [t10j32HighBitTailNode209LhsNum, t10j32HighBitTailNode209LhsDen, t10j32HighBitTailNode209Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 209. -/
def t10j32HighBitTailNode209Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode209LhsNum
  lhsDen := t10j32HighBitTailNode209LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode209LhsDen]
  vector := t10j32HighBitTailNode209Vector
  vector_pos := by norm_num [t10j32HighBitTailNode209Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode209Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 209. -/
theorem t10j32HighBitTailNode209MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (209 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode209LhsNum : NNReal) / (t10j32HighBitTailNode209LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode209LhsNum, t10j32HighBitTailNode209LhsDen]

/-- Evaluated row certificate for generated row 209. -/
def t10j32HighBitTailNode209Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (209 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode209Row
  lhs_eq := by simpa using t10j32HighBitTailNode209MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode209Row]


/-- State label for generated row 210. -/
def t10j32HighBitTailNode210Label : String :=
  "v2=13|odd=0|h=2"

/-- Destination support of generated row 210. -/
def t10j32HighBitTailNode210Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 210. -/
def t10j32HighBitTailNode210LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 210. -/
def t10j32HighBitTailNode210LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 210. -/
def t10j32HighBitTailNode210Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 210. -/
theorem t10j32HighBitTailNode210Bound :
    t10j32HighBitTailNode210LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode210Vector * t10j32HighBitTailNode210LhsDen := by
  norm_num [t10j32HighBitTailNode210LhsNum, t10j32HighBitTailNode210LhsDen, t10j32HighBitTailNode210Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 210. -/
def t10j32HighBitTailNode210Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode210LhsNum
  lhsDen := t10j32HighBitTailNode210LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode210LhsDen]
  vector := t10j32HighBitTailNode210Vector
  vector_pos := by norm_num [t10j32HighBitTailNode210Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode210Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 210. -/
theorem t10j32HighBitTailNode210MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (210 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode210LhsNum : NNReal) / (t10j32HighBitTailNode210LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode210LhsNum, t10j32HighBitTailNode210LhsDen]

/-- Evaluated row certificate for generated row 210. -/
def t10j32HighBitTailNode210Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (210 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode210Row
  lhs_eq := by simpa using t10j32HighBitTailNode210MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode210Row]


/-- State label for generated row 211. -/
def t10j32HighBitTailNode211Label : String :=
  "v2=13|odd=0|h=3"

/-- Destination support of generated row 211. -/
def t10j32HighBitTailNode211Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 211. -/
def t10j32HighBitTailNode211LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 211. -/
def t10j32HighBitTailNode211LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 211. -/
def t10j32HighBitTailNode211Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 211. -/
theorem t10j32HighBitTailNode211Bound :
    t10j32HighBitTailNode211LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode211Vector * t10j32HighBitTailNode211LhsDen := by
  norm_num [t10j32HighBitTailNode211LhsNum, t10j32HighBitTailNode211LhsDen, t10j32HighBitTailNode211Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 211. -/
def t10j32HighBitTailNode211Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode211LhsNum
  lhsDen := t10j32HighBitTailNode211LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode211LhsDen]
  vector := t10j32HighBitTailNode211Vector
  vector_pos := by norm_num [t10j32HighBitTailNode211Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode211Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 211. -/
theorem t10j32HighBitTailNode211MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (211 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode211LhsNum : NNReal) / (t10j32HighBitTailNode211LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode211LhsNum, t10j32HighBitTailNode211LhsDen]

/-- Evaluated row certificate for generated row 211. -/
def t10j32HighBitTailNode211Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (211 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode211Row
  lhs_eq := by simpa using t10j32HighBitTailNode211MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode211Row]


/-- State label for generated row 212. -/
def t10j32HighBitTailNode212Label : String :=
  "v2=13|odd=1|h=0"

/-- Destination support of generated row 212. -/
def t10j32HighBitTailNode212Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 212. -/
def t10j32HighBitTailNode212LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 212. -/
def t10j32HighBitTailNode212LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 212. -/
def t10j32HighBitTailNode212Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 212. -/
theorem t10j32HighBitTailNode212Bound :
    t10j32HighBitTailNode212LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode212Vector * t10j32HighBitTailNode212LhsDen := by
  norm_num [t10j32HighBitTailNode212LhsNum, t10j32HighBitTailNode212LhsDen, t10j32HighBitTailNode212Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 212. -/
def t10j32HighBitTailNode212Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode212LhsNum
  lhsDen := t10j32HighBitTailNode212LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode212LhsDen]
  vector := t10j32HighBitTailNode212Vector
  vector_pos := by norm_num [t10j32HighBitTailNode212Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode212Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 212. -/
theorem t10j32HighBitTailNode212MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (212 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode212LhsNum : NNReal) / (t10j32HighBitTailNode212LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode212LhsNum, t10j32HighBitTailNode212LhsDen]

/-- Evaluated row certificate for generated row 212. -/
def t10j32HighBitTailNode212Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (212 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode212Row
  lhs_eq := by simpa using t10j32HighBitTailNode212MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode212Row]


/-- State label for generated row 213. -/
def t10j32HighBitTailNode213Label : String :=
  "v2=13|odd=1|h=1"

/-- Destination support of generated row 213. -/
def t10j32HighBitTailNode213Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 213. -/
def t10j32HighBitTailNode213LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 213. -/
def t10j32HighBitTailNode213LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 213. -/
def t10j32HighBitTailNode213Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 213. -/
theorem t10j32HighBitTailNode213Bound :
    t10j32HighBitTailNode213LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode213Vector * t10j32HighBitTailNode213LhsDen := by
  norm_num [t10j32HighBitTailNode213LhsNum, t10j32HighBitTailNode213LhsDen, t10j32HighBitTailNode213Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 213. -/
def t10j32HighBitTailNode213Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode213LhsNum
  lhsDen := t10j32HighBitTailNode213LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode213LhsDen]
  vector := t10j32HighBitTailNode213Vector
  vector_pos := by norm_num [t10j32HighBitTailNode213Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode213Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 213. -/
theorem t10j32HighBitTailNode213MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (213 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode213LhsNum : NNReal) / (t10j32HighBitTailNode213LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode213LhsNum, t10j32HighBitTailNode213LhsDen]

/-- Evaluated row certificate for generated row 213. -/
def t10j32HighBitTailNode213Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (213 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode213Row
  lhs_eq := by simpa using t10j32HighBitTailNode213MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode213Row]


/-- State label for generated row 214. -/
def t10j32HighBitTailNode214Label : String :=
  "v2=13|odd=1|h=2"

/-- Destination support of generated row 214. -/
def t10j32HighBitTailNode214Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 214. -/
def t10j32HighBitTailNode214LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 214. -/
def t10j32HighBitTailNode214LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 214. -/
def t10j32HighBitTailNode214Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 214. -/
theorem t10j32HighBitTailNode214Bound :
    t10j32HighBitTailNode214LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode214Vector * t10j32HighBitTailNode214LhsDen := by
  norm_num [t10j32HighBitTailNode214LhsNum, t10j32HighBitTailNode214LhsDen, t10j32HighBitTailNode214Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 214. -/
def t10j32HighBitTailNode214Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode214LhsNum
  lhsDen := t10j32HighBitTailNode214LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode214LhsDen]
  vector := t10j32HighBitTailNode214Vector
  vector_pos := by norm_num [t10j32HighBitTailNode214Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode214Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 214. -/
theorem t10j32HighBitTailNode214MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (214 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode214LhsNum : NNReal) / (t10j32HighBitTailNode214LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode214LhsNum, t10j32HighBitTailNode214LhsDen]

/-- Evaluated row certificate for generated row 214. -/
def t10j32HighBitTailNode214Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (214 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode214Row
  lhs_eq := by simpa using t10j32HighBitTailNode214MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode214Row]


/-- State label for generated row 215. -/
def t10j32HighBitTailNode215Label : String :=
  "v2=13|odd=1|h=3"

/-- Destination support of generated row 215. -/
def t10j32HighBitTailNode215Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 215. -/
def t10j32HighBitTailNode215LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 215. -/
def t10j32HighBitTailNode215LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 215. -/
def t10j32HighBitTailNode215Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 215. -/
theorem t10j32HighBitTailNode215Bound :
    t10j32HighBitTailNode215LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode215Vector * t10j32HighBitTailNode215LhsDen := by
  norm_num [t10j32HighBitTailNode215LhsNum, t10j32HighBitTailNode215LhsDen, t10j32HighBitTailNode215Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 215. -/
def t10j32HighBitTailNode215Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode215LhsNum
  lhsDen := t10j32HighBitTailNode215LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode215LhsDen]
  vector := t10j32HighBitTailNode215Vector
  vector_pos := by norm_num [t10j32HighBitTailNode215Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode215Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 215. -/
theorem t10j32HighBitTailNode215MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (215 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode215LhsNum : NNReal) / (t10j32HighBitTailNode215LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode215LhsNum, t10j32HighBitTailNode215LhsDen]

/-- Evaluated row certificate for generated row 215. -/
def t10j32HighBitTailNode215Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (215 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode215Row
  lhs_eq := by simpa using t10j32HighBitTailNode215MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode215Row]


/-- State label for generated row 216. -/
def t10j32HighBitTailNode216Label : String :=
  "v2=13|odd=2|h=0"

/-- Destination support of generated row 216. -/
def t10j32HighBitTailNode216Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 216. -/
def t10j32HighBitTailNode216LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 216. -/
def t10j32HighBitTailNode216LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 216. -/
def t10j32HighBitTailNode216Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 216. -/
theorem t10j32HighBitTailNode216Bound :
    t10j32HighBitTailNode216LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode216Vector * t10j32HighBitTailNode216LhsDen := by
  norm_num [t10j32HighBitTailNode216LhsNum, t10j32HighBitTailNode216LhsDen, t10j32HighBitTailNode216Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 216. -/
def t10j32HighBitTailNode216Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode216LhsNum
  lhsDen := t10j32HighBitTailNode216LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode216LhsDen]
  vector := t10j32HighBitTailNode216Vector
  vector_pos := by norm_num [t10j32HighBitTailNode216Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode216Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 216. -/
theorem t10j32HighBitTailNode216MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (216 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode216LhsNum : NNReal) / (t10j32HighBitTailNode216LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode216LhsNum, t10j32HighBitTailNode216LhsDen]

/-- Evaluated row certificate for generated row 216. -/
def t10j32HighBitTailNode216Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (216 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode216Row
  lhs_eq := by simpa using t10j32HighBitTailNode216MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode216Row]


/-- State label for generated row 217. -/
def t10j32HighBitTailNode217Label : String :=
  "v2=13|odd=2|h=1"

/-- Destination support of generated row 217. -/
def t10j32HighBitTailNode217Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 217. -/
def t10j32HighBitTailNode217LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 217. -/
def t10j32HighBitTailNode217LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 217. -/
def t10j32HighBitTailNode217Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 217. -/
theorem t10j32HighBitTailNode217Bound :
    t10j32HighBitTailNode217LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode217Vector * t10j32HighBitTailNode217LhsDen := by
  norm_num [t10j32HighBitTailNode217LhsNum, t10j32HighBitTailNode217LhsDen, t10j32HighBitTailNode217Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 217. -/
def t10j32HighBitTailNode217Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode217LhsNum
  lhsDen := t10j32HighBitTailNode217LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode217LhsDen]
  vector := t10j32HighBitTailNode217Vector
  vector_pos := by norm_num [t10j32HighBitTailNode217Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode217Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 217. -/
theorem t10j32HighBitTailNode217MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (217 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode217LhsNum : NNReal) / (t10j32HighBitTailNode217LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode217LhsNum, t10j32HighBitTailNode217LhsDen]

/-- Evaluated row certificate for generated row 217. -/
def t10j32HighBitTailNode217Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (217 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode217Row
  lhs_eq := by simpa using t10j32HighBitTailNode217MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode217Row]


/-- State label for generated row 218. -/
def t10j32HighBitTailNode218Label : String :=
  "v2=13|odd=2|h=2"

/-- Destination support of generated row 218. -/
def t10j32HighBitTailNode218Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 218. -/
def t10j32HighBitTailNode218LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 218. -/
def t10j32HighBitTailNode218LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 218. -/
def t10j32HighBitTailNode218Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 218. -/
theorem t10j32HighBitTailNode218Bound :
    t10j32HighBitTailNode218LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode218Vector * t10j32HighBitTailNode218LhsDen := by
  norm_num [t10j32HighBitTailNode218LhsNum, t10j32HighBitTailNode218LhsDen, t10j32HighBitTailNode218Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 218. -/
def t10j32HighBitTailNode218Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode218LhsNum
  lhsDen := t10j32HighBitTailNode218LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode218LhsDen]
  vector := t10j32HighBitTailNode218Vector
  vector_pos := by norm_num [t10j32HighBitTailNode218Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode218Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 218. -/
theorem t10j32HighBitTailNode218MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (218 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode218LhsNum : NNReal) / (t10j32HighBitTailNode218LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode218LhsNum, t10j32HighBitTailNode218LhsDen]

/-- Evaluated row certificate for generated row 218. -/
def t10j32HighBitTailNode218Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (218 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode218Row
  lhs_eq := by simpa using t10j32HighBitTailNode218MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode218Row]


/-- State label for generated row 219. -/
def t10j32HighBitTailNode219Label : String :=
  "v2=13|odd=2|h=3"

/-- Destination support of generated row 219. -/
def t10j32HighBitTailNode219Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 219. -/
def t10j32HighBitTailNode219LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 219. -/
def t10j32HighBitTailNode219LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 219. -/
def t10j32HighBitTailNode219Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 219. -/
theorem t10j32HighBitTailNode219Bound :
    t10j32HighBitTailNode219LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode219Vector * t10j32HighBitTailNode219LhsDen := by
  norm_num [t10j32HighBitTailNode219LhsNum, t10j32HighBitTailNode219LhsDen, t10j32HighBitTailNode219Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 219. -/
def t10j32HighBitTailNode219Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode219LhsNum
  lhsDen := t10j32HighBitTailNode219LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode219LhsDen]
  vector := t10j32HighBitTailNode219Vector
  vector_pos := by norm_num [t10j32HighBitTailNode219Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode219Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 219. -/
theorem t10j32HighBitTailNode219MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (219 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode219LhsNum : NNReal) / (t10j32HighBitTailNode219LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode219LhsNum, t10j32HighBitTailNode219LhsDen]

/-- Evaluated row certificate for generated row 219. -/
def t10j32HighBitTailNode219Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (219 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode219Row
  lhs_eq := by simpa using t10j32HighBitTailNode219MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode219Row]


/-- State label for generated row 220. -/
def t10j32HighBitTailNode220Label : String :=
  "v2=13|odd=3|h=0"

/-- Destination support of generated row 220. -/
def t10j32HighBitTailNode220Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 220. -/
def t10j32HighBitTailNode220LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 220. -/
def t10j32HighBitTailNode220LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 220. -/
def t10j32HighBitTailNode220Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 220. -/
theorem t10j32HighBitTailNode220Bound :
    t10j32HighBitTailNode220LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode220Vector * t10j32HighBitTailNode220LhsDen := by
  norm_num [t10j32HighBitTailNode220LhsNum, t10j32HighBitTailNode220LhsDen, t10j32HighBitTailNode220Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 220. -/
def t10j32HighBitTailNode220Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode220LhsNum
  lhsDen := t10j32HighBitTailNode220LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode220LhsDen]
  vector := t10j32HighBitTailNode220Vector
  vector_pos := by norm_num [t10j32HighBitTailNode220Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode220Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 220. -/
theorem t10j32HighBitTailNode220MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (220 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode220LhsNum : NNReal) / (t10j32HighBitTailNode220LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode220LhsNum, t10j32HighBitTailNode220LhsDen]

/-- Evaluated row certificate for generated row 220. -/
def t10j32HighBitTailNode220Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (220 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode220Row
  lhs_eq := by simpa using t10j32HighBitTailNode220MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode220Row]


/-- State label for generated row 221. -/
def t10j32HighBitTailNode221Label : String :=
  "v2=13|odd=3|h=1"

/-- Destination support of generated row 221. -/
def t10j32HighBitTailNode221Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 221. -/
def t10j32HighBitTailNode221LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 221. -/
def t10j32HighBitTailNode221LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 221. -/
def t10j32HighBitTailNode221Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 221. -/
theorem t10j32HighBitTailNode221Bound :
    t10j32HighBitTailNode221LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode221Vector * t10j32HighBitTailNode221LhsDen := by
  norm_num [t10j32HighBitTailNode221LhsNum, t10j32HighBitTailNode221LhsDen, t10j32HighBitTailNode221Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 221. -/
def t10j32HighBitTailNode221Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode221LhsNum
  lhsDen := t10j32HighBitTailNode221LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode221LhsDen]
  vector := t10j32HighBitTailNode221Vector
  vector_pos := by norm_num [t10j32HighBitTailNode221Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode221Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 221. -/
theorem t10j32HighBitTailNode221MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (221 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode221LhsNum : NNReal) / (t10j32HighBitTailNode221LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode221LhsNum, t10j32HighBitTailNode221LhsDen]

/-- Evaluated row certificate for generated row 221. -/
def t10j32HighBitTailNode221Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (221 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode221Row
  lhs_eq := by simpa using t10j32HighBitTailNode221MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode221Row]


/-- State label for generated row 222. -/
def t10j32HighBitTailNode222Label : String :=
  "v2=13|odd=3|h=2"

/-- Destination support of generated row 222. -/
def t10j32HighBitTailNode222Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 222. -/
def t10j32HighBitTailNode222LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 222. -/
def t10j32HighBitTailNode222LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 222. -/
def t10j32HighBitTailNode222Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 222. -/
theorem t10j32HighBitTailNode222Bound :
    t10j32HighBitTailNode222LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode222Vector * t10j32HighBitTailNode222LhsDen := by
  norm_num [t10j32HighBitTailNode222LhsNum, t10j32HighBitTailNode222LhsDen, t10j32HighBitTailNode222Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 222. -/
def t10j32HighBitTailNode222Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode222LhsNum
  lhsDen := t10j32HighBitTailNode222LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode222LhsDen]
  vector := t10j32HighBitTailNode222Vector
  vector_pos := by norm_num [t10j32HighBitTailNode222Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode222Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 222. -/
theorem t10j32HighBitTailNode222MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (222 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode222LhsNum : NNReal) / (t10j32HighBitTailNode222LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode222LhsNum, t10j32HighBitTailNode222LhsDen]

/-- Evaluated row certificate for generated row 222. -/
def t10j32HighBitTailNode222Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (222 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode222Row
  lhs_eq := by simpa using t10j32HighBitTailNode222MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode222Row]


/-- State label for generated row 223. -/
def t10j32HighBitTailNode223Label : String :=
  "v2=13|odd=3|h=3"

/-- Destination support of generated row 223. -/
def t10j32HighBitTailNode223Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 223. -/
def t10j32HighBitTailNode223LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 223. -/
def t10j32HighBitTailNode223LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 223. -/
def t10j32HighBitTailNode223Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 223. -/
theorem t10j32HighBitTailNode223Bound :
    t10j32HighBitTailNode223LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode223Vector * t10j32HighBitTailNode223LhsDen := by
  norm_num [t10j32HighBitTailNode223LhsNum, t10j32HighBitTailNode223LhsDen, t10j32HighBitTailNode223Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 223. -/
def t10j32HighBitTailNode223Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode223LhsNum
  lhsDen := t10j32HighBitTailNode223LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode223LhsDen]
  vector := t10j32HighBitTailNode223Vector
  vector_pos := by norm_num [t10j32HighBitTailNode223Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode223Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 223. -/
theorem t10j32HighBitTailNode223MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (223 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode223LhsNum : NNReal) / (t10j32HighBitTailNode223LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode223LhsNum, t10j32HighBitTailNode223LhsDen]

/-- Evaluated row certificate for generated row 223. -/
def t10j32HighBitTailNode223Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (223 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode223Row
  lhs_eq := by simpa using t10j32HighBitTailNode223MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode223Row]

end Generated
end CollatzShadowing
