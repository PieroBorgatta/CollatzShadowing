import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 0. -/
def t10j32HighBitTailNode000Label : String :=
  "v2=0|odd=0|h=0"

/-- Destination support of generated row 0. -/
def t10j32HighBitTailNode000Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 0. -/
def t10j32HighBitTailNode000LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 0. -/
def t10j32HighBitTailNode000LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 0. -/
def t10j32HighBitTailNode000Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 0. -/
theorem t10j32HighBitTailNode000Bound :
    t10j32HighBitTailNode000LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode000Vector * t10j32HighBitTailNode000LhsDen := by
  norm_num [t10j32HighBitTailNode000LhsNum, t10j32HighBitTailNode000LhsDen, t10j32HighBitTailNode000Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 0. -/
def t10j32HighBitTailNode000Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode000LhsNum
  lhsDen := t10j32HighBitTailNode000LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode000LhsDen]
  vector := t10j32HighBitTailNode000Vector
  vector_pos := by norm_num [t10j32HighBitTailNode000Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode000Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 0. -/
theorem t10j32HighBitTailNode000MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (0 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode000LhsNum : NNReal) / (t10j32HighBitTailNode000LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode000LhsNum, t10j32HighBitTailNode000LhsDen]

/-- Evaluated row certificate for generated row 0. -/
def t10j32HighBitTailNode000Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (0 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode000Row
  lhs_eq := by simpa using t10j32HighBitTailNode000MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode000Row]


/-- State label for generated row 1. -/
def t10j32HighBitTailNode001Label : String :=
  "v2=0|odd=0|h=1"

/-- Destination support of generated row 1. -/
def t10j32HighBitTailNode001Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 1. -/
def t10j32HighBitTailNode001LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 1. -/
def t10j32HighBitTailNode001LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 1. -/
def t10j32HighBitTailNode001Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 1. -/
theorem t10j32HighBitTailNode001Bound :
    t10j32HighBitTailNode001LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode001Vector * t10j32HighBitTailNode001LhsDen := by
  norm_num [t10j32HighBitTailNode001LhsNum, t10j32HighBitTailNode001LhsDen, t10j32HighBitTailNode001Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 1. -/
def t10j32HighBitTailNode001Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode001LhsNum
  lhsDen := t10j32HighBitTailNode001LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode001LhsDen]
  vector := t10j32HighBitTailNode001Vector
  vector_pos := by norm_num [t10j32HighBitTailNode001Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode001Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 1. -/
theorem t10j32HighBitTailNode001MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (1 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode001LhsNum : NNReal) / (t10j32HighBitTailNode001LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode001LhsNum, t10j32HighBitTailNode001LhsDen]

/-- Evaluated row certificate for generated row 1. -/
def t10j32HighBitTailNode001Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (1 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode001Row
  lhs_eq := by simpa using t10j32HighBitTailNode001MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode001Row]


/-- State label for generated row 2. -/
def t10j32HighBitTailNode002Label : String :=
  "v2=0|odd=0|h=2"

/-- Destination support of generated row 2. -/
def t10j32HighBitTailNode002Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 2. -/
def t10j32HighBitTailNode002LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 2. -/
def t10j32HighBitTailNode002LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 2. -/
def t10j32HighBitTailNode002Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 2. -/
theorem t10j32HighBitTailNode002Bound :
    t10j32HighBitTailNode002LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode002Vector * t10j32HighBitTailNode002LhsDen := by
  norm_num [t10j32HighBitTailNode002LhsNum, t10j32HighBitTailNode002LhsDen, t10j32HighBitTailNode002Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 2. -/
def t10j32HighBitTailNode002Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode002LhsNum
  lhsDen := t10j32HighBitTailNode002LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode002LhsDen]
  vector := t10j32HighBitTailNode002Vector
  vector_pos := by norm_num [t10j32HighBitTailNode002Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode002Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 2. -/
theorem t10j32HighBitTailNode002MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (2 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode002LhsNum : NNReal) / (t10j32HighBitTailNode002LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode002LhsNum, t10j32HighBitTailNode002LhsDen]

/-- Evaluated row certificate for generated row 2. -/
def t10j32HighBitTailNode002Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (2 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode002Row
  lhs_eq := by simpa using t10j32HighBitTailNode002MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode002Row]


/-- State label for generated row 3. -/
def t10j32HighBitTailNode003Label : String :=
  "v2=0|odd=0|h=3"

/-- Destination support of generated row 3. -/
def t10j32HighBitTailNode003Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 3. -/
def t10j32HighBitTailNode003LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 3. -/
def t10j32HighBitTailNode003LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 3. -/
def t10j32HighBitTailNode003Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 3. -/
theorem t10j32HighBitTailNode003Bound :
    t10j32HighBitTailNode003LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode003Vector * t10j32HighBitTailNode003LhsDen := by
  norm_num [t10j32HighBitTailNode003LhsNum, t10j32HighBitTailNode003LhsDen, t10j32HighBitTailNode003Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 3. -/
def t10j32HighBitTailNode003Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode003LhsNum
  lhsDen := t10j32HighBitTailNode003LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode003LhsDen]
  vector := t10j32HighBitTailNode003Vector
  vector_pos := by norm_num [t10j32HighBitTailNode003Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode003Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 3. -/
theorem t10j32HighBitTailNode003MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (3 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode003LhsNum : NNReal) / (t10j32HighBitTailNode003LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode003LhsNum, t10j32HighBitTailNode003LhsDen]

/-- Evaluated row certificate for generated row 3. -/
def t10j32HighBitTailNode003Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (3 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode003Row
  lhs_eq := by simpa using t10j32HighBitTailNode003MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode003Row]


/-- State label for generated row 4. -/
def t10j32HighBitTailNode004Label : String :=
  "v2=0|odd=1|h=0"

/-- Destination support of generated row 4. -/
def t10j32HighBitTailNode004Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 37, 45, 53, 61, 69, 77, 85, 93, 101, 109, 117, 125, 141, 189, 221}

/-- Exact generated summand values for row 4. -/
noncomputable def t10j32HighBitTailNode004Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((301219057 : NNReal) / (16384 : NNReal))
  | 13 => ((14329204905 : NNReal) / (1048576 : NNReal))
  | 21 => ((2976821379 : NNReal) / (524288 : NNReal))
  | 29 => ((1721194995 : NNReal) / (262144 : NNReal))
  | 37 => ((687977403 : NNReal) / (262144 : NNReal))
  | 45 => ((13608574425 : NNReal) / (524288 : NNReal))
  | 53 => ((54267255 : NNReal) / (32768 : NNReal))
  | 61 => ((575906447 : NNReal) / (262144 : NNReal))
  | 69 => ((421875 : NNReal) / (1024 : NNReal))
  | 77 => ((578125 : NNReal) / (1024 : NNReal))
  | 85 => ((20176057 : NNReal) / (65536 : NNReal))
  | 93 => ((46875 : NNReal) / (256 : NNReal))
  | 101 => ((2635567 : NNReal) / (16384 : NNReal))
  | 109 => ((46875 : NNReal) / (256 : NNReal))
  | 117 => ((2448779 : NNReal) / (32768 : NNReal))
  | 125 => ((5746581 : NNReal) / (65536 : NNReal))
  | 141 => ((15625 : NNReal) / (512 : NNReal))
  | 189 => ((15625 : NNReal) / (512 : NNReal))
  | 221 => ((15625 : NNReal) / (1024 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 4. -/
def t10j32HighBitTailNode004LhsNum : Nat :=
  82604683125

/-- Exact denominator of `(M v)_i` for generated row 4. -/
def t10j32HighBitTailNode004LhsDen : Nat :=
  1048576

/-- Exact vector entry for generated row 4. -/
def t10j32HighBitTailNode004Vector : Nat :=
  2624288

/-- Exact cleared-denominator CW inequality for generated row 4. -/
theorem t10j32HighBitTailNode004Bound :
    t10j32HighBitTailNode004LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode004Vector * t10j32HighBitTailNode004LhsDen := by
  norm_num [t10j32HighBitTailNode004LhsNum, t10j32HighBitTailNode004LhsDen, t10j32HighBitTailNode004Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 4. -/
def t10j32HighBitTailNode004Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode004LhsNum
  lhsDen := t10j32HighBitTailNode004LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode004LhsDen]
  vector := t10j32HighBitTailNode004Vector
  vector_pos := by norm_num [t10j32HighBitTailNode004Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode004Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 4. -/
theorem t10j32HighBitTailNode004MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (4 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode004LhsNum : NNReal) / (t10j32HighBitTailNode004LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode004Support,
      t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (5 : T10J32HighBitTailState) := by
      change (((3673 : NNReal) / (524288 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode004Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h013 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (13 : T10J32HighBitTailState) := by
      change (((6645 : NNReal) / (1048576 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode004Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h021 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (21 : T10J32HighBitTailState) := by
      change (((2121 : NNReal) / (524288 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode004Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h029 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (29 : T10J32HighBitTailState) := by
      change (((897 : NNReal) / (262144 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode004Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h037 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (37 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (37 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (37 : T10J32HighBitTailState) := by
      change (((437 : NNReal) / (262144 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode004Term (37 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h045 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (45 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (45 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (45 : T10J32HighBitTailState) := by
      change (((1075 : NNReal) / (524288 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode004Term (45 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h053 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (53 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (53 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (53 : T10J32HighBitTailState) := by
      change (((49 : NNReal) / (65536 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode004Term (53 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h061 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (61 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (61 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (61 : T10J32HighBitTailState) := by
      change (((601 : NNReal) / (524288 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode004Term (61 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h069 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (69 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (69 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (69 : T10J32HighBitTailState) := by
      change (((27 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode004Term (69 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h077 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (77 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (77 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (77 : T10J32HighBitTailState) := by
      change (((37 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode004Term (77 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h085 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (85 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (85 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (85 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (65536 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode004Term (85 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h093 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (93 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (93 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (93 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode004Term (93 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h101 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (101 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (101 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (101 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (131072 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode004Term (101 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h109 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (109 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (109 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (109 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode004Term (109 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h117 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (117 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (117 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (117 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode004Term (117 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h125 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (125 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (125 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (125 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode004Term (125 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h141 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (141 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (141 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (141 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode004Term (141 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h189 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (189 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (189 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (189 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode004Term (189 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    have h221 :
        t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) (221 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (221 : T10J32HighBitTailState) =
          t10j32HighBitTailNode004Term (221 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode004Term (221 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode004Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode004Support,
          t10j32HighBitTailMatrix (4 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode004Support, t10j32HighBitTailNode004Term dst := by
        simp [t10j32HighBitTailNode004Support, h005, h013, h021, h029, h037, h045, h053, h061, h069, h077, h085, h093, h101, h109, h117, h125, h141, h189, h221]
      _ = (t10j32HighBitTailNode004LhsNum : NNReal) / (t10j32HighBitTailNode004LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode004Support, t10j32HighBitTailNode004Term]
        norm_num [t10j32HighBitTailNode004LhsNum, t10j32HighBitTailNode004LhsDen]

/-- Evaluated row certificate for generated row 4. -/
def t10j32HighBitTailNode004Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (4 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode004Row
  lhs_eq := by simpa using t10j32HighBitTailNode004MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode004Row]


/-- State label for generated row 5. -/
def t10j32HighBitTailNode005Label : String :=
  "v2=0|odd=1|h=1"

/-- Destination support of generated row 5. -/
def t10j32HighBitTailNode005Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 38, 46, 54, 62, 70, 78, 86, 94, 102, 110, 118, 126, 142, 190, 222}

/-- Exact generated summand values for row 5. -/
noncomputable def t10j32HighBitTailNode005Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((301219057 : NNReal) / (16384 : NNReal))
  | 14 => ((14329204905 : NNReal) / (1048576 : NNReal))
  | 22 => ((2976821379 : NNReal) / (524288 : NNReal))
  | 30 => ((1721194995 : NNReal) / (262144 : NNReal))
  | 38 => ((687977403 : NNReal) / (262144 : NNReal))
  | 46 => ((13608574425 : NNReal) / (524288 : NNReal))
  | 54 => ((54267255 : NNReal) / (32768 : NNReal))
  | 62 => ((575906447 : NNReal) / (262144 : NNReal))
  | 70 => ((421875 : NNReal) / (1024 : NNReal))
  | 78 => ((578125 : NNReal) / (1024 : NNReal))
  | 86 => ((20176057 : NNReal) / (65536 : NNReal))
  | 94 => ((46875 : NNReal) / (256 : NNReal))
  | 102 => ((2635567 : NNReal) / (16384 : NNReal))
  | 110 => ((46875 : NNReal) / (256 : NNReal))
  | 118 => ((2448779 : NNReal) / (32768 : NNReal))
  | 126 => ((5746581 : NNReal) / (65536 : NNReal))
  | 142 => ((15625 : NNReal) / (512 : NNReal))
  | 190 => ((15625 : NNReal) / (512 : NNReal))
  | 222 => ((15625 : NNReal) / (1024 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 5. -/
def t10j32HighBitTailNode005LhsNum : Nat :=
  82604683125

/-- Exact denominator of `(M v)_i` for generated row 5. -/
def t10j32HighBitTailNode005LhsDen : Nat :=
  1048576

/-- Exact vector entry for generated row 5. -/
def t10j32HighBitTailNode005Vector : Nat :=
  2624288

/-- Exact cleared-denominator CW inequality for generated row 5. -/
theorem t10j32HighBitTailNode005Bound :
    t10j32HighBitTailNode005LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode005Vector * t10j32HighBitTailNode005LhsDen := by
  norm_num [t10j32HighBitTailNode005LhsNum, t10j32HighBitTailNode005LhsDen, t10j32HighBitTailNode005Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 5. -/
def t10j32HighBitTailNode005Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode005LhsNum
  lhsDen := t10j32HighBitTailNode005LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode005LhsDen]
  vector := t10j32HighBitTailNode005Vector
  vector_pos := by norm_num [t10j32HighBitTailNode005Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode005Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 5. -/
theorem t10j32HighBitTailNode005MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (5 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode005LhsNum : NNReal) / (t10j32HighBitTailNode005LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode005Support,
      t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (6 : T10J32HighBitTailState) := by
      change (((3673 : NNReal) / (524288 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode005Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h014 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (14 : T10J32HighBitTailState) := by
      change (((6645 : NNReal) / (1048576 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode005Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h022 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (22 : T10J32HighBitTailState) := by
      change (((2121 : NNReal) / (524288 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode005Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h030 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (30 : T10J32HighBitTailState) := by
      change (((897 : NNReal) / (262144 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode005Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h038 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (38 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (38 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (38 : T10J32HighBitTailState) := by
      change (((437 : NNReal) / (262144 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode005Term (38 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h046 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (46 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (46 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (46 : T10J32HighBitTailState) := by
      change (((1075 : NNReal) / (524288 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode005Term (46 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h054 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (54 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (54 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (54 : T10J32HighBitTailState) := by
      change (((49 : NNReal) / (65536 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode005Term (54 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h062 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (62 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (62 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (62 : T10J32HighBitTailState) := by
      change (((601 : NNReal) / (524288 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode005Term (62 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h070 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (70 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (70 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (70 : T10J32HighBitTailState) := by
      change (((27 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode005Term (70 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h078 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (78 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (78 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (78 : T10J32HighBitTailState) := by
      change (((37 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode005Term (78 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h086 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (86 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (86 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (86 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (65536 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode005Term (86 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h094 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (94 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (94 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (94 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode005Term (94 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h102 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (102 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (102 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (102 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (131072 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode005Term (102 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h110 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (110 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (110 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (110 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode005Term (110 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h118 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (118 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (118 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (118 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode005Term (118 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h126 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (126 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (126 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (126 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode005Term (126 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h142 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (142 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (142 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (142 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode005Term (142 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h190 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (190 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (190 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (190 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode005Term (190 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    have h222 :
        t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) (222 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (222 : T10J32HighBitTailState) =
          t10j32HighBitTailNode005Term (222 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode005Term (222 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode005Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode005Support,
          t10j32HighBitTailMatrix (5 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode005Support, t10j32HighBitTailNode005Term dst := by
        simp [t10j32HighBitTailNode005Support, h006, h014, h022, h030, h038, h046, h054, h062, h070, h078, h086, h094, h102, h110, h118, h126, h142, h190, h222]
      _ = (t10j32HighBitTailNode005LhsNum : NNReal) / (t10j32HighBitTailNode005LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode005Support, t10j32HighBitTailNode005Term]
        norm_num [t10j32HighBitTailNode005LhsNum, t10j32HighBitTailNode005LhsDen]

/-- Evaluated row certificate for generated row 5. -/
def t10j32HighBitTailNode005Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (5 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode005Row
  lhs_eq := by simpa using t10j32HighBitTailNode005MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode005Row]


/-- State label for generated row 6. -/
def t10j32HighBitTailNode006Label : String :=
  "v2=0|odd=1|h=2"

/-- Destination support of generated row 6. -/
def t10j32HighBitTailNode006Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 39, 47, 55, 63, 71, 79, 87, 95, 103, 111, 119, 127, 143, 191, 223}

/-- Exact generated summand values for row 6. -/
noncomputable def t10j32HighBitTailNode006Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((301219057 : NNReal) / (16384 : NNReal))
  | 15 => ((14329204905 : NNReal) / (1048576 : NNReal))
  | 23 => ((2976821379 : NNReal) / (524288 : NNReal))
  | 31 => ((1721194995 : NNReal) / (262144 : NNReal))
  | 39 => ((687977403 : NNReal) / (262144 : NNReal))
  | 47 => ((13608574425 : NNReal) / (524288 : NNReal))
  | 55 => ((54267255 : NNReal) / (32768 : NNReal))
  | 63 => ((575906447 : NNReal) / (262144 : NNReal))
  | 71 => ((421875 : NNReal) / (1024 : NNReal))
  | 79 => ((578125 : NNReal) / (1024 : NNReal))
  | 87 => ((20176057 : NNReal) / (65536 : NNReal))
  | 95 => ((46875 : NNReal) / (256 : NNReal))
  | 103 => ((2635567 : NNReal) / (16384 : NNReal))
  | 111 => ((46875 : NNReal) / (256 : NNReal))
  | 119 => ((2448779 : NNReal) / (32768 : NNReal))
  | 127 => ((5746581 : NNReal) / (65536 : NNReal))
  | 143 => ((15625 : NNReal) / (512 : NNReal))
  | 191 => ((15625 : NNReal) / (512 : NNReal))
  | 223 => ((15625 : NNReal) / (1024 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 6. -/
def t10j32HighBitTailNode006LhsNum : Nat :=
  82604683125

/-- Exact denominator of `(M v)_i` for generated row 6. -/
def t10j32HighBitTailNode006LhsDen : Nat :=
  1048576

/-- Exact vector entry for generated row 6. -/
def t10j32HighBitTailNode006Vector : Nat :=
  2624288

/-- Exact cleared-denominator CW inequality for generated row 6. -/
theorem t10j32HighBitTailNode006Bound :
    t10j32HighBitTailNode006LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode006Vector * t10j32HighBitTailNode006LhsDen := by
  norm_num [t10j32HighBitTailNode006LhsNum, t10j32HighBitTailNode006LhsDen, t10j32HighBitTailNode006Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 6. -/
def t10j32HighBitTailNode006Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode006LhsNum
  lhsDen := t10j32HighBitTailNode006LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode006LhsDen]
  vector := t10j32HighBitTailNode006Vector
  vector_pos := by norm_num [t10j32HighBitTailNode006Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode006Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 6. -/
theorem t10j32HighBitTailNode006MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (6 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode006LhsNum : NNReal) / (t10j32HighBitTailNode006LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode006Support,
      t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (7 : T10J32HighBitTailState) := by
      change (((3673 : NNReal) / (524288 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode006Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h015 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (15 : T10J32HighBitTailState) := by
      change (((6645 : NNReal) / (1048576 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode006Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h023 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (23 : T10J32HighBitTailState) := by
      change (((2121 : NNReal) / (524288 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode006Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h031 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (31 : T10J32HighBitTailState) := by
      change (((897 : NNReal) / (262144 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode006Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h039 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (39 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (39 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (39 : T10J32HighBitTailState) := by
      change (((437 : NNReal) / (262144 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode006Term (39 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h047 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (47 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (47 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (47 : T10J32HighBitTailState) := by
      change (((1075 : NNReal) / (524288 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode006Term (47 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h055 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (55 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (55 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (55 : T10J32HighBitTailState) := by
      change (((49 : NNReal) / (65536 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode006Term (55 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h063 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (63 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (63 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (63 : T10J32HighBitTailState) := by
      change (((601 : NNReal) / (524288 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode006Term (63 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h071 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (71 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (71 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (71 : T10J32HighBitTailState) := by
      change (((27 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode006Term (71 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h079 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (79 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (79 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (79 : T10J32HighBitTailState) := by
      change (((37 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode006Term (79 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h087 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (87 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (87 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (87 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (65536 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode006Term (87 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h095 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (95 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (95 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (95 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode006Term (95 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h103 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (103 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (103 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (103 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (131072 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode006Term (103 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h111 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (111 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (111 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (111 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode006Term (111 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h119 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (119 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (119 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (119 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode006Term (119 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h127 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (127 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (127 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (127 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode006Term (127 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h143 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (143 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (143 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (143 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode006Term (143 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h191 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (191 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (191 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (191 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode006Term (191 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    have h223 :
        t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) (223 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (223 : T10J32HighBitTailState) =
          t10j32HighBitTailNode006Term (223 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode006Term (223 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode006Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode006Support,
          t10j32HighBitTailMatrix (6 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode006Support, t10j32HighBitTailNode006Term dst := by
        simp [t10j32HighBitTailNode006Support, h007, h015, h023, h031, h039, h047, h055, h063, h071, h079, h087, h095, h103, h111, h119, h127, h143, h191, h223]
      _ = (t10j32HighBitTailNode006LhsNum : NNReal) / (t10j32HighBitTailNode006LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode006Support, t10j32HighBitTailNode006Term]
        norm_num [t10j32HighBitTailNode006LhsNum, t10j32HighBitTailNode006LhsDen]

/-- Evaluated row certificate for generated row 6. -/
def t10j32HighBitTailNode006Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (6 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode006Row
  lhs_eq := by simpa using t10j32HighBitTailNode006MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode006Row]


/-- State label for generated row 7. -/
def t10j32HighBitTailNode007Label : String :=
  "v2=0|odd=1|h=3"

/-- Destination support of generated row 7. -/
def t10j32HighBitTailNode007Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100, 108, 116, 124, 140, 188, 220}

/-- Exact generated summand values for row 7. -/
noncomputable def t10j32HighBitTailNode007Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((301219057 : NNReal) / (16384 : NNReal))
  | 12 => ((14329204905 : NNReal) / (1048576 : NNReal))
  | 20 => ((2976821379 : NNReal) / (524288 : NNReal))
  | 28 => ((1721194995 : NNReal) / (262144 : NNReal))
  | 36 => ((687977403 : NNReal) / (262144 : NNReal))
  | 44 => ((13608574425 : NNReal) / (524288 : NNReal))
  | 52 => ((54267255 : NNReal) / (32768 : NNReal))
  | 60 => ((575906447 : NNReal) / (262144 : NNReal))
  | 68 => ((421875 : NNReal) / (1024 : NNReal))
  | 76 => ((578125 : NNReal) / (1024 : NNReal))
  | 84 => ((20176057 : NNReal) / (65536 : NNReal))
  | 92 => ((46875 : NNReal) / (256 : NNReal))
  | 100 => ((2635567 : NNReal) / (16384 : NNReal))
  | 108 => ((46875 : NNReal) / (256 : NNReal))
  | 116 => ((2448779 : NNReal) / (32768 : NNReal))
  | 124 => ((5746581 : NNReal) / (65536 : NNReal))
  | 140 => ((15625 : NNReal) / (512 : NNReal))
  | 188 => ((15625 : NNReal) / (512 : NNReal))
  | 220 => ((15625 : NNReal) / (1024 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 7. -/
def t10j32HighBitTailNode007LhsNum : Nat :=
  82604683125

/-- Exact denominator of `(M v)_i` for generated row 7. -/
def t10j32HighBitTailNode007LhsDen : Nat :=
  1048576

/-- Exact vector entry for generated row 7. -/
def t10j32HighBitTailNode007Vector : Nat :=
  2624288

/-- Exact cleared-denominator CW inequality for generated row 7. -/
theorem t10j32HighBitTailNode007Bound :
    t10j32HighBitTailNode007LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode007Vector * t10j32HighBitTailNode007LhsDen := by
  norm_num [t10j32HighBitTailNode007LhsNum, t10j32HighBitTailNode007LhsDen, t10j32HighBitTailNode007Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 7. -/
def t10j32HighBitTailNode007Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode007LhsNum
  lhsDen := t10j32HighBitTailNode007LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode007LhsDen]
  vector := t10j32HighBitTailNode007Vector
  vector_pos := by norm_num [t10j32HighBitTailNode007Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode007Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 7. -/
theorem t10j32HighBitTailNode007MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (7 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode007LhsNum : NNReal) / (t10j32HighBitTailNode007LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode007Support,
      t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (4 : T10J32HighBitTailState) := by
      change (((3673 : NNReal) / (524288 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode007Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h012 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (12 : T10J32HighBitTailState) := by
      change (((6645 : NNReal) / (1048576 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode007Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h020 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (20 : T10J32HighBitTailState) := by
      change (((2121 : NNReal) / (524288 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode007Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h028 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (28 : T10J32HighBitTailState) := by
      change (((897 : NNReal) / (262144 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode007Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h036 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (36 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (36 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (36 : T10J32HighBitTailState) := by
      change (((437 : NNReal) / (262144 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode007Term (36 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h044 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (44 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (44 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (44 : T10J32HighBitTailState) := by
      change (((1075 : NNReal) / (524288 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode007Term (44 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h052 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (52 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (52 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (52 : T10J32HighBitTailState) := by
      change (((49 : NNReal) / (65536 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode007Term (52 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h060 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (60 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (60 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (60 : T10J32HighBitTailState) := by
      change (((601 : NNReal) / (524288 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode007Term (60 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h068 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (68 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (68 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (68 : T10J32HighBitTailState) := by
      change (((27 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode007Term (68 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h076 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (76 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (76 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (76 : T10J32HighBitTailState) := by
      change (((37 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode007Term (76 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h084 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (84 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (84 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (84 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (65536 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode007Term (84 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h092 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (92 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (92 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (92 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode007Term (92 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h100 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (100 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (100 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (100 : T10J32HighBitTailState) := by
      change (((11 : NNReal) / (131072 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode007Term (100 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h108 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (108 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (108 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (108 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode007Term (108 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h116 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (116 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (116 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (116 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode007Term (116 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h124 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (124 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (124 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (124 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode007Term (124 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h140 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (140 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (140 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (140 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode007Term (140 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h188 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (188 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (188 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (188 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode007Term (188 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    have h220 :
        t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) (220 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (220 : T10J32HighBitTailState) =
          t10j32HighBitTailNode007Term (220 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode007Term (220 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode007Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode007Support,
          t10j32HighBitTailMatrix (7 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode007Support, t10j32HighBitTailNode007Term dst := by
        simp [t10j32HighBitTailNode007Support, h004, h012, h020, h028, h036, h044, h052, h060, h068, h076, h084, h092, h100, h108, h116, h124, h140, h188, h220]
      _ = (t10j32HighBitTailNode007LhsNum : NNReal) / (t10j32HighBitTailNode007LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode007Support, t10j32HighBitTailNode007Term]
        norm_num [t10j32HighBitTailNode007LhsNum, t10j32HighBitTailNode007LhsDen]

/-- Evaluated row certificate for generated row 7. -/
def t10j32HighBitTailNode007Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (7 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode007Row
  lhs_eq := by simpa using t10j32HighBitTailNode007MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode007Row]


/-- State label for generated row 8. -/
def t10j32HighBitTailNode008Label : String :=
  "v2=0|odd=2|h=0"

/-- Destination support of generated row 8. -/
def t10j32HighBitTailNode008Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 8. -/
def t10j32HighBitTailNode008LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 8. -/
def t10j32HighBitTailNode008LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 8. -/
def t10j32HighBitTailNode008Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 8. -/
theorem t10j32HighBitTailNode008Bound :
    t10j32HighBitTailNode008LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode008Vector * t10j32HighBitTailNode008LhsDen := by
  norm_num [t10j32HighBitTailNode008LhsNum, t10j32HighBitTailNode008LhsDen, t10j32HighBitTailNode008Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 8. -/
def t10j32HighBitTailNode008Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode008LhsNum
  lhsDen := t10j32HighBitTailNode008LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode008LhsDen]
  vector := t10j32HighBitTailNode008Vector
  vector_pos := by norm_num [t10j32HighBitTailNode008Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode008Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 8. -/
theorem t10j32HighBitTailNode008MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (8 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode008LhsNum : NNReal) / (t10j32HighBitTailNode008LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode008LhsNum, t10j32HighBitTailNode008LhsDen]

/-- Evaluated row certificate for generated row 8. -/
def t10j32HighBitTailNode008Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (8 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode008Row
  lhs_eq := by simpa using t10j32HighBitTailNode008MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode008Row]


/-- State label for generated row 9. -/
def t10j32HighBitTailNode009Label : String :=
  "v2=0|odd=2|h=1"

/-- Destination support of generated row 9. -/
def t10j32HighBitTailNode009Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 9. -/
def t10j32HighBitTailNode009LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 9. -/
def t10j32HighBitTailNode009LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 9. -/
def t10j32HighBitTailNode009Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 9. -/
theorem t10j32HighBitTailNode009Bound :
    t10j32HighBitTailNode009LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode009Vector * t10j32HighBitTailNode009LhsDen := by
  norm_num [t10j32HighBitTailNode009LhsNum, t10j32HighBitTailNode009LhsDen, t10j32HighBitTailNode009Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 9. -/
def t10j32HighBitTailNode009Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode009LhsNum
  lhsDen := t10j32HighBitTailNode009LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode009LhsDen]
  vector := t10j32HighBitTailNode009Vector
  vector_pos := by norm_num [t10j32HighBitTailNode009Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode009Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 9. -/
theorem t10j32HighBitTailNode009MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (9 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode009LhsNum : NNReal) / (t10j32HighBitTailNode009LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode009LhsNum, t10j32HighBitTailNode009LhsDen]

/-- Evaluated row certificate for generated row 9. -/
def t10j32HighBitTailNode009Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (9 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode009Row
  lhs_eq := by simpa using t10j32HighBitTailNode009MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode009Row]


/-- State label for generated row 10. -/
def t10j32HighBitTailNode010Label : String :=
  "v2=0|odd=2|h=2"

/-- Destination support of generated row 10. -/
def t10j32HighBitTailNode010Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 10. -/
def t10j32HighBitTailNode010LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 10. -/
def t10j32HighBitTailNode010LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 10. -/
def t10j32HighBitTailNode010Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 10. -/
theorem t10j32HighBitTailNode010Bound :
    t10j32HighBitTailNode010LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode010Vector * t10j32HighBitTailNode010LhsDen := by
  norm_num [t10j32HighBitTailNode010LhsNum, t10j32HighBitTailNode010LhsDen, t10j32HighBitTailNode010Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 10. -/
def t10j32HighBitTailNode010Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode010LhsNum
  lhsDen := t10j32HighBitTailNode010LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode010LhsDen]
  vector := t10j32HighBitTailNode010Vector
  vector_pos := by norm_num [t10j32HighBitTailNode010Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode010Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 10. -/
theorem t10j32HighBitTailNode010MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (10 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode010LhsNum : NNReal) / (t10j32HighBitTailNode010LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode010LhsNum, t10j32HighBitTailNode010LhsDen]

/-- Evaluated row certificate for generated row 10. -/
def t10j32HighBitTailNode010Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (10 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode010Row
  lhs_eq := by simpa using t10j32HighBitTailNode010MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode010Row]


/-- State label for generated row 11. -/
def t10j32HighBitTailNode011Label : String :=
  "v2=0|odd=2|h=3"

/-- Destination support of generated row 11. -/
def t10j32HighBitTailNode011Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 11. -/
def t10j32HighBitTailNode011LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 11. -/
def t10j32HighBitTailNode011LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 11. -/
def t10j32HighBitTailNode011Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 11. -/
theorem t10j32HighBitTailNode011Bound :
    t10j32HighBitTailNode011LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode011Vector * t10j32HighBitTailNode011LhsDen := by
  norm_num [t10j32HighBitTailNode011LhsNum, t10j32HighBitTailNode011LhsDen, t10j32HighBitTailNode011Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 11. -/
def t10j32HighBitTailNode011Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode011LhsNum
  lhsDen := t10j32HighBitTailNode011LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode011LhsDen]
  vector := t10j32HighBitTailNode011Vector
  vector_pos := by norm_num [t10j32HighBitTailNode011Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode011Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 11. -/
theorem t10j32HighBitTailNode011MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (11 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode011LhsNum : NNReal) / (t10j32HighBitTailNode011LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode011LhsNum, t10j32HighBitTailNode011LhsDen]

/-- Evaluated row certificate for generated row 11. -/
def t10j32HighBitTailNode011Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (11 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode011Row
  lhs_eq := by simpa using t10j32HighBitTailNode011MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode011Row]


/-- State label for generated row 12. -/
def t10j32HighBitTailNode012Label : String :=
  "v2=0|odd=3|h=0"

/-- Destination support of generated row 12. -/
def t10j32HighBitTailNode012Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 37, 45, 53, 61, 69, 77, 85, 93, 101, 109, 117, 125, 133, 141, 149, 165, 189}

/-- Exact generated summand values for row 12. -/
noncomputable def t10j32HighBitTailNode012Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((444242753 : NNReal) / (32768 : NNReal))
  | 13 => ((20763869681 : NNReal) / (2097152 : NNReal))
  | 21 => ((7198546371 : NNReal) / (2097152 : NNReal))
  | 29 => ((42223964175 : NNReal) / (8388608 : NNReal))
  | 37 => ((4113695547 : NNReal) / (2097152 : NNReal))
  | 45 => ((38167304085 : NNReal) / (2097152 : NNReal))
  | 53 => ((446320485 : NNReal) / (262144 : NNReal))
  | 61 => ((549075531 : NNReal) / (524288 : NNReal))
  | 69 => ((1359375 : NNReal) / (4096 : NNReal))
  | 77 => ((15625 : NNReal) / (64 : NNReal))
  | 85 => ((5502561 : NNReal) / (32768 : NNReal))
  | 93 => ((484375 : NNReal) / (4096 : NNReal))
  | 101 => ((718791 : NNReal) / (8192 : NNReal))
  | 109 => ((4515625 : NNReal) / (131072 : NNReal))
  | 117 => ((2448779 : NNReal) / (524288 : NNReal))
  | 125 => ((1915527 : NNReal) / (65536 : NNReal))
  | 133 => ((78125 : NNReal) / (2048 : NNReal))
  | 141 => ((46875 : NNReal) / (1024 : NNReal))
  | 149 => ((3084139 : NNReal) / (65536 : NNReal))
  | 165 => ((572165 : NNReal) / (8192 : NNReal))
  | 189 => ((15625 : NNReal) / (512 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 12. -/
def t10j32HighBitTailNode012LhsNum : Nat :=
  470473967967

/-- Exact denominator of `(M v)_i` for generated row 12. -/
def t10j32HighBitTailNode012LhsDen : Nat :=
  8388608

/-- Exact vector entry for generated row 12. -/
def t10j32HighBitTailNode012Vector : Nat :=
  2156389

/-- Exact cleared-denominator CW inequality for generated row 12. -/
theorem t10j32HighBitTailNode012Bound :
    t10j32HighBitTailNode012LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode012Vector * t10j32HighBitTailNode012LhsDen := by
  norm_num [t10j32HighBitTailNode012LhsNum, t10j32HighBitTailNode012LhsDen, t10j32HighBitTailNode012Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 12. -/
def t10j32HighBitTailNode012Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode012LhsNum
  lhsDen := t10j32HighBitTailNode012LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode012LhsDen]
  vector := t10j32HighBitTailNode012Vector
  vector_pos := by norm_num [t10j32HighBitTailNode012Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode012Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 12. -/
theorem t10j32HighBitTailNode012MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (12 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode012LhsNum : NNReal) / (t10j32HighBitTailNode012LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode012Support,
      t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (5 : T10J32HighBitTailState) := by
      change (((5417 : NNReal) / (1048576 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode012Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h013 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (13 : T10J32HighBitTailState) := by
      change (((9629 : NNReal) / (2097152 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode012Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h021 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (21 : T10J32HighBitTailState) := by
      change (((5129 : NNReal) / (2097152 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode012Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h029 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (29 : T10J32HighBitTailState) := by
      change (((22005 : NNReal) / (8388608 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode012Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h037 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (37 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (37 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (37 : T10J32HighBitTailState) := by
      change (((2613 : NNReal) / (2097152 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode012Term (37 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h045 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (45 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (45 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (45 : T10J32HighBitTailState) := by
      change (((3015 : NNReal) / (2097152 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode012Term (45 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h053 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (53 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (53 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (53 : T10J32HighBitTailState) := by
      change (((403 : NNReal) / (524288 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode012Term (53 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h061 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (61 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (61 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (61 : T10J32HighBitTailState) := by
      change (((573 : NNReal) / (1048576 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode012Term (61 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h069 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (69 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (69 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (69 : T10J32HighBitTailState) := by
      change (((87 : NNReal) / (262144 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode012Term (69 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h077 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (77 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (77 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (77 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode012Term (77 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h085 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (85 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (85 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (85 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (32768 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode012Term (85 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h093 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (93 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (93 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (93 : T10J32HighBitTailState) := by
      change (((31 : NNReal) / (262144 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode012Term (93 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h101 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (101 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (101 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (101 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode012Term (101 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h109 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (109 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (109 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (109 : T10J32HighBitTailState) := by
      change (((289 : NNReal) / (8388608 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode012Term (109 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h117 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (117 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (117 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (117 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (524288 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode012Term (117 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h125 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (125 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (125 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (125 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode012Term (125 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h133 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (133 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (133 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (133 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (131072 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode012Term (133 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h141 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (141 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (141 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (141 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode012Term (141 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h149 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (149 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (149 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (149 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (3084139 : NNReal)) =
        t10j32HighBitTailNode012Term (149 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h165 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (165 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (165 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (165 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2288660 : NNReal)) =
        t10j32HighBitTailNode012Term (165 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    have h189 :
        t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) (189 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (189 : T10J32HighBitTailState) =
          t10j32HighBitTailNode012Term (189 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode012Term (189 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode012Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode012Support,
          t10j32HighBitTailMatrix (12 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode012Support, t10j32HighBitTailNode012Term dst := by
        simp [t10j32HighBitTailNode012Support, h005, h013, h021, h029, h037, h045, h053, h061, h069, h077, h085, h093, h101, h109, h117, h125, h133, h141, h149, h165, h189]
      _ = (t10j32HighBitTailNode012LhsNum : NNReal) / (t10j32HighBitTailNode012LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode012Support, t10j32HighBitTailNode012Term]
        norm_num [t10j32HighBitTailNode012LhsNum, t10j32HighBitTailNode012LhsDen]

/-- Evaluated row certificate for generated row 12. -/
def t10j32HighBitTailNode012Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (12 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode012Row
  lhs_eq := by simpa using t10j32HighBitTailNode012MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode012Row]


/-- State label for generated row 13. -/
def t10j32HighBitTailNode013Label : String :=
  "v2=0|odd=3|h=1"

/-- Destination support of generated row 13. -/
def t10j32HighBitTailNode013Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 38, 46, 54, 62, 70, 78, 86, 94, 102, 110, 118, 126, 134, 142, 150, 166, 190}

/-- Exact generated summand values for row 13. -/
noncomputable def t10j32HighBitTailNode013Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((444242753 : NNReal) / (32768 : NNReal))
  | 14 => ((20763869681 : NNReal) / (2097152 : NNReal))
  | 22 => ((7198546371 : NNReal) / (2097152 : NNReal))
  | 30 => ((42223964175 : NNReal) / (8388608 : NNReal))
  | 38 => ((4113695547 : NNReal) / (2097152 : NNReal))
  | 46 => ((38167304085 : NNReal) / (2097152 : NNReal))
  | 54 => ((446320485 : NNReal) / (262144 : NNReal))
  | 62 => ((549075531 : NNReal) / (524288 : NNReal))
  | 70 => ((1359375 : NNReal) / (4096 : NNReal))
  | 78 => ((15625 : NNReal) / (64 : NNReal))
  | 86 => ((5502561 : NNReal) / (32768 : NNReal))
  | 94 => ((484375 : NNReal) / (4096 : NNReal))
  | 102 => ((718791 : NNReal) / (8192 : NNReal))
  | 110 => ((4515625 : NNReal) / (131072 : NNReal))
  | 118 => ((2448779 : NNReal) / (524288 : NNReal))
  | 126 => ((1915527 : NNReal) / (65536 : NNReal))
  | 134 => ((78125 : NNReal) / (2048 : NNReal))
  | 142 => ((46875 : NNReal) / (1024 : NNReal))
  | 150 => ((3084139 : NNReal) / (65536 : NNReal))
  | 166 => ((572165 : NNReal) / (8192 : NNReal))
  | 190 => ((15625 : NNReal) / (512 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 13. -/
def t10j32HighBitTailNode013LhsNum : Nat :=
  470473967967

/-- Exact denominator of `(M v)_i` for generated row 13. -/
def t10j32HighBitTailNode013LhsDen : Nat :=
  8388608

/-- Exact vector entry for generated row 13. -/
def t10j32HighBitTailNode013Vector : Nat :=
  2156389

/-- Exact cleared-denominator CW inequality for generated row 13. -/
theorem t10j32HighBitTailNode013Bound :
    t10j32HighBitTailNode013LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode013Vector * t10j32HighBitTailNode013LhsDen := by
  norm_num [t10j32HighBitTailNode013LhsNum, t10j32HighBitTailNode013LhsDen, t10j32HighBitTailNode013Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 13. -/
def t10j32HighBitTailNode013Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode013LhsNum
  lhsDen := t10j32HighBitTailNode013LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode013LhsDen]
  vector := t10j32HighBitTailNode013Vector
  vector_pos := by norm_num [t10j32HighBitTailNode013Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode013Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 13. -/
theorem t10j32HighBitTailNode013MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (13 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode013LhsNum : NNReal) / (t10j32HighBitTailNode013LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode013Support,
      t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (6 : T10J32HighBitTailState) := by
      change (((5417 : NNReal) / (1048576 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode013Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h014 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (14 : T10J32HighBitTailState) := by
      change (((9629 : NNReal) / (2097152 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode013Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h022 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (22 : T10J32HighBitTailState) := by
      change (((5129 : NNReal) / (2097152 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode013Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h030 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (30 : T10J32HighBitTailState) := by
      change (((22005 : NNReal) / (8388608 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode013Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h038 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (38 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (38 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (38 : T10J32HighBitTailState) := by
      change (((2613 : NNReal) / (2097152 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode013Term (38 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h046 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (46 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (46 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (46 : T10J32HighBitTailState) := by
      change (((3015 : NNReal) / (2097152 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode013Term (46 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h054 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (54 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (54 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (54 : T10J32HighBitTailState) := by
      change (((403 : NNReal) / (524288 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode013Term (54 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h062 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (62 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (62 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (62 : T10J32HighBitTailState) := by
      change (((573 : NNReal) / (1048576 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode013Term (62 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h070 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (70 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (70 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (70 : T10J32HighBitTailState) := by
      change (((87 : NNReal) / (262144 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode013Term (70 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h078 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (78 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (78 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (78 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode013Term (78 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h086 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (86 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (86 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (86 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (32768 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode013Term (86 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h094 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (94 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (94 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (94 : T10J32HighBitTailState) := by
      change (((31 : NNReal) / (262144 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode013Term (94 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h102 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (102 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (102 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (102 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode013Term (102 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h110 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (110 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (110 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (110 : T10J32HighBitTailState) := by
      change (((289 : NNReal) / (8388608 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode013Term (110 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h118 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (118 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (118 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (118 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (524288 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode013Term (118 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h126 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (126 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (126 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (126 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode013Term (126 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h134 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (134 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (134 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (134 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (131072 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode013Term (134 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h142 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (142 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (142 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (142 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode013Term (142 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h150 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (150 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (150 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (150 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (3084139 : NNReal)) =
        t10j32HighBitTailNode013Term (150 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h166 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (166 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (166 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (166 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2288660 : NNReal)) =
        t10j32HighBitTailNode013Term (166 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    have h190 :
        t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) (190 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (190 : T10J32HighBitTailState) =
          t10j32HighBitTailNode013Term (190 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode013Term (190 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode013Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode013Support,
          t10j32HighBitTailMatrix (13 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode013Support, t10j32HighBitTailNode013Term dst := by
        simp [t10j32HighBitTailNode013Support, h006, h014, h022, h030, h038, h046, h054, h062, h070, h078, h086, h094, h102, h110, h118, h126, h134, h142, h150, h166, h190]
      _ = (t10j32HighBitTailNode013LhsNum : NNReal) / (t10j32HighBitTailNode013LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode013Support, t10j32HighBitTailNode013Term]
        norm_num [t10j32HighBitTailNode013LhsNum, t10j32HighBitTailNode013LhsDen]

/-- Evaluated row certificate for generated row 13. -/
def t10j32HighBitTailNode013Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (13 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode013Row
  lhs_eq := by simpa using t10j32HighBitTailNode013MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode013Row]


/-- State label for generated row 14. -/
def t10j32HighBitTailNode014Label : String :=
  "v2=0|odd=3|h=2"

/-- Destination support of generated row 14. -/
def t10j32HighBitTailNode014Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 39, 47, 55, 63, 71, 79, 87, 95, 103, 111, 119, 127, 135, 143, 151, 167, 191}

/-- Exact generated summand values for row 14. -/
noncomputable def t10j32HighBitTailNode014Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((444242753 : NNReal) / (32768 : NNReal))
  | 15 => ((20763869681 : NNReal) / (2097152 : NNReal))
  | 23 => ((7198546371 : NNReal) / (2097152 : NNReal))
  | 31 => ((42223964175 : NNReal) / (8388608 : NNReal))
  | 39 => ((4113695547 : NNReal) / (2097152 : NNReal))
  | 47 => ((38167304085 : NNReal) / (2097152 : NNReal))
  | 55 => ((446320485 : NNReal) / (262144 : NNReal))
  | 63 => ((549075531 : NNReal) / (524288 : NNReal))
  | 71 => ((1359375 : NNReal) / (4096 : NNReal))
  | 79 => ((15625 : NNReal) / (64 : NNReal))
  | 87 => ((5502561 : NNReal) / (32768 : NNReal))
  | 95 => ((484375 : NNReal) / (4096 : NNReal))
  | 103 => ((718791 : NNReal) / (8192 : NNReal))
  | 111 => ((4515625 : NNReal) / (131072 : NNReal))
  | 119 => ((2448779 : NNReal) / (524288 : NNReal))
  | 127 => ((1915527 : NNReal) / (65536 : NNReal))
  | 135 => ((78125 : NNReal) / (2048 : NNReal))
  | 143 => ((46875 : NNReal) / (1024 : NNReal))
  | 151 => ((3084139 : NNReal) / (65536 : NNReal))
  | 167 => ((572165 : NNReal) / (8192 : NNReal))
  | 191 => ((15625 : NNReal) / (512 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 14. -/
def t10j32HighBitTailNode014LhsNum : Nat :=
  470473967967

/-- Exact denominator of `(M v)_i` for generated row 14. -/
def t10j32HighBitTailNode014LhsDen : Nat :=
  8388608

/-- Exact vector entry for generated row 14. -/
def t10j32HighBitTailNode014Vector : Nat :=
  2156389

/-- Exact cleared-denominator CW inequality for generated row 14. -/
theorem t10j32HighBitTailNode014Bound :
    t10j32HighBitTailNode014LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode014Vector * t10j32HighBitTailNode014LhsDen := by
  norm_num [t10j32HighBitTailNode014LhsNum, t10j32HighBitTailNode014LhsDen, t10j32HighBitTailNode014Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 14. -/
def t10j32HighBitTailNode014Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode014LhsNum
  lhsDen := t10j32HighBitTailNode014LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode014LhsDen]
  vector := t10j32HighBitTailNode014Vector
  vector_pos := by norm_num [t10j32HighBitTailNode014Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode014Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 14. -/
theorem t10j32HighBitTailNode014MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (14 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode014LhsNum : NNReal) / (t10j32HighBitTailNode014LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode014Support,
      t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (7 : T10J32HighBitTailState) := by
      change (((5417 : NNReal) / (1048576 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode014Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h015 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (15 : T10J32HighBitTailState) := by
      change (((9629 : NNReal) / (2097152 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode014Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h023 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (23 : T10J32HighBitTailState) := by
      change (((5129 : NNReal) / (2097152 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode014Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h031 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (31 : T10J32HighBitTailState) := by
      change (((22005 : NNReal) / (8388608 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode014Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h039 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (39 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (39 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (39 : T10J32HighBitTailState) := by
      change (((2613 : NNReal) / (2097152 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode014Term (39 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h047 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (47 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (47 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (47 : T10J32HighBitTailState) := by
      change (((3015 : NNReal) / (2097152 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode014Term (47 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h055 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (55 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (55 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (55 : T10J32HighBitTailState) := by
      change (((403 : NNReal) / (524288 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode014Term (55 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h063 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (63 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (63 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (63 : T10J32HighBitTailState) := by
      change (((573 : NNReal) / (1048576 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode014Term (63 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h071 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (71 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (71 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (71 : T10J32HighBitTailState) := by
      change (((87 : NNReal) / (262144 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode014Term (71 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h079 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (79 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (79 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (79 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode014Term (79 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h087 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (87 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (87 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (87 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (32768 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode014Term (87 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h095 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (95 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (95 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (95 : T10J32HighBitTailState) := by
      change (((31 : NNReal) / (262144 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode014Term (95 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h103 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (103 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (103 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (103 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode014Term (103 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h111 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (111 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (111 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (111 : T10J32HighBitTailState) := by
      change (((289 : NNReal) / (8388608 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode014Term (111 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h119 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (119 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (119 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (119 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (524288 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode014Term (119 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h127 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (127 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (127 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (127 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode014Term (127 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h135 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (135 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (135 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (135 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (131072 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode014Term (135 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h143 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (143 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (143 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (143 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode014Term (143 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h151 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (151 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (151 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (151 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (3084139 : NNReal)) =
        t10j32HighBitTailNode014Term (151 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h167 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (167 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (167 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (167 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2288660 : NNReal)) =
        t10j32HighBitTailNode014Term (167 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    have h191 :
        t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) (191 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (191 : T10J32HighBitTailState) =
          t10j32HighBitTailNode014Term (191 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode014Term (191 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode014Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode014Support,
          t10j32HighBitTailMatrix (14 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode014Support, t10j32HighBitTailNode014Term dst := by
        simp [t10j32HighBitTailNode014Support, h007, h015, h023, h031, h039, h047, h055, h063, h071, h079, h087, h095, h103, h111, h119, h127, h135, h143, h151, h167, h191]
      _ = (t10j32HighBitTailNode014LhsNum : NNReal) / (t10j32HighBitTailNode014LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode014Support, t10j32HighBitTailNode014Term]
        norm_num [t10j32HighBitTailNode014LhsNum, t10j32HighBitTailNode014LhsDen]

/-- Evaluated row certificate for generated row 14. -/
def t10j32HighBitTailNode014Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (14 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode014Row
  lhs_eq := by simpa using t10j32HighBitTailNode014MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode014Row]


/-- State label for generated row 15. -/
def t10j32HighBitTailNode015Label : String :=
  "v2=0|odd=3|h=3"

/-- Destination support of generated row 15. -/
def t10j32HighBitTailNode015Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100, 108, 116, 124, 132, 140, 148, 164, 188}

/-- Exact generated summand values for row 15. -/
noncomputable def t10j32HighBitTailNode015Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((444242753 : NNReal) / (32768 : NNReal))
  | 12 => ((20763869681 : NNReal) / (2097152 : NNReal))
  | 20 => ((7198546371 : NNReal) / (2097152 : NNReal))
  | 28 => ((42223964175 : NNReal) / (8388608 : NNReal))
  | 36 => ((4113695547 : NNReal) / (2097152 : NNReal))
  | 44 => ((38167304085 : NNReal) / (2097152 : NNReal))
  | 52 => ((446320485 : NNReal) / (262144 : NNReal))
  | 60 => ((549075531 : NNReal) / (524288 : NNReal))
  | 68 => ((1359375 : NNReal) / (4096 : NNReal))
  | 76 => ((15625 : NNReal) / (64 : NNReal))
  | 84 => ((5502561 : NNReal) / (32768 : NNReal))
  | 92 => ((484375 : NNReal) / (4096 : NNReal))
  | 100 => ((718791 : NNReal) / (8192 : NNReal))
  | 108 => ((4515625 : NNReal) / (131072 : NNReal))
  | 116 => ((2448779 : NNReal) / (524288 : NNReal))
  | 124 => ((1915527 : NNReal) / (65536 : NNReal))
  | 132 => ((78125 : NNReal) / (2048 : NNReal))
  | 140 => ((46875 : NNReal) / (1024 : NNReal))
  | 148 => ((3084139 : NNReal) / (65536 : NNReal))
  | 164 => ((572165 : NNReal) / (8192 : NNReal))
  | 188 => ((15625 : NNReal) / (512 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 15. -/
def t10j32HighBitTailNode015LhsNum : Nat :=
  470473967967

/-- Exact denominator of `(M v)_i` for generated row 15. -/
def t10j32HighBitTailNode015LhsDen : Nat :=
  8388608

/-- Exact vector entry for generated row 15. -/
def t10j32HighBitTailNode015Vector : Nat :=
  2156389

/-- Exact cleared-denominator CW inequality for generated row 15. -/
theorem t10j32HighBitTailNode015Bound :
    t10j32HighBitTailNode015LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode015Vector * t10j32HighBitTailNode015LhsDen := by
  norm_num [t10j32HighBitTailNode015LhsNum, t10j32HighBitTailNode015LhsDen, t10j32HighBitTailNode015Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 15. -/
def t10j32HighBitTailNode015Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode015LhsNum
  lhsDen := t10j32HighBitTailNode015LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode015LhsDen]
  vector := t10j32HighBitTailNode015Vector
  vector_pos := by norm_num [t10j32HighBitTailNode015Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode015Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 15. -/
theorem t10j32HighBitTailNode015MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (15 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode015LhsNum : NNReal) / (t10j32HighBitTailNode015LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode015Support,
      t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (4 : T10J32HighBitTailState) := by
      change (((5417 : NNReal) / (1048576 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode015Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h012 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (12 : T10J32HighBitTailState) := by
      change (((9629 : NNReal) / (2097152 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode015Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h020 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (20 : T10J32HighBitTailState) := by
      change (((5129 : NNReal) / (2097152 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode015Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h028 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (28 : T10J32HighBitTailState) := by
      change (((22005 : NNReal) / (8388608 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode015Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h036 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (36 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (36 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (36 : T10J32HighBitTailState) := by
      change (((2613 : NNReal) / (2097152 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode015Term (36 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h044 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (44 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (44 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (44 : T10J32HighBitTailState) := by
      change (((3015 : NNReal) / (2097152 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode015Term (44 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h052 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (52 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (52 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (52 : T10J32HighBitTailState) := by
      change (((403 : NNReal) / (524288 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode015Term (52 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h060 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (60 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (60 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (60 : T10J32HighBitTailState) := by
      change (((573 : NNReal) / (1048576 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode015Term (60 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h068 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (68 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (68 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (68 : T10J32HighBitTailState) := by
      change (((87 : NNReal) / (262144 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode015Term (68 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h076 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (76 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (76 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (76 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode015Term (76 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h084 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (84 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (84 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (84 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (32768 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode015Term (84 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h092 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (92 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (92 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (92 : T10J32HighBitTailState) := by
      change (((31 : NNReal) / (262144 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode015Term (92 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h100 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (100 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (100 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (100 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode015Term (100 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h108 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (108 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (108 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (108 : T10J32HighBitTailState) := by
      change (((289 : NNReal) / (8388608 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode015Term (108 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h116 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (116 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (116 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (116 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (524288 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode015Term (116 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h124 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (124 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (124 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (124 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode015Term (124 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h132 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (132 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (132 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (132 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (131072 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode015Term (132 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h140 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (140 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (140 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (140 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (65536 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode015Term (140 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h148 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (148 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (148 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (148 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (65536 : NNReal)) * (3084139 : NNReal)) =
        t10j32HighBitTailNode015Term (148 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h164 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (164 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (164 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (164 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2288660 : NNReal)) =
        t10j32HighBitTailNode015Term (164 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    have h188 :
        t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) (188 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (188 : T10J32HighBitTailState) =
          t10j32HighBitTailNode015Term (188 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode015Term (188 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode015Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode015Support,
          t10j32HighBitTailMatrix (15 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode015Support, t10j32HighBitTailNode015Term dst := by
        simp [t10j32HighBitTailNode015Support, h004, h012, h020, h028, h036, h044, h052, h060, h068, h076, h084, h092, h100, h108, h116, h124, h132, h140, h148, h164, h188]
      _ = (t10j32HighBitTailNode015LhsNum : NNReal) / (t10j32HighBitTailNode015LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode015Support, t10j32HighBitTailNode015Term]
        norm_num [t10j32HighBitTailNode015LhsNum, t10j32HighBitTailNode015LhsDen]

/-- Evaluated row certificate for generated row 15. -/
def t10j32HighBitTailNode015Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (15 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode015Row
  lhs_eq := by simpa using t10j32HighBitTailNode015MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode015Row]

end Generated
end CollatzShadowing
