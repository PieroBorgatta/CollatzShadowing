import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 80. -/
def t10j32HighBitTailNode080Label : String :=
  "v2=5|odd=0|h=0"

/-- Destination support of generated row 80. -/
def t10j32HighBitTailNode080Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 80. -/
def t10j32HighBitTailNode080LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 80. -/
def t10j32HighBitTailNode080LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 80. -/
def t10j32HighBitTailNode080Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 80. -/
theorem t10j32HighBitTailNode080Bound :
    t10j32HighBitTailNode080LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode080Vector * t10j32HighBitTailNode080LhsDen := by
  norm_num [t10j32HighBitTailNode080LhsNum, t10j32HighBitTailNode080LhsDen, t10j32HighBitTailNode080Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 80. -/
def t10j32HighBitTailNode080Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode080LhsNum
  lhsDen := t10j32HighBitTailNode080LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode080LhsDen]
  vector := t10j32HighBitTailNode080Vector
  vector_pos := by norm_num [t10j32HighBitTailNode080Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode080Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 80. -/
theorem t10j32HighBitTailNode080MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (80 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode080LhsNum : NNReal) / (t10j32HighBitTailNode080LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode080LhsNum, t10j32HighBitTailNode080LhsDen]

/-- Evaluated row certificate for generated row 80. -/
def t10j32HighBitTailNode080Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (80 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode080Row
  lhs_eq := by simpa using t10j32HighBitTailNode080MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode080Row]


/-- State label for generated row 81. -/
def t10j32HighBitTailNode081Label : String :=
  "v2=5|odd=0|h=1"

/-- Destination support of generated row 81. -/
def t10j32HighBitTailNode081Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 81. -/
def t10j32HighBitTailNode081LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 81. -/
def t10j32HighBitTailNode081LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 81. -/
def t10j32HighBitTailNode081Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 81. -/
theorem t10j32HighBitTailNode081Bound :
    t10j32HighBitTailNode081LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode081Vector * t10j32HighBitTailNode081LhsDen := by
  norm_num [t10j32HighBitTailNode081LhsNum, t10j32HighBitTailNode081LhsDen, t10j32HighBitTailNode081Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 81. -/
def t10j32HighBitTailNode081Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode081LhsNum
  lhsDen := t10j32HighBitTailNode081LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode081LhsDen]
  vector := t10j32HighBitTailNode081Vector
  vector_pos := by norm_num [t10j32HighBitTailNode081Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode081Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 81. -/
theorem t10j32HighBitTailNode081MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (81 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode081LhsNum : NNReal) / (t10j32HighBitTailNode081LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode081LhsNum, t10j32HighBitTailNode081LhsDen]

/-- Evaluated row certificate for generated row 81. -/
def t10j32HighBitTailNode081Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (81 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode081Row
  lhs_eq := by simpa using t10j32HighBitTailNode081MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode081Row]


/-- State label for generated row 82. -/
def t10j32HighBitTailNode082Label : String :=
  "v2=5|odd=0|h=2"

/-- Destination support of generated row 82. -/
def t10j32HighBitTailNode082Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 82. -/
def t10j32HighBitTailNode082LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 82. -/
def t10j32HighBitTailNode082LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 82. -/
def t10j32HighBitTailNode082Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 82. -/
theorem t10j32HighBitTailNode082Bound :
    t10j32HighBitTailNode082LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode082Vector * t10j32HighBitTailNode082LhsDen := by
  norm_num [t10j32HighBitTailNode082LhsNum, t10j32HighBitTailNode082LhsDen, t10j32HighBitTailNode082Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 82. -/
def t10j32HighBitTailNode082Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode082LhsNum
  lhsDen := t10j32HighBitTailNode082LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode082LhsDen]
  vector := t10j32HighBitTailNode082Vector
  vector_pos := by norm_num [t10j32HighBitTailNode082Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode082Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 82. -/
theorem t10j32HighBitTailNode082MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (82 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode082LhsNum : NNReal) / (t10j32HighBitTailNode082LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode082LhsNum, t10j32HighBitTailNode082LhsDen]

/-- Evaluated row certificate for generated row 82. -/
def t10j32HighBitTailNode082Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (82 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode082Row
  lhs_eq := by simpa using t10j32HighBitTailNode082MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode082Row]


/-- State label for generated row 83. -/
def t10j32HighBitTailNode083Label : String :=
  "v2=5|odd=0|h=3"

/-- Destination support of generated row 83. -/
def t10j32HighBitTailNode083Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 83. -/
def t10j32HighBitTailNode083LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 83. -/
def t10j32HighBitTailNode083LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 83. -/
def t10j32HighBitTailNode083Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 83. -/
theorem t10j32HighBitTailNode083Bound :
    t10j32HighBitTailNode083LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode083Vector * t10j32HighBitTailNode083LhsDen := by
  norm_num [t10j32HighBitTailNode083LhsNum, t10j32HighBitTailNode083LhsDen, t10j32HighBitTailNode083Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 83. -/
def t10j32HighBitTailNode083Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode083LhsNum
  lhsDen := t10j32HighBitTailNode083LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode083LhsDen]
  vector := t10j32HighBitTailNode083Vector
  vector_pos := by norm_num [t10j32HighBitTailNode083Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode083Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 83. -/
theorem t10j32HighBitTailNode083MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (83 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode083LhsNum : NNReal) / (t10j32HighBitTailNode083LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode083LhsNum, t10j32HighBitTailNode083LhsDen]

/-- Evaluated row certificate for generated row 83. -/
def t10j32HighBitTailNode083Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (83 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode083Row
  lhs_eq := by simpa using t10j32HighBitTailNode083MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode083Row]


/-- State label for generated row 84. -/
def t10j32HighBitTailNode084Label : String :=
  "v2=5|odd=1|h=0"

/-- Destination support of generated row 84. -/
def t10j32HighBitTailNode084Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29}

/-- Exact generated summand values for row 84. -/
noncomputable def t10j32HighBitTailNode084Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((738081 : NNReal) / (32 : NNReal))
  | 13 => ((2156389 : NNReal) / (512 : NNReal))
  | 21 => ((46315467 : NNReal) / (4096 : NNReal))
  | 29 => ((1918835 : NNReal) / (1024 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 84. -/
def t10j32HighBitTailNode084LhsNum : Nat :=
  165716287

/-- Exact denominator of `(M v)_i` for generated row 84. -/
def t10j32HighBitTailNode084LhsDen : Nat :=
  4096

/-- Exact vector entry for generated row 84. -/
def t10j32HighBitTailNode084Vector : Nat :=
  1834187

/-- Exact cleared-denominator CW inequality for generated row 84. -/
theorem t10j32HighBitTailNode084Bound :
    t10j32HighBitTailNode084LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode084Vector * t10j32HighBitTailNode084LhsDen := by
  norm_num [t10j32HighBitTailNode084LhsNum, t10j32HighBitTailNode084LhsDen, t10j32HighBitTailNode084Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 84. -/
def t10j32HighBitTailNode084Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode084LhsNum
  lhsDen := t10j32HighBitTailNode084LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode084LhsDen]
  vector := t10j32HighBitTailNode084Vector
  vector_pos := by norm_num [t10j32HighBitTailNode084Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode084Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 84. -/
theorem t10j32HighBitTailNode084MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (84 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode084LhsNum : NNReal) / (t10j32HighBitTailNode084LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode084Support,
      t10j32HighBitTailMatrix (84 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (84 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode084Term (5 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (1024 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode084Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode084Term]
    have h013 :
        t10j32HighBitTailMatrix (84 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode084Term (13 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (512 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode084Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode084Term]
    have h021 :
        t10j32HighBitTailMatrix (84 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode084Term (21 : T10J32HighBitTailState) := by
      change (((33 : NNReal) / (4096 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode084Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode084Term]
    have h029 :
        t10j32HighBitTailMatrix (84 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode084Term (29 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (1024 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode084Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode084Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode084Support,
          t10j32HighBitTailMatrix (84 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode084Support, t10j32HighBitTailNode084Term dst := by
        simp [t10j32HighBitTailNode084Support, h005, h013, h021, h029]
      _ = (t10j32HighBitTailNode084LhsNum : NNReal) / (t10j32HighBitTailNode084LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode084Support, t10j32HighBitTailNode084Term]
        norm_num [t10j32HighBitTailNode084LhsNum, t10j32HighBitTailNode084LhsDen]

/-- Evaluated row certificate for generated row 84. -/
def t10j32HighBitTailNode084Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (84 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode084Row
  lhs_eq := by simpa using t10j32HighBitTailNode084MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode084Row]


/-- State label for generated row 85. -/
def t10j32HighBitTailNode085Label : String :=
  "v2=5|odd=1|h=1"

/-- Destination support of generated row 85. -/
def t10j32HighBitTailNode085Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30}

/-- Exact generated summand values for row 85. -/
noncomputable def t10j32HighBitTailNode085Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((738081 : NNReal) / (32 : NNReal))
  | 14 => ((2156389 : NNReal) / (512 : NNReal))
  | 22 => ((46315467 : NNReal) / (4096 : NNReal))
  | 30 => ((1918835 : NNReal) / (1024 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 85. -/
def t10j32HighBitTailNode085LhsNum : Nat :=
  165716287

/-- Exact denominator of `(M v)_i` for generated row 85. -/
def t10j32HighBitTailNode085LhsDen : Nat :=
  4096

/-- Exact vector entry for generated row 85. -/
def t10j32HighBitTailNode085Vector : Nat :=
  1834187

/-- Exact cleared-denominator CW inequality for generated row 85. -/
theorem t10j32HighBitTailNode085Bound :
    t10j32HighBitTailNode085LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode085Vector * t10j32HighBitTailNode085LhsDen := by
  norm_num [t10j32HighBitTailNode085LhsNum, t10j32HighBitTailNode085LhsDen, t10j32HighBitTailNode085Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 85. -/
def t10j32HighBitTailNode085Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode085LhsNum
  lhsDen := t10j32HighBitTailNode085LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode085LhsDen]
  vector := t10j32HighBitTailNode085Vector
  vector_pos := by norm_num [t10j32HighBitTailNode085Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode085Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 85. -/
theorem t10j32HighBitTailNode085MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (85 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode085LhsNum : NNReal) / (t10j32HighBitTailNode085LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode085Support,
      t10j32HighBitTailMatrix (85 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (85 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode085Term (6 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (1024 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode085Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode085Term]
    have h014 :
        t10j32HighBitTailMatrix (85 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode085Term (14 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (512 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode085Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode085Term]
    have h022 :
        t10j32HighBitTailMatrix (85 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode085Term (22 : T10J32HighBitTailState) := by
      change (((33 : NNReal) / (4096 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode085Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode085Term]
    have h030 :
        t10j32HighBitTailMatrix (85 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode085Term (30 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (1024 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode085Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode085Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode085Support,
          t10j32HighBitTailMatrix (85 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode085Support, t10j32HighBitTailNode085Term dst := by
        simp [t10j32HighBitTailNode085Support, h006, h014, h022, h030]
      _ = (t10j32HighBitTailNode085LhsNum : NNReal) / (t10j32HighBitTailNode085LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode085Support, t10j32HighBitTailNode085Term]
        norm_num [t10j32HighBitTailNode085LhsNum, t10j32HighBitTailNode085LhsDen]

/-- Evaluated row certificate for generated row 85. -/
def t10j32HighBitTailNode085Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (85 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode085Row
  lhs_eq := by simpa using t10j32HighBitTailNode085MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode085Row]


/-- State label for generated row 86. -/
def t10j32HighBitTailNode086Label : String :=
  "v2=5|odd=1|h=2"

/-- Destination support of generated row 86. -/
def t10j32HighBitTailNode086Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31}

/-- Exact generated summand values for row 86. -/
noncomputable def t10j32HighBitTailNode086Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((738081 : NNReal) / (32 : NNReal))
  | 15 => ((2156389 : NNReal) / (512 : NNReal))
  | 23 => ((46315467 : NNReal) / (4096 : NNReal))
  | 31 => ((1918835 : NNReal) / (1024 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 86. -/
def t10j32HighBitTailNode086LhsNum : Nat :=
  165716287

/-- Exact denominator of `(M v)_i` for generated row 86. -/
def t10j32HighBitTailNode086LhsDen : Nat :=
  4096

/-- Exact vector entry for generated row 86. -/
def t10j32HighBitTailNode086Vector : Nat :=
  1834187

/-- Exact cleared-denominator CW inequality for generated row 86. -/
theorem t10j32HighBitTailNode086Bound :
    t10j32HighBitTailNode086LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode086Vector * t10j32HighBitTailNode086LhsDen := by
  norm_num [t10j32HighBitTailNode086LhsNum, t10j32HighBitTailNode086LhsDen, t10j32HighBitTailNode086Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 86. -/
def t10j32HighBitTailNode086Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode086LhsNum
  lhsDen := t10j32HighBitTailNode086LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode086LhsDen]
  vector := t10j32HighBitTailNode086Vector
  vector_pos := by norm_num [t10j32HighBitTailNode086Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode086Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 86. -/
theorem t10j32HighBitTailNode086MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (86 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode086LhsNum : NNReal) / (t10j32HighBitTailNode086LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode086Support,
      t10j32HighBitTailMatrix (86 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (86 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode086Term (7 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (1024 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode086Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode086Term]
    have h015 :
        t10j32HighBitTailMatrix (86 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode086Term (15 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (512 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode086Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode086Term]
    have h023 :
        t10j32HighBitTailMatrix (86 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode086Term (23 : T10J32HighBitTailState) := by
      change (((33 : NNReal) / (4096 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode086Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode086Term]
    have h031 :
        t10j32HighBitTailMatrix (86 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode086Term (31 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (1024 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode086Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode086Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode086Support,
          t10j32HighBitTailMatrix (86 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode086Support, t10j32HighBitTailNode086Term dst := by
        simp [t10j32HighBitTailNode086Support, h007, h015, h023, h031]
      _ = (t10j32HighBitTailNode086LhsNum : NNReal) / (t10j32HighBitTailNode086LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode086Support, t10j32HighBitTailNode086Term]
        norm_num [t10j32HighBitTailNode086LhsNum, t10j32HighBitTailNode086LhsDen]

/-- Evaluated row certificate for generated row 86. -/
def t10j32HighBitTailNode086Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (86 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode086Row
  lhs_eq := by simpa using t10j32HighBitTailNode086MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode086Row]


/-- State label for generated row 87. -/
def t10j32HighBitTailNode087Label : String :=
  "v2=5|odd=1|h=3"

/-- Destination support of generated row 87. -/
def t10j32HighBitTailNode087Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28}

/-- Exact generated summand values for row 87. -/
noncomputable def t10j32HighBitTailNode087Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((738081 : NNReal) / (32 : NNReal))
  | 12 => ((2156389 : NNReal) / (512 : NNReal))
  | 20 => ((46315467 : NNReal) / (4096 : NNReal))
  | 28 => ((1918835 : NNReal) / (1024 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 87. -/
def t10j32HighBitTailNode087LhsNum : Nat :=
  165716287

/-- Exact denominator of `(M v)_i` for generated row 87. -/
def t10j32HighBitTailNode087LhsDen : Nat :=
  4096

/-- Exact vector entry for generated row 87. -/
def t10j32HighBitTailNode087Vector : Nat :=
  1834187

/-- Exact cleared-denominator CW inequality for generated row 87. -/
theorem t10j32HighBitTailNode087Bound :
    t10j32HighBitTailNode087LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode087Vector * t10j32HighBitTailNode087LhsDen := by
  norm_num [t10j32HighBitTailNode087LhsNum, t10j32HighBitTailNode087LhsDen, t10j32HighBitTailNode087Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 87. -/
def t10j32HighBitTailNode087Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode087LhsNum
  lhsDen := t10j32HighBitTailNode087LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode087LhsDen]
  vector := t10j32HighBitTailNode087Vector
  vector_pos := by norm_num [t10j32HighBitTailNode087Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode087Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 87. -/
theorem t10j32HighBitTailNode087MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (87 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode087LhsNum : NNReal) / (t10j32HighBitTailNode087LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode087Support,
      t10j32HighBitTailMatrix (87 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (87 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode087Term (4 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (1024 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode087Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode087Term]
    have h012 :
        t10j32HighBitTailMatrix (87 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode087Term (12 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (512 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode087Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode087Term]
    have h020 :
        t10j32HighBitTailMatrix (87 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode087Term (20 : T10J32HighBitTailState) := by
      change (((33 : NNReal) / (4096 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode087Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode087Term]
    have h028 :
        t10j32HighBitTailMatrix (87 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode087Term (28 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (1024 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode087Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode087Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode087Support,
          t10j32HighBitTailMatrix (87 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode087Support, t10j32HighBitTailNode087Term dst := by
        simp [t10j32HighBitTailNode087Support, h004, h012, h020, h028]
      _ = (t10j32HighBitTailNode087LhsNum : NNReal) / (t10j32HighBitTailNode087LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode087Support, t10j32HighBitTailNode087Term]
        norm_num [t10j32HighBitTailNode087LhsNum, t10j32HighBitTailNode087LhsDen]

/-- Evaluated row certificate for generated row 87. -/
def t10j32HighBitTailNode087Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (87 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode087Row
  lhs_eq := by simpa using t10j32HighBitTailNode087MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode087Row]


/-- State label for generated row 88. -/
def t10j32HighBitTailNode088Label : String :=
  "v2=5|odd=2|h=0"

/-- Destination support of generated row 88. -/
def t10j32HighBitTailNode088Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 88. -/
def t10j32HighBitTailNode088LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 88. -/
def t10j32HighBitTailNode088LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 88. -/
def t10j32HighBitTailNode088Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 88. -/
theorem t10j32HighBitTailNode088Bound :
    t10j32HighBitTailNode088LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode088Vector * t10j32HighBitTailNode088LhsDen := by
  norm_num [t10j32HighBitTailNode088LhsNum, t10j32HighBitTailNode088LhsDen, t10j32HighBitTailNode088Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 88. -/
def t10j32HighBitTailNode088Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode088LhsNum
  lhsDen := t10j32HighBitTailNode088LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode088LhsDen]
  vector := t10j32HighBitTailNode088Vector
  vector_pos := by norm_num [t10j32HighBitTailNode088Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode088Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 88. -/
theorem t10j32HighBitTailNode088MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (88 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode088LhsNum : NNReal) / (t10j32HighBitTailNode088LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode088LhsNum, t10j32HighBitTailNode088LhsDen]

/-- Evaluated row certificate for generated row 88. -/
def t10j32HighBitTailNode088Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (88 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode088Row
  lhs_eq := by simpa using t10j32HighBitTailNode088MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode088Row]


/-- State label for generated row 89. -/
def t10j32HighBitTailNode089Label : String :=
  "v2=5|odd=2|h=1"

/-- Destination support of generated row 89. -/
def t10j32HighBitTailNode089Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 89. -/
def t10j32HighBitTailNode089LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 89. -/
def t10j32HighBitTailNode089LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 89. -/
def t10j32HighBitTailNode089Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 89. -/
theorem t10j32HighBitTailNode089Bound :
    t10j32HighBitTailNode089LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode089Vector * t10j32HighBitTailNode089LhsDen := by
  norm_num [t10j32HighBitTailNode089LhsNum, t10j32HighBitTailNode089LhsDen, t10j32HighBitTailNode089Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 89. -/
def t10j32HighBitTailNode089Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode089LhsNum
  lhsDen := t10j32HighBitTailNode089LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode089LhsDen]
  vector := t10j32HighBitTailNode089Vector
  vector_pos := by norm_num [t10j32HighBitTailNode089Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode089Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 89. -/
theorem t10j32HighBitTailNode089MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (89 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode089LhsNum : NNReal) / (t10j32HighBitTailNode089LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode089LhsNum, t10j32HighBitTailNode089LhsDen]

/-- Evaluated row certificate for generated row 89. -/
def t10j32HighBitTailNode089Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (89 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode089Row
  lhs_eq := by simpa using t10j32HighBitTailNode089MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode089Row]


/-- State label for generated row 90. -/
def t10j32HighBitTailNode090Label : String :=
  "v2=5|odd=2|h=2"

/-- Destination support of generated row 90. -/
def t10j32HighBitTailNode090Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 90. -/
def t10j32HighBitTailNode090LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 90. -/
def t10j32HighBitTailNode090LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 90. -/
def t10j32HighBitTailNode090Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 90. -/
theorem t10j32HighBitTailNode090Bound :
    t10j32HighBitTailNode090LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode090Vector * t10j32HighBitTailNode090LhsDen := by
  norm_num [t10j32HighBitTailNode090LhsNum, t10j32HighBitTailNode090LhsDen, t10j32HighBitTailNode090Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 90. -/
def t10j32HighBitTailNode090Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode090LhsNum
  lhsDen := t10j32HighBitTailNode090LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode090LhsDen]
  vector := t10j32HighBitTailNode090Vector
  vector_pos := by norm_num [t10j32HighBitTailNode090Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode090Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 90. -/
theorem t10j32HighBitTailNode090MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (90 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode090LhsNum : NNReal) / (t10j32HighBitTailNode090LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode090LhsNum, t10j32HighBitTailNode090LhsDen]

/-- Evaluated row certificate for generated row 90. -/
def t10j32HighBitTailNode090Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (90 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode090Row
  lhs_eq := by simpa using t10j32HighBitTailNode090MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode090Row]


/-- State label for generated row 91. -/
def t10j32HighBitTailNode091Label : String :=
  "v2=5|odd=2|h=3"

/-- Destination support of generated row 91. -/
def t10j32HighBitTailNode091Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 91. -/
def t10j32HighBitTailNode091LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 91. -/
def t10j32HighBitTailNode091LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 91. -/
def t10j32HighBitTailNode091Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 91. -/
theorem t10j32HighBitTailNode091Bound :
    t10j32HighBitTailNode091LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode091Vector * t10j32HighBitTailNode091LhsDen := by
  norm_num [t10j32HighBitTailNode091LhsNum, t10j32HighBitTailNode091LhsDen, t10j32HighBitTailNode091Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 91. -/
def t10j32HighBitTailNode091Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode091LhsNum
  lhsDen := t10j32HighBitTailNode091LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode091LhsDen]
  vector := t10j32HighBitTailNode091Vector
  vector_pos := by norm_num [t10j32HighBitTailNode091Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode091Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 91. -/
theorem t10j32HighBitTailNode091MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (91 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode091LhsNum : NNReal) / (t10j32HighBitTailNode091LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode091LhsNum, t10j32HighBitTailNode091LhsDen]

/-- Evaluated row certificate for generated row 91. -/
def t10j32HighBitTailNode091Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (91 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode091Row
  lhs_eq := by simpa using t10j32HighBitTailNode091MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode091Row]


/-- State label for generated row 92. -/
def t10j32HighBitTailNode092Label : String :=
  "v2=5|odd=3|h=0"

/-- Destination support of generated row 92. -/
def t10j32HighBitTailNode092Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 92. -/
def t10j32HighBitTailNode092LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 92. -/
def t10j32HighBitTailNode092LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 92. -/
def t10j32HighBitTailNode092Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 92. -/
theorem t10j32HighBitTailNode092Bound :
    t10j32HighBitTailNode092LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode092Vector * t10j32HighBitTailNode092LhsDen := by
  norm_num [t10j32HighBitTailNode092LhsNum, t10j32HighBitTailNode092LhsDen, t10j32HighBitTailNode092Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 92. -/
def t10j32HighBitTailNode092Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode092LhsNum
  lhsDen := t10j32HighBitTailNode092LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode092LhsDen]
  vector := t10j32HighBitTailNode092Vector
  vector_pos := by norm_num [t10j32HighBitTailNode092Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode092Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 92. -/
theorem t10j32HighBitTailNode092MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (92 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode092LhsNum : NNReal) / (t10j32HighBitTailNode092LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode092LhsNum, t10j32HighBitTailNode092LhsDen]

/-- Evaluated row certificate for generated row 92. -/
def t10j32HighBitTailNode092Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (92 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode092Row
  lhs_eq := by simpa using t10j32HighBitTailNode092MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode092Row]


/-- State label for generated row 93. -/
def t10j32HighBitTailNode093Label : String :=
  "v2=5|odd=3|h=1"

/-- Destination support of generated row 93. -/
def t10j32HighBitTailNode093Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 93. -/
def t10j32HighBitTailNode093LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 93. -/
def t10j32HighBitTailNode093LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 93. -/
def t10j32HighBitTailNode093Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 93. -/
theorem t10j32HighBitTailNode093Bound :
    t10j32HighBitTailNode093LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode093Vector * t10j32HighBitTailNode093LhsDen := by
  norm_num [t10j32HighBitTailNode093LhsNum, t10j32HighBitTailNode093LhsDen, t10j32HighBitTailNode093Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 93. -/
def t10j32HighBitTailNode093Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode093LhsNum
  lhsDen := t10j32HighBitTailNode093LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode093LhsDen]
  vector := t10j32HighBitTailNode093Vector
  vector_pos := by norm_num [t10j32HighBitTailNode093Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode093Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 93. -/
theorem t10j32HighBitTailNode093MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (93 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode093LhsNum : NNReal) / (t10j32HighBitTailNode093LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode093LhsNum, t10j32HighBitTailNode093LhsDen]

/-- Evaluated row certificate for generated row 93. -/
def t10j32HighBitTailNode093Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (93 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode093Row
  lhs_eq := by simpa using t10j32HighBitTailNode093MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode093Row]


/-- State label for generated row 94. -/
def t10j32HighBitTailNode094Label : String :=
  "v2=5|odd=3|h=2"

/-- Destination support of generated row 94. -/
def t10j32HighBitTailNode094Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 94. -/
def t10j32HighBitTailNode094LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 94. -/
def t10j32HighBitTailNode094LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 94. -/
def t10j32HighBitTailNode094Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 94. -/
theorem t10j32HighBitTailNode094Bound :
    t10j32HighBitTailNode094LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode094Vector * t10j32HighBitTailNode094LhsDen := by
  norm_num [t10j32HighBitTailNode094LhsNum, t10j32HighBitTailNode094LhsDen, t10j32HighBitTailNode094Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 94. -/
def t10j32HighBitTailNode094Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode094LhsNum
  lhsDen := t10j32HighBitTailNode094LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode094LhsDen]
  vector := t10j32HighBitTailNode094Vector
  vector_pos := by norm_num [t10j32HighBitTailNode094Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode094Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 94. -/
theorem t10j32HighBitTailNode094MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (94 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode094LhsNum : NNReal) / (t10j32HighBitTailNode094LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode094LhsNum, t10j32HighBitTailNode094LhsDen]

/-- Evaluated row certificate for generated row 94. -/
def t10j32HighBitTailNode094Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (94 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode094Row
  lhs_eq := by simpa using t10j32HighBitTailNode094MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode094Row]


/-- State label for generated row 95. -/
def t10j32HighBitTailNode095Label : String :=
  "v2=5|odd=3|h=3"

/-- Destination support of generated row 95. -/
def t10j32HighBitTailNode095Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 95. -/
def t10j32HighBitTailNode095LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 95. -/
def t10j32HighBitTailNode095LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 95. -/
def t10j32HighBitTailNode095Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 95. -/
theorem t10j32HighBitTailNode095Bound :
    t10j32HighBitTailNode095LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode095Vector * t10j32HighBitTailNode095LhsDen := by
  norm_num [t10j32HighBitTailNode095LhsNum, t10j32HighBitTailNode095LhsDen, t10j32HighBitTailNode095Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 95. -/
def t10j32HighBitTailNode095Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode095LhsNum
  lhsDen := t10j32HighBitTailNode095LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode095LhsDen]
  vector := t10j32HighBitTailNode095Vector
  vector_pos := by norm_num [t10j32HighBitTailNode095Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode095Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 95. -/
theorem t10j32HighBitTailNode095MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (95 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode095LhsNum : NNReal) / (t10j32HighBitTailNode095LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode095LhsNum, t10j32HighBitTailNode095LhsDen]

/-- Evaluated row certificate for generated row 95. -/
def t10j32HighBitTailNode095Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (95 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode095Row
  lhs_eq := by simpa using t10j32HighBitTailNode095MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode095Row]

end Generated
end CollatzShadowing
