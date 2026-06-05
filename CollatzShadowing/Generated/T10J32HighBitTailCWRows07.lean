import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 112. -/
def t10j32HighBitTailNode112Label : String :=
  "v2=7|odd=0|h=0"

/-- Destination support of generated row 112. -/
def t10j32HighBitTailNode112Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 112. -/
def t10j32HighBitTailNode112LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 112. -/
def t10j32HighBitTailNode112LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 112. -/
def t10j32HighBitTailNode112Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 112. -/
theorem t10j32HighBitTailNode112Bound :
    t10j32HighBitTailNode112LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode112Vector * t10j32HighBitTailNode112LhsDen := by
  norm_num [t10j32HighBitTailNode112LhsNum, t10j32HighBitTailNode112LhsDen, t10j32HighBitTailNode112Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 112. -/
def t10j32HighBitTailNode112Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode112LhsNum
  lhsDen := t10j32HighBitTailNode112LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode112LhsDen]
  vector := t10j32HighBitTailNode112Vector
  vector_pos := by norm_num [t10j32HighBitTailNode112Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode112Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 112. -/
theorem t10j32HighBitTailNode112MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (112 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode112LhsNum : NNReal) / (t10j32HighBitTailNode112LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode112LhsNum, t10j32HighBitTailNode112LhsDen]

/-- Evaluated row certificate for generated row 112. -/
def t10j32HighBitTailNode112Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (112 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode112Row
  lhs_eq := by simpa using t10j32HighBitTailNode112MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode112Row]


/-- State label for generated row 113. -/
def t10j32HighBitTailNode113Label : String :=
  "v2=7|odd=0|h=1"

/-- Destination support of generated row 113. -/
def t10j32HighBitTailNode113Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 113. -/
def t10j32HighBitTailNode113LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 113. -/
def t10j32HighBitTailNode113LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 113. -/
def t10j32HighBitTailNode113Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 113. -/
theorem t10j32HighBitTailNode113Bound :
    t10j32HighBitTailNode113LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode113Vector * t10j32HighBitTailNode113LhsDen := by
  norm_num [t10j32HighBitTailNode113LhsNum, t10j32HighBitTailNode113LhsDen, t10j32HighBitTailNode113Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 113. -/
def t10j32HighBitTailNode113Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode113LhsNum
  lhsDen := t10j32HighBitTailNode113LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode113LhsDen]
  vector := t10j32HighBitTailNode113Vector
  vector_pos := by norm_num [t10j32HighBitTailNode113Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode113Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 113. -/
theorem t10j32HighBitTailNode113MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (113 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode113LhsNum : NNReal) / (t10j32HighBitTailNode113LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode113LhsNum, t10j32HighBitTailNode113LhsDen]

/-- Evaluated row certificate for generated row 113. -/
def t10j32HighBitTailNode113Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (113 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode113Row
  lhs_eq := by simpa using t10j32HighBitTailNode113MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode113Row]


/-- State label for generated row 114. -/
def t10j32HighBitTailNode114Label : String :=
  "v2=7|odd=0|h=2"

/-- Destination support of generated row 114. -/
def t10j32HighBitTailNode114Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 114. -/
def t10j32HighBitTailNode114LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 114. -/
def t10j32HighBitTailNode114LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 114. -/
def t10j32HighBitTailNode114Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 114. -/
theorem t10j32HighBitTailNode114Bound :
    t10j32HighBitTailNode114LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode114Vector * t10j32HighBitTailNode114LhsDen := by
  norm_num [t10j32HighBitTailNode114LhsNum, t10j32HighBitTailNode114LhsDen, t10j32HighBitTailNode114Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 114. -/
def t10j32HighBitTailNode114Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode114LhsNum
  lhsDen := t10j32HighBitTailNode114LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode114LhsDen]
  vector := t10j32HighBitTailNode114Vector
  vector_pos := by norm_num [t10j32HighBitTailNode114Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode114Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 114. -/
theorem t10j32HighBitTailNode114MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (114 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode114LhsNum : NNReal) / (t10j32HighBitTailNode114LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode114LhsNum, t10j32HighBitTailNode114LhsDen]

/-- Evaluated row certificate for generated row 114. -/
def t10j32HighBitTailNode114Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (114 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode114Row
  lhs_eq := by simpa using t10j32HighBitTailNode114MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode114Row]


/-- State label for generated row 115. -/
def t10j32HighBitTailNode115Label : String :=
  "v2=7|odd=0|h=3"

/-- Destination support of generated row 115. -/
def t10j32HighBitTailNode115Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 115. -/
def t10j32HighBitTailNode115LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 115. -/
def t10j32HighBitTailNode115LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 115. -/
def t10j32HighBitTailNode115Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 115. -/
theorem t10j32HighBitTailNode115Bound :
    t10j32HighBitTailNode115LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode115Vector * t10j32HighBitTailNode115LhsDen := by
  norm_num [t10j32HighBitTailNode115LhsNum, t10j32HighBitTailNode115LhsDen, t10j32HighBitTailNode115Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 115. -/
def t10j32HighBitTailNode115Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode115LhsNum
  lhsDen := t10j32HighBitTailNode115LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode115LhsDen]
  vector := t10j32HighBitTailNode115Vector
  vector_pos := by norm_num [t10j32HighBitTailNode115Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode115Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 115. -/
theorem t10j32HighBitTailNode115MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (115 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode115LhsNum : NNReal) / (t10j32HighBitTailNode115LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode115LhsNum, t10j32HighBitTailNode115LhsDen]

/-- Evaluated row certificate for generated row 115. -/
def t10j32HighBitTailNode115Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (115 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode115Row
  lhs_eq := by simpa using t10j32HighBitTailNode115MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode115Row]


/-- State label for generated row 116. -/
def t10j32HighBitTailNode116Label : String :=
  "v2=7|odd=1|h=0"

/-- Destination support of generated row 116. -/
def t10j32HighBitTailNode116Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 53}

/-- Exact generated summand values for row 116. -/
noncomputable def t10j32HighBitTailNode116Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((82009 : NNReal) / (4 : NNReal))
  | 13 => ((10781945 : NNReal) / (1024 : NNReal))
  | 21 => ((1403499 : NNReal) / (64 : NNReal))
  | 53 => ((1107495 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 116. -/
def t10j32HighBitTailNode116LhsNum : Nat :=
  71952153

/-- Exact denominator of `(M v)_i` for generated row 116. -/
def t10j32HighBitTailNode116LhsDen : Nat :=
  1024

/-- Exact vector entry for generated row 116. -/
def t10j32HighBitTailNode116Vector : Nat :=
  2448779

/-- Exact cleared-denominator CW inequality for generated row 116. -/
theorem t10j32HighBitTailNode116Bound :
    t10j32HighBitTailNode116LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode116Vector * t10j32HighBitTailNode116LhsDen := by
  norm_num [t10j32HighBitTailNode116LhsNum, t10j32HighBitTailNode116LhsDen, t10j32HighBitTailNode116Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 116. -/
def t10j32HighBitTailNode116Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode116LhsNum
  lhsDen := t10j32HighBitTailNode116LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode116LhsDen]
  vector := t10j32HighBitTailNode116Vector
  vector_pos := by norm_num [t10j32HighBitTailNode116Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode116Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 116. -/
theorem t10j32HighBitTailNode116MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (116 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode116LhsNum : NNReal) / (t10j32HighBitTailNode116LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode116Support,
      t10j32HighBitTailMatrix (116 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (116 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode116Term (5 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (128 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode116Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode116Term]
    have h013 :
        t10j32HighBitTailMatrix (116 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode116Term (13 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (1024 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode116Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode116Term]
    have h021 :
        t10j32HighBitTailMatrix (116 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode116Term (21 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (64 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode116Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode116Term]
    have h053 :
        t10j32HighBitTailMatrix (116 : T10J32HighBitTailState) (53 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (53 : T10J32HighBitTailState) =
          t10j32HighBitTailNode116Term (53 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (128 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode116Term (53 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode116Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode116Support,
          t10j32HighBitTailMatrix (116 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode116Support, t10j32HighBitTailNode116Term dst := by
        simp [t10j32HighBitTailNode116Support, h005, h013, h021, h053]
      _ = (t10j32HighBitTailNode116LhsNum : NNReal) / (t10j32HighBitTailNode116LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode116Support, t10j32HighBitTailNode116Term]
        norm_num [t10j32HighBitTailNode116LhsNum, t10j32HighBitTailNode116LhsDen]

/-- Evaluated row certificate for generated row 116. -/
def t10j32HighBitTailNode116Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (116 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode116Row
  lhs_eq := by simpa using t10j32HighBitTailNode116MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode116Row]


/-- State label for generated row 117. -/
def t10j32HighBitTailNode117Label : String :=
  "v2=7|odd=1|h=1"

/-- Destination support of generated row 117. -/
def t10j32HighBitTailNode117Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 54}

/-- Exact generated summand values for row 117. -/
noncomputable def t10j32HighBitTailNode117Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((82009 : NNReal) / (4 : NNReal))
  | 14 => ((10781945 : NNReal) / (1024 : NNReal))
  | 22 => ((1403499 : NNReal) / (64 : NNReal))
  | 54 => ((1107495 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 117. -/
def t10j32HighBitTailNode117LhsNum : Nat :=
  71952153

/-- Exact denominator of `(M v)_i` for generated row 117. -/
def t10j32HighBitTailNode117LhsDen : Nat :=
  1024

/-- Exact vector entry for generated row 117. -/
def t10j32HighBitTailNode117Vector : Nat :=
  2448779

/-- Exact cleared-denominator CW inequality for generated row 117. -/
theorem t10j32HighBitTailNode117Bound :
    t10j32HighBitTailNode117LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode117Vector * t10j32HighBitTailNode117LhsDen := by
  norm_num [t10j32HighBitTailNode117LhsNum, t10j32HighBitTailNode117LhsDen, t10j32HighBitTailNode117Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 117. -/
def t10j32HighBitTailNode117Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode117LhsNum
  lhsDen := t10j32HighBitTailNode117LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode117LhsDen]
  vector := t10j32HighBitTailNode117Vector
  vector_pos := by norm_num [t10j32HighBitTailNode117Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode117Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 117. -/
theorem t10j32HighBitTailNode117MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (117 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode117LhsNum : NNReal) / (t10j32HighBitTailNode117LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode117Support,
      t10j32HighBitTailMatrix (117 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (117 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode117Term (6 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (128 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode117Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode117Term]
    have h014 :
        t10j32HighBitTailMatrix (117 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode117Term (14 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (1024 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode117Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode117Term]
    have h022 :
        t10j32HighBitTailMatrix (117 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode117Term (22 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (64 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode117Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode117Term]
    have h054 :
        t10j32HighBitTailMatrix (117 : T10J32HighBitTailState) (54 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (54 : T10J32HighBitTailState) =
          t10j32HighBitTailNode117Term (54 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (128 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode117Term (54 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode117Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode117Support,
          t10j32HighBitTailMatrix (117 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode117Support, t10j32HighBitTailNode117Term dst := by
        simp [t10j32HighBitTailNode117Support, h006, h014, h022, h054]
      _ = (t10j32HighBitTailNode117LhsNum : NNReal) / (t10j32HighBitTailNode117LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode117Support, t10j32HighBitTailNode117Term]
        norm_num [t10j32HighBitTailNode117LhsNum, t10j32HighBitTailNode117LhsDen]

/-- Evaluated row certificate for generated row 117. -/
def t10j32HighBitTailNode117Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (117 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode117Row
  lhs_eq := by simpa using t10j32HighBitTailNode117MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode117Row]


/-- State label for generated row 118. -/
def t10j32HighBitTailNode118Label : String :=
  "v2=7|odd=1|h=2"

/-- Destination support of generated row 118. -/
def t10j32HighBitTailNode118Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 55}

/-- Exact generated summand values for row 118. -/
noncomputable def t10j32HighBitTailNode118Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((82009 : NNReal) / (4 : NNReal))
  | 15 => ((10781945 : NNReal) / (1024 : NNReal))
  | 23 => ((1403499 : NNReal) / (64 : NNReal))
  | 55 => ((1107495 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 118. -/
def t10j32HighBitTailNode118LhsNum : Nat :=
  71952153

/-- Exact denominator of `(M v)_i` for generated row 118. -/
def t10j32HighBitTailNode118LhsDen : Nat :=
  1024

/-- Exact vector entry for generated row 118. -/
def t10j32HighBitTailNode118Vector : Nat :=
  2448779

/-- Exact cleared-denominator CW inequality for generated row 118. -/
theorem t10j32HighBitTailNode118Bound :
    t10j32HighBitTailNode118LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode118Vector * t10j32HighBitTailNode118LhsDen := by
  norm_num [t10j32HighBitTailNode118LhsNum, t10j32HighBitTailNode118LhsDen, t10j32HighBitTailNode118Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 118. -/
def t10j32HighBitTailNode118Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode118LhsNum
  lhsDen := t10j32HighBitTailNode118LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode118LhsDen]
  vector := t10j32HighBitTailNode118Vector
  vector_pos := by norm_num [t10j32HighBitTailNode118Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode118Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 118. -/
theorem t10j32HighBitTailNode118MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (118 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode118LhsNum : NNReal) / (t10j32HighBitTailNode118LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode118Support,
      t10j32HighBitTailMatrix (118 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (118 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode118Term (7 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (128 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode118Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode118Term]
    have h015 :
        t10j32HighBitTailMatrix (118 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode118Term (15 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (1024 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode118Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode118Term]
    have h023 :
        t10j32HighBitTailMatrix (118 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode118Term (23 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (64 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode118Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode118Term]
    have h055 :
        t10j32HighBitTailMatrix (118 : T10J32HighBitTailState) (55 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (55 : T10J32HighBitTailState) =
          t10j32HighBitTailNode118Term (55 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (128 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode118Term (55 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode118Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode118Support,
          t10j32HighBitTailMatrix (118 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode118Support, t10j32HighBitTailNode118Term dst := by
        simp [t10j32HighBitTailNode118Support, h007, h015, h023, h055]
      _ = (t10j32HighBitTailNode118LhsNum : NNReal) / (t10j32HighBitTailNode118LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode118Support, t10j32HighBitTailNode118Term]
        norm_num [t10j32HighBitTailNode118LhsNum, t10j32HighBitTailNode118LhsDen]

/-- Evaluated row certificate for generated row 118. -/
def t10j32HighBitTailNode118Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (118 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode118Row
  lhs_eq := by simpa using t10j32HighBitTailNode118MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode118Row]


/-- State label for generated row 119. -/
def t10j32HighBitTailNode119Label : String :=
  "v2=7|odd=1|h=3"

/-- Destination support of generated row 119. -/
def t10j32HighBitTailNode119Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 52}

/-- Exact generated summand values for row 119. -/
noncomputable def t10j32HighBitTailNode119Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((82009 : NNReal) / (4 : NNReal))
  | 12 => ((10781945 : NNReal) / (1024 : NNReal))
  | 20 => ((1403499 : NNReal) / (64 : NNReal))
  | 52 => ((1107495 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 119. -/
def t10j32HighBitTailNode119LhsNum : Nat :=
  71952153

/-- Exact denominator of `(M v)_i` for generated row 119. -/
def t10j32HighBitTailNode119LhsDen : Nat :=
  1024

/-- Exact vector entry for generated row 119. -/
def t10j32HighBitTailNode119Vector : Nat :=
  2448779

/-- Exact cleared-denominator CW inequality for generated row 119. -/
theorem t10j32HighBitTailNode119Bound :
    t10j32HighBitTailNode119LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode119Vector * t10j32HighBitTailNode119LhsDen := by
  norm_num [t10j32HighBitTailNode119LhsNum, t10j32HighBitTailNode119LhsDen, t10j32HighBitTailNode119Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 119. -/
def t10j32HighBitTailNode119Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode119LhsNum
  lhsDen := t10j32HighBitTailNode119LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode119LhsDen]
  vector := t10j32HighBitTailNode119Vector
  vector_pos := by norm_num [t10j32HighBitTailNode119Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode119Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 119. -/
theorem t10j32HighBitTailNode119MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (119 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode119LhsNum : NNReal) / (t10j32HighBitTailNode119LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode119Support,
      t10j32HighBitTailMatrix (119 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (119 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode119Term (4 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (128 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode119Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode119Term]
    have h012 :
        t10j32HighBitTailMatrix (119 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode119Term (12 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (1024 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode119Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode119Term]
    have h020 :
        t10j32HighBitTailMatrix (119 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode119Term (20 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (64 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode119Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode119Term]
    have h052 :
        t10j32HighBitTailMatrix (119 : T10J32HighBitTailState) (52 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (52 : T10J32HighBitTailState) =
          t10j32HighBitTailNode119Term (52 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (128 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode119Term (52 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode119Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode119Support,
          t10j32HighBitTailMatrix (119 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode119Support, t10j32HighBitTailNode119Term dst := by
        simp [t10j32HighBitTailNode119Support, h004, h012, h020, h052]
      _ = (t10j32HighBitTailNode119LhsNum : NNReal) / (t10j32HighBitTailNode119LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode119Support, t10j32HighBitTailNode119Term]
        norm_num [t10j32HighBitTailNode119LhsNum, t10j32HighBitTailNode119LhsDen]

/-- Evaluated row certificate for generated row 119. -/
def t10j32HighBitTailNode119Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (119 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode119Row
  lhs_eq := by simpa using t10j32HighBitTailNode119MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode119Row]


/-- State label for generated row 120. -/
def t10j32HighBitTailNode120Label : String :=
  "v2=7|odd=2|h=0"

/-- Destination support of generated row 120. -/
def t10j32HighBitTailNode120Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 120. -/
def t10j32HighBitTailNode120LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 120. -/
def t10j32HighBitTailNode120LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 120. -/
def t10j32HighBitTailNode120Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 120. -/
theorem t10j32HighBitTailNode120Bound :
    t10j32HighBitTailNode120LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode120Vector * t10j32HighBitTailNode120LhsDen := by
  norm_num [t10j32HighBitTailNode120LhsNum, t10j32HighBitTailNode120LhsDen, t10j32HighBitTailNode120Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 120. -/
def t10j32HighBitTailNode120Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode120LhsNum
  lhsDen := t10j32HighBitTailNode120LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode120LhsDen]
  vector := t10j32HighBitTailNode120Vector
  vector_pos := by norm_num [t10j32HighBitTailNode120Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode120Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 120. -/
theorem t10j32HighBitTailNode120MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (120 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode120LhsNum : NNReal) / (t10j32HighBitTailNode120LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode120LhsNum, t10j32HighBitTailNode120LhsDen]

/-- Evaluated row certificate for generated row 120. -/
def t10j32HighBitTailNode120Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (120 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode120Row
  lhs_eq := by simpa using t10j32HighBitTailNode120MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode120Row]


/-- State label for generated row 121. -/
def t10j32HighBitTailNode121Label : String :=
  "v2=7|odd=2|h=1"

/-- Destination support of generated row 121. -/
def t10j32HighBitTailNode121Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 121. -/
def t10j32HighBitTailNode121LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 121. -/
def t10j32HighBitTailNode121LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 121. -/
def t10j32HighBitTailNode121Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 121. -/
theorem t10j32HighBitTailNode121Bound :
    t10j32HighBitTailNode121LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode121Vector * t10j32HighBitTailNode121LhsDen := by
  norm_num [t10j32HighBitTailNode121LhsNum, t10j32HighBitTailNode121LhsDen, t10j32HighBitTailNode121Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 121. -/
def t10j32HighBitTailNode121Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode121LhsNum
  lhsDen := t10j32HighBitTailNode121LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode121LhsDen]
  vector := t10j32HighBitTailNode121Vector
  vector_pos := by norm_num [t10j32HighBitTailNode121Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode121Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 121. -/
theorem t10j32HighBitTailNode121MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (121 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode121LhsNum : NNReal) / (t10j32HighBitTailNode121LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode121LhsNum, t10j32HighBitTailNode121LhsDen]

/-- Evaluated row certificate for generated row 121. -/
def t10j32HighBitTailNode121Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (121 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode121Row
  lhs_eq := by simpa using t10j32HighBitTailNode121MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode121Row]


/-- State label for generated row 122. -/
def t10j32HighBitTailNode122Label : String :=
  "v2=7|odd=2|h=2"

/-- Destination support of generated row 122. -/
def t10j32HighBitTailNode122Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 122. -/
def t10j32HighBitTailNode122LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 122. -/
def t10j32HighBitTailNode122LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 122. -/
def t10j32HighBitTailNode122Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 122. -/
theorem t10j32HighBitTailNode122Bound :
    t10j32HighBitTailNode122LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode122Vector * t10j32HighBitTailNode122LhsDen := by
  norm_num [t10j32HighBitTailNode122LhsNum, t10j32HighBitTailNode122LhsDen, t10j32HighBitTailNode122Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 122. -/
def t10j32HighBitTailNode122Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode122LhsNum
  lhsDen := t10j32HighBitTailNode122LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode122LhsDen]
  vector := t10j32HighBitTailNode122Vector
  vector_pos := by norm_num [t10j32HighBitTailNode122Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode122Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 122. -/
theorem t10j32HighBitTailNode122MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (122 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode122LhsNum : NNReal) / (t10j32HighBitTailNode122LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode122LhsNum, t10j32HighBitTailNode122LhsDen]

/-- Evaluated row certificate for generated row 122. -/
def t10j32HighBitTailNode122Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (122 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode122Row
  lhs_eq := by simpa using t10j32HighBitTailNode122MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode122Row]


/-- State label for generated row 123. -/
def t10j32HighBitTailNode123Label : String :=
  "v2=7|odd=2|h=3"

/-- Destination support of generated row 123. -/
def t10j32HighBitTailNode123Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 123. -/
def t10j32HighBitTailNode123LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 123. -/
def t10j32HighBitTailNode123LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 123. -/
def t10j32HighBitTailNode123Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 123. -/
theorem t10j32HighBitTailNode123Bound :
    t10j32HighBitTailNode123LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode123Vector * t10j32HighBitTailNode123LhsDen := by
  norm_num [t10j32HighBitTailNode123LhsNum, t10j32HighBitTailNode123LhsDen, t10j32HighBitTailNode123Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 123. -/
def t10j32HighBitTailNode123Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode123LhsNum
  lhsDen := t10j32HighBitTailNode123LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode123LhsDen]
  vector := t10j32HighBitTailNode123Vector
  vector_pos := by norm_num [t10j32HighBitTailNode123Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode123Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 123. -/
theorem t10j32HighBitTailNode123MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (123 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode123LhsNum : NNReal) / (t10j32HighBitTailNode123LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode123LhsNum, t10j32HighBitTailNode123LhsDen]

/-- Evaluated row certificate for generated row 123. -/
def t10j32HighBitTailNode123Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (123 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode123Row
  lhs_eq := by simpa using t10j32HighBitTailNode123MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode123Row]


/-- State label for generated row 124. -/
def t10j32HighBitTailNode124Label : String :=
  "v2=7|odd=3|h=0"

/-- Destination support of generated row 124. -/
def t10j32HighBitTailNode124Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 37}

/-- Exact generated summand values for row 124. -/
noncomputable def t10j32HighBitTailNode124Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((82009 : NNReal) / (128 : NNReal))
  | 13 => ((28033057 : NNReal) / (1024 : NNReal))
  | 21 => ((1403499 : NNReal) / (512 : NNReal))
  | 29 => ((1918835 : NNReal) / (256 : NNReal))
  | 37 => ((1574319 : NNReal) / (256 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 124. -/
def t10j32HighBitTailNode124LhsNum : Nat :=
  45468743

/-- Exact denominator of `(M v)_i` for generated row 124. -/
def t10j32HighBitTailNode124LhsDen : Nat :=
  1024

/-- Exact vector entry for generated row 124. -/
def t10j32HighBitTailNode124Vector : Nat :=
  1915527

/-- Exact cleared-denominator CW inequality for generated row 124. -/
theorem t10j32HighBitTailNode124Bound :
    t10j32HighBitTailNode124LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode124Vector * t10j32HighBitTailNode124LhsDen := by
  norm_num [t10j32HighBitTailNode124LhsNum, t10j32HighBitTailNode124LhsDen, t10j32HighBitTailNode124Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 124. -/
def t10j32HighBitTailNode124Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode124LhsNum
  lhsDen := t10j32HighBitTailNode124LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode124LhsDen]
  vector := t10j32HighBitTailNode124Vector
  vector_pos := by norm_num [t10j32HighBitTailNode124Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode124Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 124. -/
theorem t10j32HighBitTailNode124MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (124 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode124LhsNum : NNReal) / (t10j32HighBitTailNode124LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode124Support,
      t10j32HighBitTailMatrix (124 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (124 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode124Term (5 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode124Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode124Term]
    have h013 :
        t10j32HighBitTailMatrix (124 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode124Term (13 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (1024 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode124Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode124Term]
    have h021 :
        t10j32HighBitTailMatrix (124 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode124Term (21 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (512 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode124Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode124Term]
    have h029 :
        t10j32HighBitTailMatrix (124 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode124Term (29 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode124Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode124Term]
    have h037 :
        t10j32HighBitTailMatrix (124 : T10J32HighBitTailState) (37 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (37 : T10J32HighBitTailState) =
          t10j32HighBitTailNode124Term (37 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode124Term (37 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode124Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode124Support,
          t10j32HighBitTailMatrix (124 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode124Support, t10j32HighBitTailNode124Term dst := by
        simp [t10j32HighBitTailNode124Support, h005, h013, h021, h029, h037]
      _ = (t10j32HighBitTailNode124LhsNum : NNReal) / (t10j32HighBitTailNode124LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode124Support, t10j32HighBitTailNode124Term]
        norm_num [t10j32HighBitTailNode124LhsNum, t10j32HighBitTailNode124LhsDen]

/-- Evaluated row certificate for generated row 124. -/
def t10j32HighBitTailNode124Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (124 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode124Row
  lhs_eq := by simpa using t10j32HighBitTailNode124MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode124Row]


/-- State label for generated row 125. -/
def t10j32HighBitTailNode125Label : String :=
  "v2=7|odd=3|h=1"

/-- Destination support of generated row 125. -/
def t10j32HighBitTailNode125Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 38}

/-- Exact generated summand values for row 125. -/
noncomputable def t10j32HighBitTailNode125Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((82009 : NNReal) / (128 : NNReal))
  | 14 => ((28033057 : NNReal) / (1024 : NNReal))
  | 22 => ((1403499 : NNReal) / (512 : NNReal))
  | 30 => ((1918835 : NNReal) / (256 : NNReal))
  | 38 => ((1574319 : NNReal) / (256 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 125. -/
def t10j32HighBitTailNode125LhsNum : Nat :=
  45468743

/-- Exact denominator of `(M v)_i` for generated row 125. -/
def t10j32HighBitTailNode125LhsDen : Nat :=
  1024

/-- Exact vector entry for generated row 125. -/
def t10j32HighBitTailNode125Vector : Nat :=
  1915527

/-- Exact cleared-denominator CW inequality for generated row 125. -/
theorem t10j32HighBitTailNode125Bound :
    t10j32HighBitTailNode125LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode125Vector * t10j32HighBitTailNode125LhsDen := by
  norm_num [t10j32HighBitTailNode125LhsNum, t10j32HighBitTailNode125LhsDen, t10j32HighBitTailNode125Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 125. -/
def t10j32HighBitTailNode125Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode125LhsNum
  lhsDen := t10j32HighBitTailNode125LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode125LhsDen]
  vector := t10j32HighBitTailNode125Vector
  vector_pos := by norm_num [t10j32HighBitTailNode125Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode125Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 125. -/
theorem t10j32HighBitTailNode125MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (125 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode125LhsNum : NNReal) / (t10j32HighBitTailNode125LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode125Support,
      t10j32HighBitTailMatrix (125 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (125 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode125Term (6 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode125Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode125Term]
    have h014 :
        t10j32HighBitTailMatrix (125 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode125Term (14 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (1024 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode125Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode125Term]
    have h022 :
        t10j32HighBitTailMatrix (125 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode125Term (22 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (512 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode125Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode125Term]
    have h030 :
        t10j32HighBitTailMatrix (125 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode125Term (30 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode125Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode125Term]
    have h038 :
        t10j32HighBitTailMatrix (125 : T10J32HighBitTailState) (38 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (38 : T10J32HighBitTailState) =
          t10j32HighBitTailNode125Term (38 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode125Term (38 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode125Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode125Support,
          t10j32HighBitTailMatrix (125 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode125Support, t10j32HighBitTailNode125Term dst := by
        simp [t10j32HighBitTailNode125Support, h006, h014, h022, h030, h038]
      _ = (t10j32HighBitTailNode125LhsNum : NNReal) / (t10j32HighBitTailNode125LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode125Support, t10j32HighBitTailNode125Term]
        norm_num [t10j32HighBitTailNode125LhsNum, t10j32HighBitTailNode125LhsDen]

/-- Evaluated row certificate for generated row 125. -/
def t10j32HighBitTailNode125Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (125 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode125Row
  lhs_eq := by simpa using t10j32HighBitTailNode125MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode125Row]


/-- State label for generated row 126. -/
def t10j32HighBitTailNode126Label : String :=
  "v2=7|odd=3|h=2"

/-- Destination support of generated row 126. -/
def t10j32HighBitTailNode126Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 39}

/-- Exact generated summand values for row 126. -/
noncomputable def t10j32HighBitTailNode126Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((82009 : NNReal) / (128 : NNReal))
  | 15 => ((28033057 : NNReal) / (1024 : NNReal))
  | 23 => ((1403499 : NNReal) / (512 : NNReal))
  | 31 => ((1918835 : NNReal) / (256 : NNReal))
  | 39 => ((1574319 : NNReal) / (256 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 126. -/
def t10j32HighBitTailNode126LhsNum : Nat :=
  45468743

/-- Exact denominator of `(M v)_i` for generated row 126. -/
def t10j32HighBitTailNode126LhsDen : Nat :=
  1024

/-- Exact vector entry for generated row 126. -/
def t10j32HighBitTailNode126Vector : Nat :=
  1915527

/-- Exact cleared-denominator CW inequality for generated row 126. -/
theorem t10j32HighBitTailNode126Bound :
    t10j32HighBitTailNode126LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode126Vector * t10j32HighBitTailNode126LhsDen := by
  norm_num [t10j32HighBitTailNode126LhsNum, t10j32HighBitTailNode126LhsDen, t10j32HighBitTailNode126Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 126. -/
def t10j32HighBitTailNode126Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode126LhsNum
  lhsDen := t10j32HighBitTailNode126LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode126LhsDen]
  vector := t10j32HighBitTailNode126Vector
  vector_pos := by norm_num [t10j32HighBitTailNode126Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode126Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 126. -/
theorem t10j32HighBitTailNode126MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (126 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode126LhsNum : NNReal) / (t10j32HighBitTailNode126LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode126Support,
      t10j32HighBitTailMatrix (126 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (126 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode126Term (7 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode126Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode126Term]
    have h015 :
        t10j32HighBitTailMatrix (126 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode126Term (15 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (1024 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode126Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode126Term]
    have h023 :
        t10j32HighBitTailMatrix (126 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode126Term (23 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (512 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode126Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode126Term]
    have h031 :
        t10j32HighBitTailMatrix (126 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode126Term (31 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode126Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode126Term]
    have h039 :
        t10j32HighBitTailMatrix (126 : T10J32HighBitTailState) (39 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (39 : T10J32HighBitTailState) =
          t10j32HighBitTailNode126Term (39 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode126Term (39 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode126Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode126Support,
          t10j32HighBitTailMatrix (126 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode126Support, t10j32HighBitTailNode126Term dst := by
        simp [t10j32HighBitTailNode126Support, h007, h015, h023, h031, h039]
      _ = (t10j32HighBitTailNode126LhsNum : NNReal) / (t10j32HighBitTailNode126LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode126Support, t10j32HighBitTailNode126Term]
        norm_num [t10j32HighBitTailNode126LhsNum, t10j32HighBitTailNode126LhsDen]

/-- Evaluated row certificate for generated row 126. -/
def t10j32HighBitTailNode126Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (126 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode126Row
  lhs_eq := by simpa using t10j32HighBitTailNode126MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode126Row]


/-- State label for generated row 127. -/
def t10j32HighBitTailNode127Label : String :=
  "v2=7|odd=3|h=3"

/-- Destination support of generated row 127. -/
def t10j32HighBitTailNode127Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 36}

/-- Exact generated summand values for row 127. -/
noncomputable def t10j32HighBitTailNode127Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((82009 : NNReal) / (128 : NNReal))
  | 12 => ((28033057 : NNReal) / (1024 : NNReal))
  | 20 => ((1403499 : NNReal) / (512 : NNReal))
  | 28 => ((1918835 : NNReal) / (256 : NNReal))
  | 36 => ((1574319 : NNReal) / (256 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 127. -/
def t10j32HighBitTailNode127LhsNum : Nat :=
  45468743

/-- Exact denominator of `(M v)_i` for generated row 127. -/
def t10j32HighBitTailNode127LhsDen : Nat :=
  1024

/-- Exact vector entry for generated row 127. -/
def t10j32HighBitTailNode127Vector : Nat :=
  1915527

/-- Exact cleared-denominator CW inequality for generated row 127. -/
theorem t10j32HighBitTailNode127Bound :
    t10j32HighBitTailNode127LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode127Vector * t10j32HighBitTailNode127LhsDen := by
  norm_num [t10j32HighBitTailNode127LhsNum, t10j32HighBitTailNode127LhsDen, t10j32HighBitTailNode127Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 127. -/
def t10j32HighBitTailNode127Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode127LhsNum
  lhsDen := t10j32HighBitTailNode127LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode127LhsDen]
  vector := t10j32HighBitTailNode127Vector
  vector_pos := by norm_num [t10j32HighBitTailNode127Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode127Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 127. -/
theorem t10j32HighBitTailNode127MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (127 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode127LhsNum : NNReal) / (t10j32HighBitTailNode127LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode127Support,
      t10j32HighBitTailMatrix (127 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (127 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode127Term (4 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode127Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode127Term]
    have h012 :
        t10j32HighBitTailMatrix (127 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode127Term (12 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (1024 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode127Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode127Term]
    have h020 :
        t10j32HighBitTailMatrix (127 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode127Term (20 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (512 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode127Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode127Term]
    have h028 :
        t10j32HighBitTailMatrix (127 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode127Term (28 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode127Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode127Term]
    have h036 :
        t10j32HighBitTailMatrix (127 : T10J32HighBitTailState) (36 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (36 : T10J32HighBitTailState) =
          t10j32HighBitTailNode127Term (36 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode127Term (36 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode127Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode127Support,
          t10j32HighBitTailMatrix (127 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode127Support, t10j32HighBitTailNode127Term dst := by
        simp [t10j32HighBitTailNode127Support, h004, h012, h020, h028, h036]
      _ = (t10j32HighBitTailNode127LhsNum : NNReal) / (t10j32HighBitTailNode127LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode127Support, t10j32HighBitTailNode127Term]
        norm_num [t10j32HighBitTailNode127LhsNum, t10j32HighBitTailNode127LhsDen]

/-- Evaluated row certificate for generated row 127. -/
def t10j32HighBitTailNode127Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (127 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode127Row
  lhs_eq := by simpa using t10j32HighBitTailNode127MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode127Row]

end Generated
end CollatzShadowing
