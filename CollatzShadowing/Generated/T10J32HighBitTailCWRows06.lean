import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 96. -/
def t10j32HighBitTailNode096Label : String :=
  "v2=6|odd=0|h=0"

/-- Destination support of generated row 96. -/
def t10j32HighBitTailNode096Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 96. -/
def t10j32HighBitTailNode096LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 96. -/
def t10j32HighBitTailNode096LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 96. -/
def t10j32HighBitTailNode096Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 96. -/
theorem t10j32HighBitTailNode096Bound :
    t10j32HighBitTailNode096LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode096Vector * t10j32HighBitTailNode096LhsDen := by
  norm_num [t10j32HighBitTailNode096LhsNum, t10j32HighBitTailNode096LhsDen, t10j32HighBitTailNode096Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 96. -/
def t10j32HighBitTailNode096Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode096LhsNum
  lhsDen := t10j32HighBitTailNode096LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode096LhsDen]
  vector := t10j32HighBitTailNode096Vector
  vector_pos := by norm_num [t10j32HighBitTailNode096Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode096Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 96. -/
theorem t10j32HighBitTailNode096MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (96 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode096LhsNum : NNReal) / (t10j32HighBitTailNode096LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode096LhsNum, t10j32HighBitTailNode096LhsDen]

/-- Evaluated row certificate for generated row 96. -/
def t10j32HighBitTailNode096Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (96 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode096Row
  lhs_eq := by simpa using t10j32HighBitTailNode096MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode096Row]


/-- State label for generated row 97. -/
def t10j32HighBitTailNode097Label : String :=
  "v2=6|odd=0|h=1"

/-- Destination support of generated row 97. -/
def t10j32HighBitTailNode097Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 97. -/
def t10j32HighBitTailNode097LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 97. -/
def t10j32HighBitTailNode097LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 97. -/
def t10j32HighBitTailNode097Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 97. -/
theorem t10j32HighBitTailNode097Bound :
    t10j32HighBitTailNode097LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode097Vector * t10j32HighBitTailNode097LhsDen := by
  norm_num [t10j32HighBitTailNode097LhsNum, t10j32HighBitTailNode097LhsDen, t10j32HighBitTailNode097Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 97. -/
def t10j32HighBitTailNode097Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode097LhsNum
  lhsDen := t10j32HighBitTailNode097LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode097LhsDen]
  vector := t10j32HighBitTailNode097Vector
  vector_pos := by norm_num [t10j32HighBitTailNode097Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode097Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 97. -/
theorem t10j32HighBitTailNode097MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (97 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode097LhsNum : NNReal) / (t10j32HighBitTailNode097LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode097LhsNum, t10j32HighBitTailNode097LhsDen]

/-- Evaluated row certificate for generated row 97. -/
def t10j32HighBitTailNode097Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (97 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode097Row
  lhs_eq := by simpa using t10j32HighBitTailNode097MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode097Row]


/-- State label for generated row 98. -/
def t10j32HighBitTailNode098Label : String :=
  "v2=6|odd=0|h=2"

/-- Destination support of generated row 98. -/
def t10j32HighBitTailNode098Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 98. -/
def t10j32HighBitTailNode098LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 98. -/
def t10j32HighBitTailNode098LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 98. -/
def t10j32HighBitTailNode098Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 98. -/
theorem t10j32HighBitTailNode098Bound :
    t10j32HighBitTailNode098LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode098Vector * t10j32HighBitTailNode098LhsDen := by
  norm_num [t10j32HighBitTailNode098LhsNum, t10j32HighBitTailNode098LhsDen, t10j32HighBitTailNode098Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 98. -/
def t10j32HighBitTailNode098Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode098LhsNum
  lhsDen := t10j32HighBitTailNode098LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode098LhsDen]
  vector := t10j32HighBitTailNode098Vector
  vector_pos := by norm_num [t10j32HighBitTailNode098Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode098Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 98. -/
theorem t10j32HighBitTailNode098MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (98 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode098LhsNum : NNReal) / (t10j32HighBitTailNode098LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode098LhsNum, t10j32HighBitTailNode098LhsDen]

/-- Evaluated row certificate for generated row 98. -/
def t10j32HighBitTailNode098Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (98 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode098Row
  lhs_eq := by simpa using t10j32HighBitTailNode098MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode098Row]


/-- State label for generated row 99. -/
def t10j32HighBitTailNode099Label : String :=
  "v2=6|odd=0|h=3"

/-- Destination support of generated row 99. -/
def t10j32HighBitTailNode099Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 99. -/
def t10j32HighBitTailNode099LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 99. -/
def t10j32HighBitTailNode099LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 99. -/
def t10j32HighBitTailNode099Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 99. -/
theorem t10j32HighBitTailNode099Bound :
    t10j32HighBitTailNode099LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode099Vector * t10j32HighBitTailNode099LhsDen := by
  norm_num [t10j32HighBitTailNode099LhsNum, t10j32HighBitTailNode099LhsDen, t10j32HighBitTailNode099Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 99. -/
def t10j32HighBitTailNode099Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode099LhsNum
  lhsDen := t10j32HighBitTailNode099LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode099LhsDen]
  vector := t10j32HighBitTailNode099Vector
  vector_pos := by norm_num [t10j32HighBitTailNode099Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode099Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 99. -/
theorem t10j32HighBitTailNode099MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (99 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode099LhsNum : NNReal) / (t10j32HighBitTailNode099LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode099LhsNum, t10j32HighBitTailNode099LhsDen]

/-- Evaluated row certificate for generated row 99. -/
def t10j32HighBitTailNode099Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (99 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode099Row
  lhs_eq := by simpa using t10j32HighBitTailNode099MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode099Row]


/-- State label for generated row 100. -/
def t10j32HighBitTailNode100Label : String :=
  "v2=6|odd=1|h=0"

/-- Destination support of generated row 100. -/
def t10j32HighBitTailNode100Support : Finset T10J32HighBitTailState :=
  {13, 29, 61}

/-- Exact generated summand values for row 100. -/
noncomputable def t10j32HighBitTailNode100Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 13 => ((15094723 : NNReal) / (512 : NNReal))
  | 29 => ((1918835 : NNReal) / (256 : NNReal))
  | 61 => ((958247 : NNReal) / (128 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 100. -/
def t10j32HighBitTailNode100LhsNum : Nat :=
  22765381

/-- Exact denominator of `(M v)_i` for generated row 100. -/
def t10j32HighBitTailNode100LhsDen : Nat :=
  512

/-- Exact vector entry for generated row 100. -/
def t10j32HighBitTailNode100Vector : Nat :=
  1916776

/-- Exact cleared-denominator CW inequality for generated row 100. -/
theorem t10j32HighBitTailNode100Bound :
    t10j32HighBitTailNode100LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode100Vector * t10j32HighBitTailNode100LhsDen := by
  norm_num [t10j32HighBitTailNode100LhsNum, t10j32HighBitTailNode100LhsDen, t10j32HighBitTailNode100Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 100. -/
def t10j32HighBitTailNode100Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode100LhsNum
  lhsDen := t10j32HighBitTailNode100LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode100LhsDen]
  vector := t10j32HighBitTailNode100Vector
  vector_pos := by norm_num [t10j32HighBitTailNode100Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode100Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 100. -/
theorem t10j32HighBitTailNode100MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (100 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode100LhsNum : NNReal) / (t10j32HighBitTailNode100LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode100Support,
      t10j32HighBitTailMatrix (100 : T10J32HighBitTailState) dst *
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
    have h013 :
        t10j32HighBitTailMatrix (100 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode100Term (13 : T10J32HighBitTailState) := by
      change (((7 : NNReal) / (512 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode100Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode100Term]
    have h029 :
        t10j32HighBitTailMatrix (100 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode100Term (29 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode100Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode100Term]
    have h061 :
        t10j32HighBitTailMatrix (100 : T10J32HighBitTailState) (61 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (61 : T10J32HighBitTailState) =
          t10j32HighBitTailNode100Term (61 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode100Term (61 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode100Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode100Support,
          t10j32HighBitTailMatrix (100 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode100Support, t10j32HighBitTailNode100Term dst := by
        simp [t10j32HighBitTailNode100Support, h013, h029, h061]
      _ = (t10j32HighBitTailNode100LhsNum : NNReal) / (t10j32HighBitTailNode100LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode100Support, t10j32HighBitTailNode100Term]
        norm_num [t10j32HighBitTailNode100LhsNum, t10j32HighBitTailNode100LhsDen]

/-- Evaluated row certificate for generated row 100. -/
def t10j32HighBitTailNode100Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (100 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode100Row
  lhs_eq := by simpa using t10j32HighBitTailNode100MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode100Row]


/-- State label for generated row 101. -/
def t10j32HighBitTailNode101Label : String :=
  "v2=6|odd=1|h=1"

/-- Destination support of generated row 101. -/
def t10j32HighBitTailNode101Support : Finset T10J32HighBitTailState :=
  {14, 30, 62}

/-- Exact generated summand values for row 101. -/
noncomputable def t10j32HighBitTailNode101Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 14 => ((15094723 : NNReal) / (512 : NNReal))
  | 30 => ((1918835 : NNReal) / (256 : NNReal))
  | 62 => ((958247 : NNReal) / (128 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 101. -/
def t10j32HighBitTailNode101LhsNum : Nat :=
  22765381

/-- Exact denominator of `(M v)_i` for generated row 101. -/
def t10j32HighBitTailNode101LhsDen : Nat :=
  512

/-- Exact vector entry for generated row 101. -/
def t10j32HighBitTailNode101Vector : Nat :=
  1916776

/-- Exact cleared-denominator CW inequality for generated row 101. -/
theorem t10j32HighBitTailNode101Bound :
    t10j32HighBitTailNode101LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode101Vector * t10j32HighBitTailNode101LhsDen := by
  norm_num [t10j32HighBitTailNode101LhsNum, t10j32HighBitTailNode101LhsDen, t10j32HighBitTailNode101Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 101. -/
def t10j32HighBitTailNode101Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode101LhsNum
  lhsDen := t10j32HighBitTailNode101LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode101LhsDen]
  vector := t10j32HighBitTailNode101Vector
  vector_pos := by norm_num [t10j32HighBitTailNode101Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode101Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 101. -/
theorem t10j32HighBitTailNode101MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (101 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode101LhsNum : NNReal) / (t10j32HighBitTailNode101LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode101Support,
      t10j32HighBitTailMatrix (101 : T10J32HighBitTailState) dst *
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
    have h014 :
        t10j32HighBitTailMatrix (101 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode101Term (14 : T10J32HighBitTailState) := by
      change (((7 : NNReal) / (512 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode101Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode101Term]
    have h030 :
        t10j32HighBitTailMatrix (101 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode101Term (30 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode101Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode101Term]
    have h062 :
        t10j32HighBitTailMatrix (101 : T10J32HighBitTailState) (62 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (62 : T10J32HighBitTailState) =
          t10j32HighBitTailNode101Term (62 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode101Term (62 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode101Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode101Support,
          t10j32HighBitTailMatrix (101 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode101Support, t10j32HighBitTailNode101Term dst := by
        simp [t10j32HighBitTailNode101Support, h014, h030, h062]
      _ = (t10j32HighBitTailNode101LhsNum : NNReal) / (t10j32HighBitTailNode101LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode101Support, t10j32HighBitTailNode101Term]
        norm_num [t10j32HighBitTailNode101LhsNum, t10j32HighBitTailNode101LhsDen]

/-- Evaluated row certificate for generated row 101. -/
def t10j32HighBitTailNode101Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (101 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode101Row
  lhs_eq := by simpa using t10j32HighBitTailNode101MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode101Row]


/-- State label for generated row 102. -/
def t10j32HighBitTailNode102Label : String :=
  "v2=6|odd=1|h=2"

/-- Destination support of generated row 102. -/
def t10j32HighBitTailNode102Support : Finset T10J32HighBitTailState :=
  {15, 31, 63}

/-- Exact generated summand values for row 102. -/
noncomputable def t10j32HighBitTailNode102Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 15 => ((15094723 : NNReal) / (512 : NNReal))
  | 31 => ((1918835 : NNReal) / (256 : NNReal))
  | 63 => ((958247 : NNReal) / (128 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 102. -/
def t10j32HighBitTailNode102LhsNum : Nat :=
  22765381

/-- Exact denominator of `(M v)_i` for generated row 102. -/
def t10j32HighBitTailNode102LhsDen : Nat :=
  512

/-- Exact vector entry for generated row 102. -/
def t10j32HighBitTailNode102Vector : Nat :=
  1916776

/-- Exact cleared-denominator CW inequality for generated row 102. -/
theorem t10j32HighBitTailNode102Bound :
    t10j32HighBitTailNode102LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode102Vector * t10j32HighBitTailNode102LhsDen := by
  norm_num [t10j32HighBitTailNode102LhsNum, t10j32HighBitTailNode102LhsDen, t10j32HighBitTailNode102Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 102. -/
def t10j32HighBitTailNode102Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode102LhsNum
  lhsDen := t10j32HighBitTailNode102LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode102LhsDen]
  vector := t10j32HighBitTailNode102Vector
  vector_pos := by norm_num [t10j32HighBitTailNode102Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode102Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 102. -/
theorem t10j32HighBitTailNode102MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (102 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode102LhsNum : NNReal) / (t10j32HighBitTailNode102LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode102Support,
      t10j32HighBitTailMatrix (102 : T10J32HighBitTailState) dst *
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
    have h015 :
        t10j32HighBitTailMatrix (102 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode102Term (15 : T10J32HighBitTailState) := by
      change (((7 : NNReal) / (512 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode102Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode102Term]
    have h031 :
        t10j32HighBitTailMatrix (102 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode102Term (31 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode102Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode102Term]
    have h063 :
        t10j32HighBitTailMatrix (102 : T10J32HighBitTailState) (63 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (63 : T10J32HighBitTailState) =
          t10j32HighBitTailNode102Term (63 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode102Term (63 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode102Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode102Support,
          t10j32HighBitTailMatrix (102 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode102Support, t10j32HighBitTailNode102Term dst := by
        simp [t10j32HighBitTailNode102Support, h015, h031, h063]
      _ = (t10j32HighBitTailNode102LhsNum : NNReal) / (t10j32HighBitTailNode102LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode102Support, t10j32HighBitTailNode102Term]
        norm_num [t10j32HighBitTailNode102LhsNum, t10j32HighBitTailNode102LhsDen]

/-- Evaluated row certificate for generated row 102. -/
def t10j32HighBitTailNode102Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (102 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode102Row
  lhs_eq := by simpa using t10j32HighBitTailNode102MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode102Row]


/-- State label for generated row 103. -/
def t10j32HighBitTailNode103Label : String :=
  "v2=6|odd=1|h=3"

/-- Destination support of generated row 103. -/
def t10j32HighBitTailNode103Support : Finset T10J32HighBitTailState :=
  {12, 28, 60}

/-- Exact generated summand values for row 103. -/
noncomputable def t10j32HighBitTailNode103Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 12 => ((15094723 : NNReal) / (512 : NNReal))
  | 28 => ((1918835 : NNReal) / (256 : NNReal))
  | 60 => ((958247 : NNReal) / (128 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 103. -/
def t10j32HighBitTailNode103LhsNum : Nat :=
  22765381

/-- Exact denominator of `(M v)_i` for generated row 103. -/
def t10j32HighBitTailNode103LhsDen : Nat :=
  512

/-- Exact vector entry for generated row 103. -/
def t10j32HighBitTailNode103Vector : Nat :=
  1916776

/-- Exact cleared-denominator CW inequality for generated row 103. -/
theorem t10j32HighBitTailNode103Bound :
    t10j32HighBitTailNode103LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode103Vector * t10j32HighBitTailNode103LhsDen := by
  norm_num [t10j32HighBitTailNode103LhsNum, t10j32HighBitTailNode103LhsDen, t10j32HighBitTailNode103Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 103. -/
def t10j32HighBitTailNode103Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode103LhsNum
  lhsDen := t10j32HighBitTailNode103LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode103LhsDen]
  vector := t10j32HighBitTailNode103Vector
  vector_pos := by norm_num [t10j32HighBitTailNode103Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode103Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 103. -/
theorem t10j32HighBitTailNode103MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (103 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode103LhsNum : NNReal) / (t10j32HighBitTailNode103LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode103Support,
      t10j32HighBitTailMatrix (103 : T10J32HighBitTailState) dst *
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
    have h012 :
        t10j32HighBitTailMatrix (103 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode103Term (12 : T10J32HighBitTailState) := by
      change (((7 : NNReal) / (512 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode103Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode103Term]
    have h028 :
        t10j32HighBitTailMatrix (103 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode103Term (28 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode103Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode103Term]
    have h060 :
        t10j32HighBitTailMatrix (103 : T10J32HighBitTailState) (60 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (60 : T10J32HighBitTailState) =
          t10j32HighBitTailNode103Term (60 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (256 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode103Term (60 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode103Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode103Support,
          t10j32HighBitTailMatrix (103 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode103Support, t10j32HighBitTailNode103Term dst := by
        simp [t10j32HighBitTailNode103Support, h012, h028, h060]
      _ = (t10j32HighBitTailNode103LhsNum : NNReal) / (t10j32HighBitTailNode103LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode103Support, t10j32HighBitTailNode103Term]
        norm_num [t10j32HighBitTailNode103LhsNum, t10j32HighBitTailNode103LhsDen]

/-- Evaluated row certificate for generated row 103. -/
def t10j32HighBitTailNode103Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (103 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode103Row
  lhs_eq := by simpa using t10j32HighBitTailNode103MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode103Row]


/-- State label for generated row 104. -/
def t10j32HighBitTailNode104Label : String :=
  "v2=6|odd=2|h=0"

/-- Destination support of generated row 104. -/
def t10j32HighBitTailNode104Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 104. -/
def t10j32HighBitTailNode104LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 104. -/
def t10j32HighBitTailNode104LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 104. -/
def t10j32HighBitTailNode104Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 104. -/
theorem t10j32HighBitTailNode104Bound :
    t10j32HighBitTailNode104LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode104Vector * t10j32HighBitTailNode104LhsDen := by
  norm_num [t10j32HighBitTailNode104LhsNum, t10j32HighBitTailNode104LhsDen, t10j32HighBitTailNode104Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 104. -/
def t10j32HighBitTailNode104Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode104LhsNum
  lhsDen := t10j32HighBitTailNode104LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode104LhsDen]
  vector := t10j32HighBitTailNode104Vector
  vector_pos := by norm_num [t10j32HighBitTailNode104Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode104Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 104. -/
theorem t10j32HighBitTailNode104MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (104 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode104LhsNum : NNReal) / (t10j32HighBitTailNode104LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode104LhsNum, t10j32HighBitTailNode104LhsDen]

/-- Evaluated row certificate for generated row 104. -/
def t10j32HighBitTailNode104Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (104 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode104Row
  lhs_eq := by simpa using t10j32HighBitTailNode104MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode104Row]


/-- State label for generated row 105. -/
def t10j32HighBitTailNode105Label : String :=
  "v2=6|odd=2|h=1"

/-- Destination support of generated row 105. -/
def t10j32HighBitTailNode105Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 105. -/
def t10j32HighBitTailNode105LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 105. -/
def t10j32HighBitTailNode105LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 105. -/
def t10j32HighBitTailNode105Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 105. -/
theorem t10j32HighBitTailNode105Bound :
    t10j32HighBitTailNode105LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode105Vector * t10j32HighBitTailNode105LhsDen := by
  norm_num [t10j32HighBitTailNode105LhsNum, t10j32HighBitTailNode105LhsDen, t10j32HighBitTailNode105Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 105. -/
def t10j32HighBitTailNode105Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode105LhsNum
  lhsDen := t10j32HighBitTailNode105LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode105LhsDen]
  vector := t10j32HighBitTailNode105Vector
  vector_pos := by norm_num [t10j32HighBitTailNode105Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode105Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 105. -/
theorem t10j32HighBitTailNode105MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (105 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode105LhsNum : NNReal) / (t10j32HighBitTailNode105LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode105LhsNum, t10j32HighBitTailNode105LhsDen]

/-- Evaluated row certificate for generated row 105. -/
def t10j32HighBitTailNode105Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (105 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode105Row
  lhs_eq := by simpa using t10j32HighBitTailNode105MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode105Row]


/-- State label for generated row 106. -/
def t10j32HighBitTailNode106Label : String :=
  "v2=6|odd=2|h=2"

/-- Destination support of generated row 106. -/
def t10j32HighBitTailNode106Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 106. -/
def t10j32HighBitTailNode106LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 106. -/
def t10j32HighBitTailNode106LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 106. -/
def t10j32HighBitTailNode106Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 106. -/
theorem t10j32HighBitTailNode106Bound :
    t10j32HighBitTailNode106LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode106Vector * t10j32HighBitTailNode106LhsDen := by
  norm_num [t10j32HighBitTailNode106LhsNum, t10j32HighBitTailNode106LhsDen, t10j32HighBitTailNode106Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 106. -/
def t10j32HighBitTailNode106Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode106LhsNum
  lhsDen := t10j32HighBitTailNode106LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode106LhsDen]
  vector := t10j32HighBitTailNode106Vector
  vector_pos := by norm_num [t10j32HighBitTailNode106Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode106Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 106. -/
theorem t10j32HighBitTailNode106MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (106 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode106LhsNum : NNReal) / (t10j32HighBitTailNode106LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode106LhsNum, t10j32HighBitTailNode106LhsDen]

/-- Evaluated row certificate for generated row 106. -/
def t10j32HighBitTailNode106Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (106 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode106Row
  lhs_eq := by simpa using t10j32HighBitTailNode106MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode106Row]


/-- State label for generated row 107. -/
def t10j32HighBitTailNode107Label : String :=
  "v2=6|odd=2|h=3"

/-- Destination support of generated row 107. -/
def t10j32HighBitTailNode107Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 107. -/
def t10j32HighBitTailNode107LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 107. -/
def t10j32HighBitTailNode107LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 107. -/
def t10j32HighBitTailNode107Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 107. -/
theorem t10j32HighBitTailNode107Bound :
    t10j32HighBitTailNode107LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode107Vector * t10j32HighBitTailNode107LhsDen := by
  norm_num [t10j32HighBitTailNode107LhsNum, t10j32HighBitTailNode107LhsDen, t10j32HighBitTailNode107Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 107. -/
def t10j32HighBitTailNode107Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode107LhsNum
  lhsDen := t10j32HighBitTailNode107LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode107LhsDen]
  vector := t10j32HighBitTailNode107Vector
  vector_pos := by norm_num [t10j32HighBitTailNode107Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode107Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 107. -/
theorem t10j32HighBitTailNode107MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (107 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode107LhsNum : NNReal) / (t10j32HighBitTailNode107LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode107LhsNum, t10j32HighBitTailNode107LhsDen]

/-- Evaluated row certificate for generated row 107. -/
def t10j32HighBitTailNode107Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (107 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode107Row
  lhs_eq := by simpa using t10j32HighBitTailNode107MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode107Row]


/-- State label for generated row 108. -/
def t10j32HighBitTailNode108Label : String :=
  "v2=6|odd=3|h=0"

/-- Destination support of generated row 108. -/
def t10j32HighBitTailNode108Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 108. -/
def t10j32HighBitTailNode108LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 108. -/
def t10j32HighBitTailNode108LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 108. -/
def t10j32HighBitTailNode108Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 108. -/
theorem t10j32HighBitTailNode108Bound :
    t10j32HighBitTailNode108LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode108Vector * t10j32HighBitTailNode108LhsDen := by
  norm_num [t10j32HighBitTailNode108LhsNum, t10j32HighBitTailNode108LhsDen, t10j32HighBitTailNode108Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 108. -/
def t10j32HighBitTailNode108Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode108LhsNum
  lhsDen := t10j32HighBitTailNode108LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode108LhsDen]
  vector := t10j32HighBitTailNode108Vector
  vector_pos := by norm_num [t10j32HighBitTailNode108Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode108Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 108. -/
theorem t10j32HighBitTailNode108MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (108 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode108LhsNum : NNReal) / (t10j32HighBitTailNode108LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode108LhsNum, t10j32HighBitTailNode108LhsDen]

/-- Evaluated row certificate for generated row 108. -/
def t10j32HighBitTailNode108Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (108 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode108Row
  lhs_eq := by simpa using t10j32HighBitTailNode108MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode108Row]


/-- State label for generated row 109. -/
def t10j32HighBitTailNode109Label : String :=
  "v2=6|odd=3|h=1"

/-- Destination support of generated row 109. -/
def t10j32HighBitTailNode109Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 109. -/
def t10j32HighBitTailNode109LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 109. -/
def t10j32HighBitTailNode109LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 109. -/
def t10j32HighBitTailNode109Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 109. -/
theorem t10j32HighBitTailNode109Bound :
    t10j32HighBitTailNode109LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode109Vector * t10j32HighBitTailNode109LhsDen := by
  norm_num [t10j32HighBitTailNode109LhsNum, t10j32HighBitTailNode109LhsDen, t10j32HighBitTailNode109Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 109. -/
def t10j32HighBitTailNode109Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode109LhsNum
  lhsDen := t10j32HighBitTailNode109LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode109LhsDen]
  vector := t10j32HighBitTailNode109Vector
  vector_pos := by norm_num [t10j32HighBitTailNode109Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode109Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 109. -/
theorem t10j32HighBitTailNode109MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (109 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode109LhsNum : NNReal) / (t10j32HighBitTailNode109LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode109LhsNum, t10j32HighBitTailNode109LhsDen]

/-- Evaluated row certificate for generated row 109. -/
def t10j32HighBitTailNode109Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (109 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode109Row
  lhs_eq := by simpa using t10j32HighBitTailNode109MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode109Row]


/-- State label for generated row 110. -/
def t10j32HighBitTailNode110Label : String :=
  "v2=6|odd=3|h=2"

/-- Destination support of generated row 110. -/
def t10j32HighBitTailNode110Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 110. -/
def t10j32HighBitTailNode110LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 110. -/
def t10j32HighBitTailNode110LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 110. -/
def t10j32HighBitTailNode110Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 110. -/
theorem t10j32HighBitTailNode110Bound :
    t10j32HighBitTailNode110LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode110Vector * t10j32HighBitTailNode110LhsDen := by
  norm_num [t10j32HighBitTailNode110LhsNum, t10j32HighBitTailNode110LhsDen, t10j32HighBitTailNode110Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 110. -/
def t10j32HighBitTailNode110Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode110LhsNum
  lhsDen := t10j32HighBitTailNode110LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode110LhsDen]
  vector := t10j32HighBitTailNode110Vector
  vector_pos := by norm_num [t10j32HighBitTailNode110Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode110Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 110. -/
theorem t10j32HighBitTailNode110MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (110 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode110LhsNum : NNReal) / (t10j32HighBitTailNode110LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode110LhsNum, t10j32HighBitTailNode110LhsDen]

/-- Evaluated row certificate for generated row 110. -/
def t10j32HighBitTailNode110Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (110 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode110Row
  lhs_eq := by simpa using t10j32HighBitTailNode110MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode110Row]


/-- State label for generated row 111. -/
def t10j32HighBitTailNode111Label : String :=
  "v2=6|odd=3|h=3"

/-- Destination support of generated row 111. -/
def t10j32HighBitTailNode111Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 111. -/
def t10j32HighBitTailNode111LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 111. -/
def t10j32HighBitTailNode111LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 111. -/
def t10j32HighBitTailNode111Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 111. -/
theorem t10j32HighBitTailNode111Bound :
    t10j32HighBitTailNode111LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode111Vector * t10j32HighBitTailNode111LhsDen := by
  norm_num [t10j32HighBitTailNode111LhsNum, t10j32HighBitTailNode111LhsDen, t10j32HighBitTailNode111Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 111. -/
def t10j32HighBitTailNode111Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode111LhsNum
  lhsDen := t10j32HighBitTailNode111LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode111LhsDen]
  vector := t10j32HighBitTailNode111Vector
  vector_pos := by norm_num [t10j32HighBitTailNode111Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode111Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 111. -/
theorem t10j32HighBitTailNode111MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (111 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode111LhsNum : NNReal) / (t10j32HighBitTailNode111LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode111LhsNum, t10j32HighBitTailNode111LhsDen]

/-- Evaluated row certificate for generated row 111. -/
def t10j32HighBitTailNode111Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (111 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode111Row
  lhs_eq := by simpa using t10j32HighBitTailNode111MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode111Row]

end Generated
end CollatzShadowing
