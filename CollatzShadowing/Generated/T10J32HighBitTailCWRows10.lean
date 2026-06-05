import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 160. -/
def t10j32HighBitTailNode160Label : String :=
  "v2=10|odd=0|h=0"

/-- Destination support of generated row 160. -/
def t10j32HighBitTailNode160Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 160. -/
def t10j32HighBitTailNode160LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 160. -/
def t10j32HighBitTailNode160LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 160. -/
def t10j32HighBitTailNode160Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 160. -/
theorem t10j32HighBitTailNode160Bound :
    t10j32HighBitTailNode160LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode160Vector * t10j32HighBitTailNode160LhsDen := by
  norm_num [t10j32HighBitTailNode160LhsNum, t10j32HighBitTailNode160LhsDen, t10j32HighBitTailNode160Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 160. -/
def t10j32HighBitTailNode160Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode160LhsNum
  lhsDen := t10j32HighBitTailNode160LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode160LhsDen]
  vector := t10j32HighBitTailNode160Vector
  vector_pos := by norm_num [t10j32HighBitTailNode160Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode160Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 160. -/
theorem t10j32HighBitTailNode160MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (160 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode160LhsNum : NNReal) / (t10j32HighBitTailNode160LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode160LhsNum, t10j32HighBitTailNode160LhsDen]

/-- Evaluated row certificate for generated row 160. -/
def t10j32HighBitTailNode160Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (160 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode160Row
  lhs_eq := by simpa using t10j32HighBitTailNode160MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode160Row]


/-- State label for generated row 161. -/
def t10j32HighBitTailNode161Label : String :=
  "v2=10|odd=0|h=1"

/-- Destination support of generated row 161. -/
def t10j32HighBitTailNode161Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 161. -/
def t10j32HighBitTailNode161LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 161. -/
def t10j32HighBitTailNode161LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 161. -/
def t10j32HighBitTailNode161Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 161. -/
theorem t10j32HighBitTailNode161Bound :
    t10j32HighBitTailNode161LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode161Vector * t10j32HighBitTailNode161LhsDen := by
  norm_num [t10j32HighBitTailNode161LhsNum, t10j32HighBitTailNode161LhsDen, t10j32HighBitTailNode161Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 161. -/
def t10j32HighBitTailNode161Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode161LhsNum
  lhsDen := t10j32HighBitTailNode161LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode161LhsDen]
  vector := t10j32HighBitTailNode161Vector
  vector_pos := by norm_num [t10j32HighBitTailNode161Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode161Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 161. -/
theorem t10j32HighBitTailNode161MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (161 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode161LhsNum : NNReal) / (t10j32HighBitTailNode161LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode161LhsNum, t10j32HighBitTailNode161LhsDen]

/-- Evaluated row certificate for generated row 161. -/
def t10j32HighBitTailNode161Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (161 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode161Row
  lhs_eq := by simpa using t10j32HighBitTailNode161MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode161Row]


/-- State label for generated row 162. -/
def t10j32HighBitTailNode162Label : String :=
  "v2=10|odd=0|h=2"

/-- Destination support of generated row 162. -/
def t10j32HighBitTailNode162Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 162. -/
def t10j32HighBitTailNode162LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 162. -/
def t10j32HighBitTailNode162LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 162. -/
def t10j32HighBitTailNode162Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 162. -/
theorem t10j32HighBitTailNode162Bound :
    t10j32HighBitTailNode162LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode162Vector * t10j32HighBitTailNode162LhsDen := by
  norm_num [t10j32HighBitTailNode162LhsNum, t10j32HighBitTailNode162LhsDen, t10j32HighBitTailNode162Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 162. -/
def t10j32HighBitTailNode162Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode162LhsNum
  lhsDen := t10j32HighBitTailNode162LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode162LhsDen]
  vector := t10j32HighBitTailNode162Vector
  vector_pos := by norm_num [t10j32HighBitTailNode162Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode162Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 162. -/
theorem t10j32HighBitTailNode162MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (162 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode162LhsNum : NNReal) / (t10j32HighBitTailNode162LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode162LhsNum, t10j32HighBitTailNode162LhsDen]

/-- Evaluated row certificate for generated row 162. -/
def t10j32HighBitTailNode162Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (162 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode162Row
  lhs_eq := by simpa using t10j32HighBitTailNode162MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode162Row]


/-- State label for generated row 163. -/
def t10j32HighBitTailNode163Label : String :=
  "v2=10|odd=0|h=3"

/-- Destination support of generated row 163. -/
def t10j32HighBitTailNode163Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 163. -/
def t10j32HighBitTailNode163LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 163. -/
def t10j32HighBitTailNode163LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 163. -/
def t10j32HighBitTailNode163Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 163. -/
theorem t10j32HighBitTailNode163Bound :
    t10j32HighBitTailNode163LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode163Vector * t10j32HighBitTailNode163LhsDen := by
  norm_num [t10j32HighBitTailNode163LhsNum, t10j32HighBitTailNode163LhsDen, t10j32HighBitTailNode163Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 163. -/
def t10j32HighBitTailNode163Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode163LhsNum
  lhsDen := t10j32HighBitTailNode163LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode163LhsDen]
  vector := t10j32HighBitTailNode163Vector
  vector_pos := by norm_num [t10j32HighBitTailNode163Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode163Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 163. -/
theorem t10j32HighBitTailNode163MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (163 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode163LhsNum : NNReal) / (t10j32HighBitTailNode163LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode163LhsNum, t10j32HighBitTailNode163LhsDen]

/-- Evaluated row certificate for generated row 163. -/
def t10j32HighBitTailNode163Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (163 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode163Row
  lhs_eq := by simpa using t10j32HighBitTailNode163MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode163Row]


/-- State label for generated row 164. -/
def t10j32HighBitTailNode164Label : String :=
  "v2=10|odd=1|h=0"

/-- Destination support of generated row 164. -/
def t10j32HighBitTailNode164Support : Finset T10J32HighBitTailState :=
  {69}

/-- Exact generated summand values for row 164. -/
noncomputable def t10j32HighBitTailNode164Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 69 => ((62500 : NNReal) / (1 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 164. -/
def t10j32HighBitTailNode164LhsNum : Nat :=
  62500

/-- Exact denominator of `(M v)_i` for generated row 164. -/
def t10j32HighBitTailNode164LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 164. -/
def t10j32HighBitTailNode164Vector : Nat :=
  2288660

/-- Exact cleared-denominator CW inequality for generated row 164. -/
theorem t10j32HighBitTailNode164Bound :
    t10j32HighBitTailNode164LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode164Vector * t10j32HighBitTailNode164LhsDen := by
  norm_num [t10j32HighBitTailNode164LhsNum, t10j32HighBitTailNode164LhsDen, t10j32HighBitTailNode164Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 164. -/
def t10j32HighBitTailNode164Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode164LhsNum
  lhsDen := t10j32HighBitTailNode164LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode164LhsDen]
  vector := t10j32HighBitTailNode164Vector
  vector_pos := by norm_num [t10j32HighBitTailNode164Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode164Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 164. -/
theorem t10j32HighBitTailNode164MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (164 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode164LhsNum : NNReal) / (t10j32HighBitTailNode164LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode164Support,
      t10j32HighBitTailMatrix (164 : T10J32HighBitTailState) dst *
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
    have h069 :
        t10j32HighBitTailMatrix (164 : T10J32HighBitTailState) (69 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (69 : T10J32HighBitTailState) =
          t10j32HighBitTailNode164Term (69 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode164Term (69 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode164Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode164Support,
          t10j32HighBitTailMatrix (164 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode164Support, t10j32HighBitTailNode164Term dst := by
        simp [t10j32HighBitTailNode164Support, h069]
      _ = (t10j32HighBitTailNode164LhsNum : NNReal) / (t10j32HighBitTailNode164LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode164Support, t10j32HighBitTailNode164Term]
        norm_num [t10j32HighBitTailNode164LhsNum, t10j32HighBitTailNode164LhsDen]

/-- Evaluated row certificate for generated row 164. -/
def t10j32HighBitTailNode164Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (164 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode164Row
  lhs_eq := by simpa using t10j32HighBitTailNode164MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode164Row]


/-- State label for generated row 165. -/
def t10j32HighBitTailNode165Label : String :=
  "v2=10|odd=1|h=1"

/-- Destination support of generated row 165. -/
def t10j32HighBitTailNode165Support : Finset T10J32HighBitTailState :=
  {70}

/-- Exact generated summand values for row 165. -/
noncomputable def t10j32HighBitTailNode165Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 70 => ((62500 : NNReal) / (1 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 165. -/
def t10j32HighBitTailNode165LhsNum : Nat :=
  62500

/-- Exact denominator of `(M v)_i` for generated row 165. -/
def t10j32HighBitTailNode165LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 165. -/
def t10j32HighBitTailNode165Vector : Nat :=
  2288660

/-- Exact cleared-denominator CW inequality for generated row 165. -/
theorem t10j32HighBitTailNode165Bound :
    t10j32HighBitTailNode165LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode165Vector * t10j32HighBitTailNode165LhsDen := by
  norm_num [t10j32HighBitTailNode165LhsNum, t10j32HighBitTailNode165LhsDen, t10j32HighBitTailNode165Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 165. -/
def t10j32HighBitTailNode165Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode165LhsNum
  lhsDen := t10j32HighBitTailNode165LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode165LhsDen]
  vector := t10j32HighBitTailNode165Vector
  vector_pos := by norm_num [t10j32HighBitTailNode165Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode165Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 165. -/
theorem t10j32HighBitTailNode165MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (165 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode165LhsNum : NNReal) / (t10j32HighBitTailNode165LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode165Support,
      t10j32HighBitTailMatrix (165 : T10J32HighBitTailState) dst *
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
    have h070 :
        t10j32HighBitTailMatrix (165 : T10J32HighBitTailState) (70 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (70 : T10J32HighBitTailState) =
          t10j32HighBitTailNode165Term (70 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode165Term (70 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode165Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode165Support,
          t10j32HighBitTailMatrix (165 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode165Support, t10j32HighBitTailNode165Term dst := by
        simp [t10j32HighBitTailNode165Support, h070]
      _ = (t10j32HighBitTailNode165LhsNum : NNReal) / (t10j32HighBitTailNode165LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode165Support, t10j32HighBitTailNode165Term]
        norm_num [t10j32HighBitTailNode165LhsNum, t10j32HighBitTailNode165LhsDen]

/-- Evaluated row certificate for generated row 165. -/
def t10j32HighBitTailNode165Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (165 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode165Row
  lhs_eq := by simpa using t10j32HighBitTailNode165MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode165Row]


/-- State label for generated row 166. -/
def t10j32HighBitTailNode166Label : String :=
  "v2=10|odd=1|h=2"

/-- Destination support of generated row 166. -/
def t10j32HighBitTailNode166Support : Finset T10J32HighBitTailState :=
  {71}

/-- Exact generated summand values for row 166. -/
noncomputable def t10j32HighBitTailNode166Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 71 => ((62500 : NNReal) / (1 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 166. -/
def t10j32HighBitTailNode166LhsNum : Nat :=
  62500

/-- Exact denominator of `(M v)_i` for generated row 166. -/
def t10j32HighBitTailNode166LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 166. -/
def t10j32HighBitTailNode166Vector : Nat :=
  2288660

/-- Exact cleared-denominator CW inequality for generated row 166. -/
theorem t10j32HighBitTailNode166Bound :
    t10j32HighBitTailNode166LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode166Vector * t10j32HighBitTailNode166LhsDen := by
  norm_num [t10j32HighBitTailNode166LhsNum, t10j32HighBitTailNode166LhsDen, t10j32HighBitTailNode166Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 166. -/
def t10j32HighBitTailNode166Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode166LhsNum
  lhsDen := t10j32HighBitTailNode166LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode166LhsDen]
  vector := t10j32HighBitTailNode166Vector
  vector_pos := by norm_num [t10j32HighBitTailNode166Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode166Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 166. -/
theorem t10j32HighBitTailNode166MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (166 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode166LhsNum : NNReal) / (t10j32HighBitTailNode166LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode166Support,
      t10j32HighBitTailMatrix (166 : T10J32HighBitTailState) dst *
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
    have h071 :
        t10j32HighBitTailMatrix (166 : T10J32HighBitTailState) (71 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (71 : T10J32HighBitTailState) =
          t10j32HighBitTailNode166Term (71 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode166Term (71 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode166Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode166Support,
          t10j32HighBitTailMatrix (166 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode166Support, t10j32HighBitTailNode166Term dst := by
        simp [t10j32HighBitTailNode166Support, h071]
      _ = (t10j32HighBitTailNode166LhsNum : NNReal) / (t10j32HighBitTailNode166LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode166Support, t10j32HighBitTailNode166Term]
        norm_num [t10j32HighBitTailNode166LhsNum, t10j32HighBitTailNode166LhsDen]

/-- Evaluated row certificate for generated row 166. -/
def t10j32HighBitTailNode166Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (166 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode166Row
  lhs_eq := by simpa using t10j32HighBitTailNode166MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode166Row]


/-- State label for generated row 167. -/
def t10j32HighBitTailNode167Label : String :=
  "v2=10|odd=1|h=3"

/-- Destination support of generated row 167. -/
def t10j32HighBitTailNode167Support : Finset T10J32HighBitTailState :=
  {68}

/-- Exact generated summand values for row 167. -/
noncomputable def t10j32HighBitTailNode167Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 68 => ((62500 : NNReal) / (1 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 167. -/
def t10j32HighBitTailNode167LhsNum : Nat :=
  62500

/-- Exact denominator of `(M v)_i` for generated row 167. -/
def t10j32HighBitTailNode167LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 167. -/
def t10j32HighBitTailNode167Vector : Nat :=
  2288660

/-- Exact cleared-denominator CW inequality for generated row 167. -/
theorem t10j32HighBitTailNode167Bound :
    t10j32HighBitTailNode167LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode167Vector * t10j32HighBitTailNode167LhsDen := by
  norm_num [t10j32HighBitTailNode167LhsNum, t10j32HighBitTailNode167LhsDen, t10j32HighBitTailNode167Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 167. -/
def t10j32HighBitTailNode167Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode167LhsNum
  lhsDen := t10j32HighBitTailNode167LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode167LhsDen]
  vector := t10j32HighBitTailNode167Vector
  vector_pos := by norm_num [t10j32HighBitTailNode167Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode167Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 167. -/
theorem t10j32HighBitTailNode167MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (167 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode167LhsNum : NNReal) / (t10j32HighBitTailNode167LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode167Support,
      t10j32HighBitTailMatrix (167 : T10J32HighBitTailState) dst *
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
    have h068 :
        t10j32HighBitTailMatrix (167 : T10J32HighBitTailState) (68 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (68 : T10J32HighBitTailState) =
          t10j32HighBitTailNode167Term (68 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode167Term (68 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode167Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode167Support,
          t10j32HighBitTailMatrix (167 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode167Support, t10j32HighBitTailNode167Term dst := by
        simp [t10j32HighBitTailNode167Support, h068]
      _ = (t10j32HighBitTailNode167LhsNum : NNReal) / (t10j32HighBitTailNode167LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode167Support, t10j32HighBitTailNode167Term]
        norm_num [t10j32HighBitTailNode167LhsNum, t10j32HighBitTailNode167LhsDen]

/-- Evaluated row certificate for generated row 167. -/
def t10j32HighBitTailNode167Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (167 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode167Row
  lhs_eq := by simpa using t10j32HighBitTailNode167MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode167Row]


/-- State label for generated row 168. -/
def t10j32HighBitTailNode168Label : String :=
  "v2=10|odd=2|h=0"

/-- Destination support of generated row 168. -/
def t10j32HighBitTailNode168Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 168. -/
def t10j32HighBitTailNode168LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 168. -/
def t10j32HighBitTailNode168LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 168. -/
def t10j32HighBitTailNode168Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 168. -/
theorem t10j32HighBitTailNode168Bound :
    t10j32HighBitTailNode168LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode168Vector * t10j32HighBitTailNode168LhsDen := by
  norm_num [t10j32HighBitTailNode168LhsNum, t10j32HighBitTailNode168LhsDen, t10j32HighBitTailNode168Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 168. -/
def t10j32HighBitTailNode168Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode168LhsNum
  lhsDen := t10j32HighBitTailNode168LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode168LhsDen]
  vector := t10j32HighBitTailNode168Vector
  vector_pos := by norm_num [t10j32HighBitTailNode168Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode168Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 168. -/
theorem t10j32HighBitTailNode168MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (168 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode168LhsNum : NNReal) / (t10j32HighBitTailNode168LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode168LhsNum, t10j32HighBitTailNode168LhsDen]

/-- Evaluated row certificate for generated row 168. -/
def t10j32HighBitTailNode168Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (168 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode168Row
  lhs_eq := by simpa using t10j32HighBitTailNode168MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode168Row]


/-- State label for generated row 169. -/
def t10j32HighBitTailNode169Label : String :=
  "v2=10|odd=2|h=1"

/-- Destination support of generated row 169. -/
def t10j32HighBitTailNode169Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 169. -/
def t10j32HighBitTailNode169LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 169. -/
def t10j32HighBitTailNode169LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 169. -/
def t10j32HighBitTailNode169Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 169. -/
theorem t10j32HighBitTailNode169Bound :
    t10j32HighBitTailNode169LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode169Vector * t10j32HighBitTailNode169LhsDen := by
  norm_num [t10j32HighBitTailNode169LhsNum, t10j32HighBitTailNode169LhsDen, t10j32HighBitTailNode169Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 169. -/
def t10j32HighBitTailNode169Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode169LhsNum
  lhsDen := t10j32HighBitTailNode169LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode169LhsDen]
  vector := t10j32HighBitTailNode169Vector
  vector_pos := by norm_num [t10j32HighBitTailNode169Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode169Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 169. -/
theorem t10j32HighBitTailNode169MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (169 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode169LhsNum : NNReal) / (t10j32HighBitTailNode169LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode169LhsNum, t10j32HighBitTailNode169LhsDen]

/-- Evaluated row certificate for generated row 169. -/
def t10j32HighBitTailNode169Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (169 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode169Row
  lhs_eq := by simpa using t10j32HighBitTailNode169MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode169Row]


/-- State label for generated row 170. -/
def t10j32HighBitTailNode170Label : String :=
  "v2=10|odd=2|h=2"

/-- Destination support of generated row 170. -/
def t10j32HighBitTailNode170Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 170. -/
def t10j32HighBitTailNode170LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 170. -/
def t10j32HighBitTailNode170LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 170. -/
def t10j32HighBitTailNode170Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 170. -/
theorem t10j32HighBitTailNode170Bound :
    t10j32HighBitTailNode170LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode170Vector * t10j32HighBitTailNode170LhsDen := by
  norm_num [t10j32HighBitTailNode170LhsNum, t10j32HighBitTailNode170LhsDen, t10j32HighBitTailNode170Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 170. -/
def t10j32HighBitTailNode170Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode170LhsNum
  lhsDen := t10j32HighBitTailNode170LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode170LhsDen]
  vector := t10j32HighBitTailNode170Vector
  vector_pos := by norm_num [t10j32HighBitTailNode170Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode170Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 170. -/
theorem t10j32HighBitTailNode170MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (170 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode170LhsNum : NNReal) / (t10j32HighBitTailNode170LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode170LhsNum, t10j32HighBitTailNode170LhsDen]

/-- Evaluated row certificate for generated row 170. -/
def t10j32HighBitTailNode170Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (170 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode170Row
  lhs_eq := by simpa using t10j32HighBitTailNode170MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode170Row]


/-- State label for generated row 171. -/
def t10j32HighBitTailNode171Label : String :=
  "v2=10|odd=2|h=3"

/-- Destination support of generated row 171. -/
def t10j32HighBitTailNode171Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 171. -/
def t10j32HighBitTailNode171LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 171. -/
def t10j32HighBitTailNode171LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 171. -/
def t10j32HighBitTailNode171Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 171. -/
theorem t10j32HighBitTailNode171Bound :
    t10j32HighBitTailNode171LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode171Vector * t10j32HighBitTailNode171LhsDen := by
  norm_num [t10j32HighBitTailNode171LhsNum, t10j32HighBitTailNode171LhsDen, t10j32HighBitTailNode171Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 171. -/
def t10j32HighBitTailNode171Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode171LhsNum
  lhsDen := t10j32HighBitTailNode171LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode171LhsDen]
  vector := t10j32HighBitTailNode171Vector
  vector_pos := by norm_num [t10j32HighBitTailNode171Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode171Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 171. -/
theorem t10j32HighBitTailNode171MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (171 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode171LhsNum : NNReal) / (t10j32HighBitTailNode171LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode171LhsNum, t10j32HighBitTailNode171LhsDen]

/-- Evaluated row certificate for generated row 171. -/
def t10j32HighBitTailNode171Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (171 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode171Row
  lhs_eq := by simpa using t10j32HighBitTailNode171MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode171Row]


/-- State label for generated row 172. -/
def t10j32HighBitTailNode172Label : String :=
  "v2=10|odd=3|h=0"

/-- Destination support of generated row 172. -/
def t10j32HighBitTailNode172Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 45, 85}

/-- Exact generated summand values for row 172. -/
noncomputable def t10j32HighBitTailNode172Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((492054 : NNReal) / (1 : NNReal))
  | 13 => ((2156389 : NNReal) / (8 : NNReal))
  | 21 => ((1403499 : NNReal) / (16 : NNReal))
  | 29 => ((1918835 : NNReal) / (16 : NNReal))
  | 45 => ((12659139 : NNReal) / (16 : NNReal))
  | 85 => ((1834187 : NNReal) / (16 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 172. -/
def t10j32HighBitTailNode172LhsNum : Nat :=
  15000651

/-- Exact denominator of `(M v)_i` for generated row 172. -/
def t10j32HighBitTailNode172LhsDen : Nat :=
  8

/-- Exact vector entry for generated row 172. -/
def t10j32HighBitTailNode172Vector : Nat :=
  39661472

/-- Exact cleared-denominator CW inequality for generated row 172. -/
theorem t10j32HighBitTailNode172Bound :
    t10j32HighBitTailNode172LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode172Vector * t10j32HighBitTailNode172LhsDen := by
  norm_num [t10j32HighBitTailNode172LhsNum, t10j32HighBitTailNode172LhsDen, t10j32HighBitTailNode172Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 172. -/
def t10j32HighBitTailNode172Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode172LhsNum
  lhsDen := t10j32HighBitTailNode172LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode172LhsDen]
  vector := t10j32HighBitTailNode172Vector
  vector_pos := by norm_num [t10j32HighBitTailNode172Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode172Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 172. -/
theorem t10j32HighBitTailNode172MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (172 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode172LhsNum : NNReal) / (t10j32HighBitTailNode172LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode172Support,
      t10j32HighBitTailMatrix (172 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (172 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode172Term (5 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode172Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode172Term]
    have h013 :
        t10j32HighBitTailMatrix (172 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode172Term (13 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode172Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode172Term]
    have h021 :
        t10j32HighBitTailMatrix (172 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode172Term (21 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode172Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode172Term]
    have h029 :
        t10j32HighBitTailMatrix (172 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode172Term (29 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode172Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode172Term]
    have h045 :
        t10j32HighBitTailMatrix (172 : T10J32HighBitTailState) (45 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (45 : T10J32HighBitTailState) =
          t10j32HighBitTailNode172Term (45 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode172Term (45 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode172Term]
    have h085 :
        t10j32HighBitTailMatrix (172 : T10J32HighBitTailState) (85 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (85 : T10J32HighBitTailState) =
          t10j32HighBitTailNode172Term (85 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode172Term (85 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode172Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode172Support,
          t10j32HighBitTailMatrix (172 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode172Support, t10j32HighBitTailNode172Term dst := by
        simp [t10j32HighBitTailNode172Support, h005, h013, h021, h029, h045, h085]
      _ = (t10j32HighBitTailNode172LhsNum : NNReal) / (t10j32HighBitTailNode172LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode172Support, t10j32HighBitTailNode172Term]
        norm_num [t10j32HighBitTailNode172LhsNum, t10j32HighBitTailNode172LhsDen]

/-- Evaluated row certificate for generated row 172. -/
def t10j32HighBitTailNode172Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (172 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode172Row
  lhs_eq := by simpa using t10j32HighBitTailNode172MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode172Row]


/-- State label for generated row 173. -/
def t10j32HighBitTailNode173Label : String :=
  "v2=10|odd=3|h=1"

/-- Destination support of generated row 173. -/
def t10j32HighBitTailNode173Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 46, 86}

/-- Exact generated summand values for row 173. -/
noncomputable def t10j32HighBitTailNode173Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((492054 : NNReal) / (1 : NNReal))
  | 14 => ((2156389 : NNReal) / (8 : NNReal))
  | 22 => ((1403499 : NNReal) / (16 : NNReal))
  | 30 => ((1918835 : NNReal) / (16 : NNReal))
  | 46 => ((12659139 : NNReal) / (16 : NNReal))
  | 86 => ((1834187 : NNReal) / (16 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 173. -/
def t10j32HighBitTailNode173LhsNum : Nat :=
  15000651

/-- Exact denominator of `(M v)_i` for generated row 173. -/
def t10j32HighBitTailNode173LhsDen : Nat :=
  8

/-- Exact vector entry for generated row 173. -/
def t10j32HighBitTailNode173Vector : Nat :=
  39661472

/-- Exact cleared-denominator CW inequality for generated row 173. -/
theorem t10j32HighBitTailNode173Bound :
    t10j32HighBitTailNode173LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode173Vector * t10j32HighBitTailNode173LhsDen := by
  norm_num [t10j32HighBitTailNode173LhsNum, t10j32HighBitTailNode173LhsDen, t10j32HighBitTailNode173Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 173. -/
def t10j32HighBitTailNode173Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode173LhsNum
  lhsDen := t10j32HighBitTailNode173LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode173LhsDen]
  vector := t10j32HighBitTailNode173Vector
  vector_pos := by norm_num [t10j32HighBitTailNode173Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode173Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 173. -/
theorem t10j32HighBitTailNode173MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (173 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode173LhsNum : NNReal) / (t10j32HighBitTailNode173LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode173Support,
      t10j32HighBitTailMatrix (173 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (173 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode173Term (6 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode173Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode173Term]
    have h014 :
        t10j32HighBitTailMatrix (173 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode173Term (14 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode173Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode173Term]
    have h022 :
        t10j32HighBitTailMatrix (173 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode173Term (22 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode173Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode173Term]
    have h030 :
        t10j32HighBitTailMatrix (173 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode173Term (30 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode173Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode173Term]
    have h046 :
        t10j32HighBitTailMatrix (173 : T10J32HighBitTailState) (46 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (46 : T10J32HighBitTailState) =
          t10j32HighBitTailNode173Term (46 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode173Term (46 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode173Term]
    have h086 :
        t10j32HighBitTailMatrix (173 : T10J32HighBitTailState) (86 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (86 : T10J32HighBitTailState) =
          t10j32HighBitTailNode173Term (86 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode173Term (86 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode173Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode173Support,
          t10j32HighBitTailMatrix (173 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode173Support, t10j32HighBitTailNode173Term dst := by
        simp [t10j32HighBitTailNode173Support, h006, h014, h022, h030, h046, h086]
      _ = (t10j32HighBitTailNode173LhsNum : NNReal) / (t10j32HighBitTailNode173LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode173Support, t10j32HighBitTailNode173Term]
        norm_num [t10j32HighBitTailNode173LhsNum, t10j32HighBitTailNode173LhsDen]

/-- Evaluated row certificate for generated row 173. -/
def t10j32HighBitTailNode173Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (173 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode173Row
  lhs_eq := by simpa using t10j32HighBitTailNode173MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode173Row]


/-- State label for generated row 174. -/
def t10j32HighBitTailNode174Label : String :=
  "v2=10|odd=3|h=2"

/-- Destination support of generated row 174. -/
def t10j32HighBitTailNode174Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 47, 87}

/-- Exact generated summand values for row 174. -/
noncomputable def t10j32HighBitTailNode174Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((492054 : NNReal) / (1 : NNReal))
  | 15 => ((2156389 : NNReal) / (8 : NNReal))
  | 23 => ((1403499 : NNReal) / (16 : NNReal))
  | 31 => ((1918835 : NNReal) / (16 : NNReal))
  | 47 => ((12659139 : NNReal) / (16 : NNReal))
  | 87 => ((1834187 : NNReal) / (16 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 174. -/
def t10j32HighBitTailNode174LhsNum : Nat :=
  15000651

/-- Exact denominator of `(M v)_i` for generated row 174. -/
def t10j32HighBitTailNode174LhsDen : Nat :=
  8

/-- Exact vector entry for generated row 174. -/
def t10j32HighBitTailNode174Vector : Nat :=
  39661472

/-- Exact cleared-denominator CW inequality for generated row 174. -/
theorem t10j32HighBitTailNode174Bound :
    t10j32HighBitTailNode174LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode174Vector * t10j32HighBitTailNode174LhsDen := by
  norm_num [t10j32HighBitTailNode174LhsNum, t10j32HighBitTailNode174LhsDen, t10j32HighBitTailNode174Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 174. -/
def t10j32HighBitTailNode174Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode174LhsNum
  lhsDen := t10j32HighBitTailNode174LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode174LhsDen]
  vector := t10j32HighBitTailNode174Vector
  vector_pos := by norm_num [t10j32HighBitTailNode174Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode174Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 174. -/
theorem t10j32HighBitTailNode174MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (174 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode174LhsNum : NNReal) / (t10j32HighBitTailNode174LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode174Support,
      t10j32HighBitTailMatrix (174 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (174 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode174Term (7 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode174Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode174Term]
    have h015 :
        t10j32HighBitTailMatrix (174 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode174Term (15 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode174Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode174Term]
    have h023 :
        t10j32HighBitTailMatrix (174 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode174Term (23 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode174Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode174Term]
    have h031 :
        t10j32HighBitTailMatrix (174 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode174Term (31 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode174Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode174Term]
    have h047 :
        t10j32HighBitTailMatrix (174 : T10J32HighBitTailState) (47 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (47 : T10J32HighBitTailState) =
          t10j32HighBitTailNode174Term (47 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode174Term (47 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode174Term]
    have h087 :
        t10j32HighBitTailMatrix (174 : T10J32HighBitTailState) (87 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (87 : T10J32HighBitTailState) =
          t10j32HighBitTailNode174Term (87 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode174Term (87 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode174Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode174Support,
          t10j32HighBitTailMatrix (174 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode174Support, t10j32HighBitTailNode174Term dst := by
        simp [t10j32HighBitTailNode174Support, h007, h015, h023, h031, h047, h087]
      _ = (t10j32HighBitTailNode174LhsNum : NNReal) / (t10j32HighBitTailNode174LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode174Support, t10j32HighBitTailNode174Term]
        norm_num [t10j32HighBitTailNode174LhsNum, t10j32HighBitTailNode174LhsDen]

/-- Evaluated row certificate for generated row 174. -/
def t10j32HighBitTailNode174Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (174 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode174Row
  lhs_eq := by simpa using t10j32HighBitTailNode174MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode174Row]


/-- State label for generated row 175. -/
def t10j32HighBitTailNode175Label : String :=
  "v2=10|odd=3|h=3"

/-- Destination support of generated row 175. -/
def t10j32HighBitTailNode175Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 44, 84}

/-- Exact generated summand values for row 175. -/
noncomputable def t10j32HighBitTailNode175Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((492054 : NNReal) / (1 : NNReal))
  | 12 => ((2156389 : NNReal) / (8 : NNReal))
  | 20 => ((1403499 : NNReal) / (16 : NNReal))
  | 28 => ((1918835 : NNReal) / (16 : NNReal))
  | 44 => ((12659139 : NNReal) / (16 : NNReal))
  | 84 => ((1834187 : NNReal) / (16 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 175. -/
def t10j32HighBitTailNode175LhsNum : Nat :=
  15000651

/-- Exact denominator of `(M v)_i` for generated row 175. -/
def t10j32HighBitTailNode175LhsDen : Nat :=
  8

/-- Exact vector entry for generated row 175. -/
def t10j32HighBitTailNode175Vector : Nat :=
  39661472

/-- Exact cleared-denominator CW inequality for generated row 175. -/
theorem t10j32HighBitTailNode175Bound :
    t10j32HighBitTailNode175LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode175Vector * t10j32HighBitTailNode175LhsDen := by
  norm_num [t10j32HighBitTailNode175LhsNum, t10j32HighBitTailNode175LhsDen, t10j32HighBitTailNode175Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 175. -/
def t10j32HighBitTailNode175Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode175LhsNum
  lhsDen := t10j32HighBitTailNode175LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode175LhsDen]
  vector := t10j32HighBitTailNode175Vector
  vector_pos := by norm_num [t10j32HighBitTailNode175Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode175Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 175. -/
theorem t10j32HighBitTailNode175MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (175 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode175LhsNum : NNReal) / (t10j32HighBitTailNode175LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode175Support,
      t10j32HighBitTailMatrix (175 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (175 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode175Term (4 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode175Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode175Term]
    have h012 :
        t10j32HighBitTailMatrix (175 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode175Term (12 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode175Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode175Term]
    have h020 :
        t10j32HighBitTailMatrix (175 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode175Term (20 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode175Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode175Term]
    have h028 :
        t10j32HighBitTailMatrix (175 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode175Term (28 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode175Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode175Term]
    have h044 :
        t10j32HighBitTailMatrix (175 : T10J32HighBitTailState) (44 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (44 : T10J32HighBitTailState) =
          t10j32HighBitTailNode175Term (44 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode175Term (44 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode175Term]
    have h084 :
        t10j32HighBitTailMatrix (175 : T10J32HighBitTailState) (84 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (84 : T10J32HighBitTailState) =
          t10j32HighBitTailNode175Term (84 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (16 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode175Term (84 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode175Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode175Support,
          t10j32HighBitTailMatrix (175 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode175Support, t10j32HighBitTailNode175Term dst := by
        simp [t10j32HighBitTailNode175Support, h004, h012, h020, h028, h044, h084]
      _ = (t10j32HighBitTailNode175LhsNum : NNReal) / (t10j32HighBitTailNode175LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode175Support, t10j32HighBitTailNode175Term]
        norm_num [t10j32HighBitTailNode175LhsNum, t10j32HighBitTailNode175LhsDen]

/-- Evaluated row certificate for generated row 175. -/
def t10j32HighBitTailNode175Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (175 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode175Row
  lhs_eq := by simpa using t10j32HighBitTailNode175MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode175Row]

end Generated
end CollatzShadowing
