import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 144. -/
def t10j32HighBitTailNode144Label : String :=
  "v2=9|odd=0|h=0"

/-- Destination support of generated row 144. -/
def t10j32HighBitTailNode144Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 144. -/
def t10j32HighBitTailNode144LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 144. -/
def t10j32HighBitTailNode144LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 144. -/
def t10j32HighBitTailNode144Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 144. -/
theorem t10j32HighBitTailNode144Bound :
    t10j32HighBitTailNode144LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode144Vector * t10j32HighBitTailNode144LhsDen := by
  norm_num [t10j32HighBitTailNode144LhsNum, t10j32HighBitTailNode144LhsDen, t10j32HighBitTailNode144Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 144. -/
def t10j32HighBitTailNode144Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode144LhsNum
  lhsDen := t10j32HighBitTailNode144LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode144LhsDen]
  vector := t10j32HighBitTailNode144Vector
  vector_pos := by norm_num [t10j32HighBitTailNode144Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode144Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 144. -/
theorem t10j32HighBitTailNode144MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (144 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode144LhsNum : NNReal) / (t10j32HighBitTailNode144LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode144LhsNum, t10j32HighBitTailNode144LhsDen]

/-- Evaluated row certificate for generated row 144. -/
def t10j32HighBitTailNode144Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (144 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode144Row
  lhs_eq := by simpa using t10j32HighBitTailNode144MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode144Row]


/-- State label for generated row 145. -/
def t10j32HighBitTailNode145Label : String :=
  "v2=9|odd=0|h=1"

/-- Destination support of generated row 145. -/
def t10j32HighBitTailNode145Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 145. -/
def t10j32HighBitTailNode145LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 145. -/
def t10j32HighBitTailNode145LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 145. -/
def t10j32HighBitTailNode145Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 145. -/
theorem t10j32HighBitTailNode145Bound :
    t10j32HighBitTailNode145LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode145Vector * t10j32HighBitTailNode145LhsDen := by
  norm_num [t10j32HighBitTailNode145LhsNum, t10j32HighBitTailNode145LhsDen, t10j32HighBitTailNode145Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 145. -/
def t10j32HighBitTailNode145Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode145LhsNum
  lhsDen := t10j32HighBitTailNode145LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode145LhsDen]
  vector := t10j32HighBitTailNode145Vector
  vector_pos := by norm_num [t10j32HighBitTailNode145Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode145Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 145. -/
theorem t10j32HighBitTailNode145MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (145 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode145LhsNum : NNReal) / (t10j32HighBitTailNode145LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode145LhsNum, t10j32HighBitTailNode145LhsDen]

/-- Evaluated row certificate for generated row 145. -/
def t10j32HighBitTailNode145Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (145 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode145Row
  lhs_eq := by simpa using t10j32HighBitTailNode145MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode145Row]


/-- State label for generated row 146. -/
def t10j32HighBitTailNode146Label : String :=
  "v2=9|odd=0|h=2"

/-- Destination support of generated row 146. -/
def t10j32HighBitTailNode146Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 146. -/
def t10j32HighBitTailNode146LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 146. -/
def t10j32HighBitTailNode146LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 146. -/
def t10j32HighBitTailNode146Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 146. -/
theorem t10j32HighBitTailNode146Bound :
    t10j32HighBitTailNode146LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode146Vector * t10j32HighBitTailNode146LhsDen := by
  norm_num [t10j32HighBitTailNode146LhsNum, t10j32HighBitTailNode146LhsDen, t10j32HighBitTailNode146Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 146. -/
def t10j32HighBitTailNode146Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode146LhsNum
  lhsDen := t10j32HighBitTailNode146LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode146LhsDen]
  vector := t10j32HighBitTailNode146Vector
  vector_pos := by norm_num [t10j32HighBitTailNode146Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode146Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 146. -/
theorem t10j32HighBitTailNode146MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (146 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode146LhsNum : NNReal) / (t10j32HighBitTailNode146LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode146LhsNum, t10j32HighBitTailNode146LhsDen]

/-- Evaluated row certificate for generated row 146. -/
def t10j32HighBitTailNode146Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (146 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode146Row
  lhs_eq := by simpa using t10j32HighBitTailNode146MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode146Row]


/-- State label for generated row 147. -/
def t10j32HighBitTailNode147Label : String :=
  "v2=9|odd=0|h=3"

/-- Destination support of generated row 147. -/
def t10j32HighBitTailNode147Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 147. -/
def t10j32HighBitTailNode147LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 147. -/
def t10j32HighBitTailNode147LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 147. -/
def t10j32HighBitTailNode147Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 147. -/
theorem t10j32HighBitTailNode147Bound :
    t10j32HighBitTailNode147LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode147Vector * t10j32HighBitTailNode147LhsDen := by
  norm_num [t10j32HighBitTailNode147LhsNum, t10j32HighBitTailNode147LhsDen, t10j32HighBitTailNode147Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 147. -/
def t10j32HighBitTailNode147Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode147LhsNum
  lhsDen := t10j32HighBitTailNode147LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode147LhsDen]
  vector := t10j32HighBitTailNode147Vector
  vector_pos := by norm_num [t10j32HighBitTailNode147Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode147Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 147. -/
theorem t10j32HighBitTailNode147MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (147 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode147LhsNum : NNReal) / (t10j32HighBitTailNode147LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode147LhsNum, t10j32HighBitTailNode147LhsDen]

/-- Evaluated row certificate for generated row 147. -/
def t10j32HighBitTailNode147Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (147 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode147Row
  lhs_eq := by simpa using t10j32HighBitTailNode147MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode147Row]


/-- State label for generated row 148. -/
def t10j32HighBitTailNode148Label : String :=
  "v2=9|odd=1|h=0"

/-- Destination support of generated row 148. -/
def t10j32HighBitTailNode148Support : Finset T10J32HighBitTailState :=
  {13}

/-- Exact generated summand values for row 148. -/
noncomputable def t10j32HighBitTailNode148Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 13 => ((6469167 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 148. -/
def t10j32HighBitTailNode148LhsNum : Nat :=
  6469167

/-- Exact denominator of `(M v)_i` for generated row 148. -/
def t10j32HighBitTailNode148LhsDen : Nat :=
  64

/-- Exact vector entry for generated row 148. -/
def t10j32HighBitTailNode148Vector : Nat :=
  3084139

/-- Exact cleared-denominator CW inequality for generated row 148. -/
theorem t10j32HighBitTailNode148Bound :
    t10j32HighBitTailNode148LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode148Vector * t10j32HighBitTailNode148LhsDen := by
  norm_num [t10j32HighBitTailNode148LhsNum, t10j32HighBitTailNode148LhsDen, t10j32HighBitTailNode148Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 148. -/
def t10j32HighBitTailNode148Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode148LhsNum
  lhsDen := t10j32HighBitTailNode148LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode148LhsDen]
  vector := t10j32HighBitTailNode148Vector
  vector_pos := by norm_num [t10j32HighBitTailNode148Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode148Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 148. -/
theorem t10j32HighBitTailNode148MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (148 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode148LhsNum : NNReal) / (t10j32HighBitTailNode148LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode148Support,
      t10j32HighBitTailMatrix (148 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (148 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode148Term (13 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (64 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode148Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode148Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode148Support,
          t10j32HighBitTailMatrix (148 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode148Support, t10j32HighBitTailNode148Term dst := by
        simp [t10j32HighBitTailNode148Support, h013]
      _ = (t10j32HighBitTailNode148LhsNum : NNReal) / (t10j32HighBitTailNode148LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode148Support, t10j32HighBitTailNode148Term]
        norm_num [t10j32HighBitTailNode148LhsNum, t10j32HighBitTailNode148LhsDen]

/-- Evaluated row certificate for generated row 148. -/
def t10j32HighBitTailNode148Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (148 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode148Row
  lhs_eq := by simpa using t10j32HighBitTailNode148MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode148Row]


/-- State label for generated row 149. -/
def t10j32HighBitTailNode149Label : String :=
  "v2=9|odd=1|h=1"

/-- Destination support of generated row 149. -/
def t10j32HighBitTailNode149Support : Finset T10J32HighBitTailState :=
  {14}

/-- Exact generated summand values for row 149. -/
noncomputable def t10j32HighBitTailNode149Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 14 => ((6469167 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 149. -/
def t10j32HighBitTailNode149LhsNum : Nat :=
  6469167

/-- Exact denominator of `(M v)_i` for generated row 149. -/
def t10j32HighBitTailNode149LhsDen : Nat :=
  64

/-- Exact vector entry for generated row 149. -/
def t10j32HighBitTailNode149Vector : Nat :=
  3084139

/-- Exact cleared-denominator CW inequality for generated row 149. -/
theorem t10j32HighBitTailNode149Bound :
    t10j32HighBitTailNode149LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode149Vector * t10j32HighBitTailNode149LhsDen := by
  norm_num [t10j32HighBitTailNode149LhsNum, t10j32HighBitTailNode149LhsDen, t10j32HighBitTailNode149Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 149. -/
def t10j32HighBitTailNode149Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode149LhsNum
  lhsDen := t10j32HighBitTailNode149LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode149LhsDen]
  vector := t10j32HighBitTailNode149Vector
  vector_pos := by norm_num [t10j32HighBitTailNode149Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode149Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 149. -/
theorem t10j32HighBitTailNode149MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (149 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode149LhsNum : NNReal) / (t10j32HighBitTailNode149LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode149Support,
      t10j32HighBitTailMatrix (149 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (149 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode149Term (14 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (64 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode149Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode149Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode149Support,
          t10j32HighBitTailMatrix (149 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode149Support, t10j32HighBitTailNode149Term dst := by
        simp [t10j32HighBitTailNode149Support, h014]
      _ = (t10j32HighBitTailNode149LhsNum : NNReal) / (t10j32HighBitTailNode149LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode149Support, t10j32HighBitTailNode149Term]
        norm_num [t10j32HighBitTailNode149LhsNum, t10j32HighBitTailNode149LhsDen]

/-- Evaluated row certificate for generated row 149. -/
def t10j32HighBitTailNode149Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (149 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode149Row
  lhs_eq := by simpa using t10j32HighBitTailNode149MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode149Row]


/-- State label for generated row 150. -/
def t10j32HighBitTailNode150Label : String :=
  "v2=9|odd=1|h=2"

/-- Destination support of generated row 150. -/
def t10j32HighBitTailNode150Support : Finset T10J32HighBitTailState :=
  {15}

/-- Exact generated summand values for row 150. -/
noncomputable def t10j32HighBitTailNode150Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 15 => ((6469167 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 150. -/
def t10j32HighBitTailNode150LhsNum : Nat :=
  6469167

/-- Exact denominator of `(M v)_i` for generated row 150. -/
def t10j32HighBitTailNode150LhsDen : Nat :=
  64

/-- Exact vector entry for generated row 150. -/
def t10j32HighBitTailNode150Vector : Nat :=
  3084139

/-- Exact cleared-denominator CW inequality for generated row 150. -/
theorem t10j32HighBitTailNode150Bound :
    t10j32HighBitTailNode150LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode150Vector * t10j32HighBitTailNode150LhsDen := by
  norm_num [t10j32HighBitTailNode150LhsNum, t10j32HighBitTailNode150LhsDen, t10j32HighBitTailNode150Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 150. -/
def t10j32HighBitTailNode150Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode150LhsNum
  lhsDen := t10j32HighBitTailNode150LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode150LhsDen]
  vector := t10j32HighBitTailNode150Vector
  vector_pos := by norm_num [t10j32HighBitTailNode150Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode150Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 150. -/
theorem t10j32HighBitTailNode150MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (150 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode150LhsNum : NNReal) / (t10j32HighBitTailNode150LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode150Support,
      t10j32HighBitTailMatrix (150 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (150 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode150Term (15 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (64 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode150Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode150Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode150Support,
          t10j32HighBitTailMatrix (150 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode150Support, t10j32HighBitTailNode150Term dst := by
        simp [t10j32HighBitTailNode150Support, h015]
      _ = (t10j32HighBitTailNode150LhsNum : NNReal) / (t10j32HighBitTailNode150LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode150Support, t10j32HighBitTailNode150Term]
        norm_num [t10j32HighBitTailNode150LhsNum, t10j32HighBitTailNode150LhsDen]

/-- Evaluated row certificate for generated row 150. -/
def t10j32HighBitTailNode150Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (150 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode150Row
  lhs_eq := by simpa using t10j32HighBitTailNode150MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode150Row]


/-- State label for generated row 151. -/
def t10j32HighBitTailNode151Label : String :=
  "v2=9|odd=1|h=3"

/-- Destination support of generated row 151. -/
def t10j32HighBitTailNode151Support : Finset T10J32HighBitTailState :=
  {12}

/-- Exact generated summand values for row 151. -/
noncomputable def t10j32HighBitTailNode151Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 12 => ((6469167 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 151. -/
def t10j32HighBitTailNode151LhsNum : Nat :=
  6469167

/-- Exact denominator of `(M v)_i` for generated row 151. -/
def t10j32HighBitTailNode151LhsDen : Nat :=
  64

/-- Exact vector entry for generated row 151. -/
def t10j32HighBitTailNode151Vector : Nat :=
  3084139

/-- Exact cleared-denominator CW inequality for generated row 151. -/
theorem t10j32HighBitTailNode151Bound :
    t10j32HighBitTailNode151LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode151Vector * t10j32HighBitTailNode151LhsDen := by
  norm_num [t10j32HighBitTailNode151LhsNum, t10j32HighBitTailNode151LhsDen, t10j32HighBitTailNode151Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 151. -/
def t10j32HighBitTailNode151Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode151LhsNum
  lhsDen := t10j32HighBitTailNode151LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode151LhsDen]
  vector := t10j32HighBitTailNode151Vector
  vector_pos := by norm_num [t10j32HighBitTailNode151Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode151Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 151. -/
theorem t10j32HighBitTailNode151MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (151 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode151LhsNum : NNReal) / (t10j32HighBitTailNode151LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode151Support,
      t10j32HighBitTailMatrix (151 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (151 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode151Term (12 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (64 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode151Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode151Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode151Support,
          t10j32HighBitTailMatrix (151 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode151Support, t10j32HighBitTailNode151Term dst := by
        simp [t10j32HighBitTailNode151Support, h012]
      _ = (t10j32HighBitTailNode151LhsNum : NNReal) / (t10j32HighBitTailNode151LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode151Support, t10j32HighBitTailNode151Term]
        norm_num [t10j32HighBitTailNode151LhsNum, t10j32HighBitTailNode151LhsDen]

/-- Evaluated row certificate for generated row 151. -/
def t10j32HighBitTailNode151Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (151 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode151Row
  lhs_eq := by simpa using t10j32HighBitTailNode151MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode151Row]


/-- State label for generated row 152. -/
def t10j32HighBitTailNode152Label : String :=
  "v2=9|odd=2|h=0"

/-- Destination support of generated row 152. -/
def t10j32HighBitTailNode152Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 152. -/
def t10j32HighBitTailNode152LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 152. -/
def t10j32HighBitTailNode152LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 152. -/
def t10j32HighBitTailNode152Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 152. -/
theorem t10j32HighBitTailNode152Bound :
    t10j32HighBitTailNode152LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode152Vector * t10j32HighBitTailNode152LhsDen := by
  norm_num [t10j32HighBitTailNode152LhsNum, t10j32HighBitTailNode152LhsDen, t10j32HighBitTailNode152Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 152. -/
def t10j32HighBitTailNode152Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode152LhsNum
  lhsDen := t10j32HighBitTailNode152LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode152LhsDen]
  vector := t10j32HighBitTailNode152Vector
  vector_pos := by norm_num [t10j32HighBitTailNode152Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode152Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 152. -/
theorem t10j32HighBitTailNode152MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (152 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode152LhsNum : NNReal) / (t10j32HighBitTailNode152LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode152LhsNum, t10j32HighBitTailNode152LhsDen]

/-- Evaluated row certificate for generated row 152. -/
def t10j32HighBitTailNode152Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (152 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode152Row
  lhs_eq := by simpa using t10j32HighBitTailNode152MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode152Row]


/-- State label for generated row 153. -/
def t10j32HighBitTailNode153Label : String :=
  "v2=9|odd=2|h=1"

/-- Destination support of generated row 153. -/
def t10j32HighBitTailNode153Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 153. -/
def t10j32HighBitTailNode153LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 153. -/
def t10j32HighBitTailNode153LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 153. -/
def t10j32HighBitTailNode153Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 153. -/
theorem t10j32HighBitTailNode153Bound :
    t10j32HighBitTailNode153LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode153Vector * t10j32HighBitTailNode153LhsDen := by
  norm_num [t10j32HighBitTailNode153LhsNum, t10j32HighBitTailNode153LhsDen, t10j32HighBitTailNode153Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 153. -/
def t10j32HighBitTailNode153Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode153LhsNum
  lhsDen := t10j32HighBitTailNode153LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode153LhsDen]
  vector := t10j32HighBitTailNode153Vector
  vector_pos := by norm_num [t10j32HighBitTailNode153Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode153Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 153. -/
theorem t10j32HighBitTailNode153MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (153 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode153LhsNum : NNReal) / (t10j32HighBitTailNode153LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode153LhsNum, t10j32HighBitTailNode153LhsDen]

/-- Evaluated row certificate for generated row 153. -/
def t10j32HighBitTailNode153Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (153 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode153Row
  lhs_eq := by simpa using t10j32HighBitTailNode153MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode153Row]


/-- State label for generated row 154. -/
def t10j32HighBitTailNode154Label : String :=
  "v2=9|odd=2|h=2"

/-- Destination support of generated row 154. -/
def t10j32HighBitTailNode154Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 154. -/
def t10j32HighBitTailNode154LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 154. -/
def t10j32HighBitTailNode154LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 154. -/
def t10j32HighBitTailNode154Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 154. -/
theorem t10j32HighBitTailNode154Bound :
    t10j32HighBitTailNode154LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode154Vector * t10j32HighBitTailNode154LhsDen := by
  norm_num [t10j32HighBitTailNode154LhsNum, t10j32HighBitTailNode154LhsDen, t10j32HighBitTailNode154Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 154. -/
def t10j32HighBitTailNode154Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode154LhsNum
  lhsDen := t10j32HighBitTailNode154LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode154LhsDen]
  vector := t10j32HighBitTailNode154Vector
  vector_pos := by norm_num [t10j32HighBitTailNode154Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode154Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 154. -/
theorem t10j32HighBitTailNode154MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (154 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode154LhsNum : NNReal) / (t10j32HighBitTailNode154LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode154LhsNum, t10j32HighBitTailNode154LhsDen]

/-- Evaluated row certificate for generated row 154. -/
def t10j32HighBitTailNode154Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (154 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode154Row
  lhs_eq := by simpa using t10j32HighBitTailNode154MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode154Row]


/-- State label for generated row 155. -/
def t10j32HighBitTailNode155Label : String :=
  "v2=9|odd=2|h=3"

/-- Destination support of generated row 155. -/
def t10j32HighBitTailNode155Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 155. -/
def t10j32HighBitTailNode155LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 155. -/
def t10j32HighBitTailNode155LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 155. -/
def t10j32HighBitTailNode155Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 155. -/
theorem t10j32HighBitTailNode155Bound :
    t10j32HighBitTailNode155LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode155Vector * t10j32HighBitTailNode155LhsDen := by
  norm_num [t10j32HighBitTailNode155LhsNum, t10j32HighBitTailNode155LhsDen, t10j32HighBitTailNode155Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 155. -/
def t10j32HighBitTailNode155Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode155LhsNum
  lhsDen := t10j32HighBitTailNode155LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode155LhsDen]
  vector := t10j32HighBitTailNode155Vector
  vector_pos := by norm_num [t10j32HighBitTailNode155Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode155Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 155. -/
theorem t10j32HighBitTailNode155MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (155 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode155LhsNum : NNReal) / (t10j32HighBitTailNode155LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode155LhsNum, t10j32HighBitTailNode155LhsDen]

/-- Evaluated row certificate for generated row 155. -/
def t10j32HighBitTailNode155Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (155 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode155Row
  lhs_eq := by simpa using t10j32HighBitTailNode155MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode155Row]


/-- State label for generated row 156. -/
def t10j32HighBitTailNode156Label : String :=
  "v2=9|odd=3|h=0"

/-- Destination support of generated row 156. -/
def t10j32HighBitTailNode156Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 156. -/
def t10j32HighBitTailNode156LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 156. -/
def t10j32HighBitTailNode156LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 156. -/
def t10j32HighBitTailNode156Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 156. -/
theorem t10j32HighBitTailNode156Bound :
    t10j32HighBitTailNode156LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode156Vector * t10j32HighBitTailNode156LhsDen := by
  norm_num [t10j32HighBitTailNode156LhsNum, t10j32HighBitTailNode156LhsDen, t10j32HighBitTailNode156Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 156. -/
def t10j32HighBitTailNode156Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode156LhsNum
  lhsDen := t10j32HighBitTailNode156LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode156LhsDen]
  vector := t10j32HighBitTailNode156Vector
  vector_pos := by norm_num [t10j32HighBitTailNode156Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode156Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 156. -/
theorem t10j32HighBitTailNode156MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (156 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode156LhsNum : NNReal) / (t10j32HighBitTailNode156LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode156LhsNum, t10j32HighBitTailNode156LhsDen]

/-- Evaluated row certificate for generated row 156. -/
def t10j32HighBitTailNode156Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (156 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode156Row
  lhs_eq := by simpa using t10j32HighBitTailNode156MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode156Row]


/-- State label for generated row 157. -/
def t10j32HighBitTailNode157Label : String :=
  "v2=9|odd=3|h=1"

/-- Destination support of generated row 157. -/
def t10j32HighBitTailNode157Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 157. -/
def t10j32HighBitTailNode157LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 157. -/
def t10j32HighBitTailNode157LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 157. -/
def t10j32HighBitTailNode157Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 157. -/
theorem t10j32HighBitTailNode157Bound :
    t10j32HighBitTailNode157LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode157Vector * t10j32HighBitTailNode157LhsDen := by
  norm_num [t10j32HighBitTailNode157LhsNum, t10j32HighBitTailNode157LhsDen, t10j32HighBitTailNode157Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 157. -/
def t10j32HighBitTailNode157Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode157LhsNum
  lhsDen := t10j32HighBitTailNode157LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode157LhsDen]
  vector := t10j32HighBitTailNode157Vector
  vector_pos := by norm_num [t10j32HighBitTailNode157Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode157Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 157. -/
theorem t10j32HighBitTailNode157MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (157 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode157LhsNum : NNReal) / (t10j32HighBitTailNode157LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode157LhsNum, t10j32HighBitTailNode157LhsDen]

/-- Evaluated row certificate for generated row 157. -/
def t10j32HighBitTailNode157Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (157 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode157Row
  lhs_eq := by simpa using t10j32HighBitTailNode157MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode157Row]


/-- State label for generated row 158. -/
def t10j32HighBitTailNode158Label : String :=
  "v2=9|odd=3|h=2"

/-- Destination support of generated row 158. -/
def t10j32HighBitTailNode158Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 158. -/
def t10j32HighBitTailNode158LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 158. -/
def t10j32HighBitTailNode158LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 158. -/
def t10j32HighBitTailNode158Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 158. -/
theorem t10j32HighBitTailNode158Bound :
    t10j32HighBitTailNode158LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode158Vector * t10j32HighBitTailNode158LhsDen := by
  norm_num [t10j32HighBitTailNode158LhsNum, t10j32HighBitTailNode158LhsDen, t10j32HighBitTailNode158Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 158. -/
def t10j32HighBitTailNode158Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode158LhsNum
  lhsDen := t10j32HighBitTailNode158LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode158LhsDen]
  vector := t10j32HighBitTailNode158Vector
  vector_pos := by norm_num [t10j32HighBitTailNode158Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode158Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 158. -/
theorem t10j32HighBitTailNode158MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (158 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode158LhsNum : NNReal) / (t10j32HighBitTailNode158LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode158LhsNum, t10j32HighBitTailNode158LhsDen]

/-- Evaluated row certificate for generated row 158. -/
def t10j32HighBitTailNode158Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (158 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode158Row
  lhs_eq := by simpa using t10j32HighBitTailNode158MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode158Row]


/-- State label for generated row 159. -/
def t10j32HighBitTailNode159Label : String :=
  "v2=9|odd=3|h=3"

/-- Destination support of generated row 159. -/
def t10j32HighBitTailNode159Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 159. -/
def t10j32HighBitTailNode159LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 159. -/
def t10j32HighBitTailNode159LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 159. -/
def t10j32HighBitTailNode159Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 159. -/
theorem t10j32HighBitTailNode159Bound :
    t10j32HighBitTailNode159LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode159Vector * t10j32HighBitTailNode159LhsDen := by
  norm_num [t10j32HighBitTailNode159LhsNum, t10j32HighBitTailNode159LhsDen, t10j32HighBitTailNode159Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 159. -/
def t10j32HighBitTailNode159Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode159LhsNum
  lhsDen := t10j32HighBitTailNode159LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode159LhsDen]
  vector := t10j32HighBitTailNode159Vector
  vector_pos := by norm_num [t10j32HighBitTailNode159Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode159Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 159. -/
theorem t10j32HighBitTailNode159MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (159 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode159LhsNum : NNReal) / (t10j32HighBitTailNode159LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode159LhsNum, t10j32HighBitTailNode159LhsDen]

/-- Evaluated row certificate for generated row 159. -/
def t10j32HighBitTailNode159Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (159 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode159Row
  lhs_eq := by simpa using t10j32HighBitTailNode159MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode159Row]

end Generated
end CollatzShadowing
