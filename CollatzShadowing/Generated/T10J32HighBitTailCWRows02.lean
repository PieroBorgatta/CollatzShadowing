import CollatzShadowing.Generated.T10J32HighBitTailCWData

set_option linter.style.longLine false
set_option linter.style.cdot false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- State label for generated row 32. -/
def t10j32HighBitTailNode032Label : String :=
  "v2=2|odd=0|h=0"

/-- Destination support of generated row 32. -/
def t10j32HighBitTailNode032Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 32. -/
def t10j32HighBitTailNode032LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 32. -/
def t10j32HighBitTailNode032LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 32. -/
def t10j32HighBitTailNode032Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 32. -/
theorem t10j32HighBitTailNode032Bound :
    t10j32HighBitTailNode032LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode032Vector * t10j32HighBitTailNode032LhsDen := by
  norm_num [t10j32HighBitTailNode032LhsNum, t10j32HighBitTailNode032LhsDen, t10j32HighBitTailNode032Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 32. -/
def t10j32HighBitTailNode032Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode032LhsNum
  lhsDen := t10j32HighBitTailNode032LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode032LhsDen]
  vector := t10j32HighBitTailNode032Vector
  vector_pos := by norm_num [t10j32HighBitTailNode032Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode032Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 32. -/
theorem t10j32HighBitTailNode032MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (32 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode032LhsNum : NNReal) / (t10j32HighBitTailNode032LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode032LhsNum, t10j32HighBitTailNode032LhsDen]

/-- Evaluated row certificate for generated row 32. -/
def t10j32HighBitTailNode032Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (32 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode032Row
  lhs_eq := by simpa using t10j32HighBitTailNode032MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode032Row]


/-- State label for generated row 33. -/
def t10j32HighBitTailNode033Label : String :=
  "v2=2|odd=0|h=1"

/-- Destination support of generated row 33. -/
def t10j32HighBitTailNode033Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 33. -/
def t10j32HighBitTailNode033LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 33. -/
def t10j32HighBitTailNode033LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 33. -/
def t10j32HighBitTailNode033Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 33. -/
theorem t10j32HighBitTailNode033Bound :
    t10j32HighBitTailNode033LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode033Vector * t10j32HighBitTailNode033LhsDen := by
  norm_num [t10j32HighBitTailNode033LhsNum, t10j32HighBitTailNode033LhsDen, t10j32HighBitTailNode033Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 33. -/
def t10j32HighBitTailNode033Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode033LhsNum
  lhsDen := t10j32HighBitTailNode033LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode033LhsDen]
  vector := t10j32HighBitTailNode033Vector
  vector_pos := by norm_num [t10j32HighBitTailNode033Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode033Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 33. -/
theorem t10j32HighBitTailNode033MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (33 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode033LhsNum : NNReal) / (t10j32HighBitTailNode033LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode033LhsNum, t10j32HighBitTailNode033LhsDen]

/-- Evaluated row certificate for generated row 33. -/
def t10j32HighBitTailNode033Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (33 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode033Row
  lhs_eq := by simpa using t10j32HighBitTailNode033MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode033Row]


/-- State label for generated row 34. -/
def t10j32HighBitTailNode034Label : String :=
  "v2=2|odd=0|h=2"

/-- Destination support of generated row 34. -/
def t10j32HighBitTailNode034Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 34. -/
def t10j32HighBitTailNode034LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 34. -/
def t10j32HighBitTailNode034LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 34. -/
def t10j32HighBitTailNode034Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 34. -/
theorem t10j32HighBitTailNode034Bound :
    t10j32HighBitTailNode034LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode034Vector * t10j32HighBitTailNode034LhsDen := by
  norm_num [t10j32HighBitTailNode034LhsNum, t10j32HighBitTailNode034LhsDen, t10j32HighBitTailNode034Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 34. -/
def t10j32HighBitTailNode034Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode034LhsNum
  lhsDen := t10j32HighBitTailNode034LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode034LhsDen]
  vector := t10j32HighBitTailNode034Vector
  vector_pos := by norm_num [t10j32HighBitTailNode034Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode034Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 34. -/
theorem t10j32HighBitTailNode034MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (34 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode034LhsNum : NNReal) / (t10j32HighBitTailNode034LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode034LhsNum, t10j32HighBitTailNode034LhsDen]

/-- Evaluated row certificate for generated row 34. -/
def t10j32HighBitTailNode034Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (34 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode034Row
  lhs_eq := by simpa using t10j32HighBitTailNode034MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode034Row]


/-- State label for generated row 35. -/
def t10j32HighBitTailNode035Label : String :=
  "v2=2|odd=0|h=3"

/-- Destination support of generated row 35. -/
def t10j32HighBitTailNode035Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 35. -/
def t10j32HighBitTailNode035LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 35. -/
def t10j32HighBitTailNode035LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 35. -/
def t10j32HighBitTailNode035Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 35. -/
theorem t10j32HighBitTailNode035Bound :
    t10j32HighBitTailNode035LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode035Vector * t10j32HighBitTailNode035LhsDen := by
  norm_num [t10j32HighBitTailNode035LhsNum, t10j32HighBitTailNode035LhsDen, t10j32HighBitTailNode035Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 35. -/
def t10j32HighBitTailNode035Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode035LhsNum
  lhsDen := t10j32HighBitTailNode035LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode035LhsDen]
  vector := t10j32HighBitTailNode035Vector
  vector_pos := by norm_num [t10j32HighBitTailNode035Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode035Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 35. -/
theorem t10j32HighBitTailNode035MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (35 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode035LhsNum : NNReal) / (t10j32HighBitTailNode035LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode035LhsNum, t10j32HighBitTailNode035LhsDen]

/-- Evaluated row certificate for generated row 35. -/
def t10j32HighBitTailNode035Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (35 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode035Row
  lhs_eq := by simpa using t10j32HighBitTailNode035MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode035Row]


/-- State label for generated row 36. -/
def t10j32HighBitTailNode036Label : String :=
  "v2=2|odd=1|h=0"

/-- Destination support of generated row 36. -/
def t10j32HighBitTailNode036Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 37, 45, 53, 61, 77, 101, 117, 133}

/-- Exact generated summand values for row 36. -/
noncomputable def t10j32HighBitTailNode036Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((7462819 : NNReal) / (1024 : NNReal))
  | 13 => ((3184986553 : NNReal) / (524288 : NNReal))
  | 21 => ((857537889 : NNReal) / (262144 : NNReal))
  | 29 => ((201477675 : NNReal) / (65536 : NNReal))
  | 37 => ((4722957 : NNReal) / (16384 : NNReal))
  | 45 => ((37977417 : NNReal) / (8192 : NNReal))
  | 53 => ((63127215 : NNReal) / (32768 : NNReal))
  | 61 => ((958247 : NNReal) / (4096 : NNReal))
  | 77 => ((140625 : NNReal) / (512 : NNReal))
  | 101 => ((239597 : NNReal) / (512 : NNReal))
  | 117 => ((2448779 : NNReal) / (32768 : NNReal))
  | 133 => ((15625 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 36. -/
def t10j32HighBitTailNode036LhsNum : Nat :=
  14603755219

/-- Exact denominator of `(M v)_i` for generated row 36. -/
def t10j32HighBitTailNode036LhsDen : Nat :=
  524288

/-- Exact vector entry for generated row 36. -/
def t10j32HighBitTailNode036Vector : Nat :=
  1574319

/-- Exact cleared-denominator CW inequality for generated row 36. -/
theorem t10j32HighBitTailNode036Bound :
    t10j32HighBitTailNode036LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode036Vector * t10j32HighBitTailNode036LhsDen := by
  norm_num [t10j32HighBitTailNode036LhsNum, t10j32HighBitTailNode036LhsDen, t10j32HighBitTailNode036Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 36. -/
def t10j32HighBitTailNode036Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode036LhsNum
  lhsDen := t10j32HighBitTailNode036LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode036LhsDen]
  vector := t10j32HighBitTailNode036Vector
  vector_pos := by norm_num [t10j32HighBitTailNode036Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode036Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 36. -/
theorem t10j32HighBitTailNode036MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (36 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode036LhsNum : NNReal) / (t10j32HighBitTailNode036LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode036Support,
      t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (5 : T10J32HighBitTailState) := by
      change (((91 : NNReal) / (32768 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode036Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h013 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (13 : T10J32HighBitTailState) := by
      change (((1477 : NNReal) / (524288 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode036Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h021 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (21 : T10J32HighBitTailState) := by
      change (((611 : NNReal) / (262144 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode036Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h029 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (29 : T10J32HighBitTailState) := by
      change (((105 : NNReal) / (65536 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode036Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h037 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (37 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (37 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (37 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode036Term (37 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h045 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (45 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (45 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (45 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode036Term (45 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h053 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (53 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (53 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (53 : T10J32HighBitTailState) := by
      change (((57 : NNReal) / (65536 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode036Term (53 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h061 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (61 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (61 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (61 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode036Term (61 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h077 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (77 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (77 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (77 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode036Term (77 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h101 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (101 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (101 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (101 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode036Term (101 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h117 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (117 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (117 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (117 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode036Term (117 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    have h133 :
        t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) (133 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (133 : T10J32HighBitTailState) =
          t10j32HighBitTailNode036Term (133 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode036Term (133 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode036Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode036Support,
          t10j32HighBitTailMatrix (36 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode036Support, t10j32HighBitTailNode036Term dst := by
        simp [t10j32HighBitTailNode036Support, h005, h013, h021, h029, h037, h045, h053, h061, h077, h101, h117, h133]
      _ = (t10j32HighBitTailNode036LhsNum : NNReal) / (t10j32HighBitTailNode036LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode036Support, t10j32HighBitTailNode036Term]
        norm_num [t10j32HighBitTailNode036LhsNum, t10j32HighBitTailNode036LhsDen]

/-- Evaluated row certificate for generated row 36. -/
def t10j32HighBitTailNode036Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (36 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode036Row
  lhs_eq := by simpa using t10j32HighBitTailNode036MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode036Row]


/-- State label for generated row 37. -/
def t10j32HighBitTailNode037Label : String :=
  "v2=2|odd=1|h=1"

/-- Destination support of generated row 37. -/
def t10j32HighBitTailNode037Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 38, 46, 54, 62, 78, 102, 118, 134}

/-- Exact generated summand values for row 37. -/
noncomputable def t10j32HighBitTailNode037Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((7462819 : NNReal) / (1024 : NNReal))
  | 14 => ((3184986553 : NNReal) / (524288 : NNReal))
  | 22 => ((857537889 : NNReal) / (262144 : NNReal))
  | 30 => ((201477675 : NNReal) / (65536 : NNReal))
  | 38 => ((4722957 : NNReal) / (16384 : NNReal))
  | 46 => ((37977417 : NNReal) / (8192 : NNReal))
  | 54 => ((63127215 : NNReal) / (32768 : NNReal))
  | 62 => ((958247 : NNReal) / (4096 : NNReal))
  | 78 => ((140625 : NNReal) / (512 : NNReal))
  | 102 => ((239597 : NNReal) / (512 : NNReal))
  | 118 => ((2448779 : NNReal) / (32768 : NNReal))
  | 134 => ((15625 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 37. -/
def t10j32HighBitTailNode037LhsNum : Nat :=
  14603755219

/-- Exact denominator of `(M v)_i` for generated row 37. -/
def t10j32HighBitTailNode037LhsDen : Nat :=
  524288

/-- Exact vector entry for generated row 37. -/
def t10j32HighBitTailNode037Vector : Nat :=
  1574319

/-- Exact cleared-denominator CW inequality for generated row 37. -/
theorem t10j32HighBitTailNode037Bound :
    t10j32HighBitTailNode037LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode037Vector * t10j32HighBitTailNode037LhsDen := by
  norm_num [t10j32HighBitTailNode037LhsNum, t10j32HighBitTailNode037LhsDen, t10j32HighBitTailNode037Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 37. -/
def t10j32HighBitTailNode037Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode037LhsNum
  lhsDen := t10j32HighBitTailNode037LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode037LhsDen]
  vector := t10j32HighBitTailNode037Vector
  vector_pos := by norm_num [t10j32HighBitTailNode037Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode037Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 37. -/
theorem t10j32HighBitTailNode037MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (37 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode037LhsNum : NNReal) / (t10j32HighBitTailNode037LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode037Support,
      t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (6 : T10J32HighBitTailState) := by
      change (((91 : NNReal) / (32768 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode037Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h014 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (14 : T10J32HighBitTailState) := by
      change (((1477 : NNReal) / (524288 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode037Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h022 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (22 : T10J32HighBitTailState) := by
      change (((611 : NNReal) / (262144 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode037Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h030 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (30 : T10J32HighBitTailState) := by
      change (((105 : NNReal) / (65536 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode037Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h038 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (38 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (38 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (38 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode037Term (38 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h046 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (46 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (46 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (46 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode037Term (46 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h054 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (54 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (54 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (54 : T10J32HighBitTailState) := by
      change (((57 : NNReal) / (65536 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode037Term (54 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h062 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (62 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (62 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (62 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode037Term (62 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h078 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (78 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (78 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (78 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode037Term (78 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h102 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (102 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (102 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (102 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode037Term (102 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h118 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (118 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (118 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (118 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode037Term (118 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    have h134 :
        t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) (134 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (134 : T10J32HighBitTailState) =
          t10j32HighBitTailNode037Term (134 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode037Term (134 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode037Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode037Support,
          t10j32HighBitTailMatrix (37 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode037Support, t10j32HighBitTailNode037Term dst := by
        simp [t10j32HighBitTailNode037Support, h006, h014, h022, h030, h038, h046, h054, h062, h078, h102, h118, h134]
      _ = (t10j32HighBitTailNode037LhsNum : NNReal) / (t10j32HighBitTailNode037LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode037Support, t10j32HighBitTailNode037Term]
        norm_num [t10j32HighBitTailNode037LhsNum, t10j32HighBitTailNode037LhsDen]

/-- Evaluated row certificate for generated row 37. -/
def t10j32HighBitTailNode037Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (37 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode037Row
  lhs_eq := by simpa using t10j32HighBitTailNode037MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode037Row]


/-- State label for generated row 38. -/
def t10j32HighBitTailNode038Label : String :=
  "v2=2|odd=1|h=2"

/-- Destination support of generated row 38. -/
def t10j32HighBitTailNode038Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 39, 47, 55, 63, 79, 103, 119, 135}

/-- Exact generated summand values for row 38. -/
noncomputable def t10j32HighBitTailNode038Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((7462819 : NNReal) / (1024 : NNReal))
  | 15 => ((3184986553 : NNReal) / (524288 : NNReal))
  | 23 => ((857537889 : NNReal) / (262144 : NNReal))
  | 31 => ((201477675 : NNReal) / (65536 : NNReal))
  | 39 => ((4722957 : NNReal) / (16384 : NNReal))
  | 47 => ((37977417 : NNReal) / (8192 : NNReal))
  | 55 => ((63127215 : NNReal) / (32768 : NNReal))
  | 63 => ((958247 : NNReal) / (4096 : NNReal))
  | 79 => ((140625 : NNReal) / (512 : NNReal))
  | 103 => ((239597 : NNReal) / (512 : NNReal))
  | 119 => ((2448779 : NNReal) / (32768 : NNReal))
  | 135 => ((15625 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 38. -/
def t10j32HighBitTailNode038LhsNum : Nat :=
  14603755219

/-- Exact denominator of `(M v)_i` for generated row 38. -/
def t10j32HighBitTailNode038LhsDen : Nat :=
  524288

/-- Exact vector entry for generated row 38. -/
def t10j32HighBitTailNode038Vector : Nat :=
  1574319

/-- Exact cleared-denominator CW inequality for generated row 38. -/
theorem t10j32HighBitTailNode038Bound :
    t10j32HighBitTailNode038LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode038Vector * t10j32HighBitTailNode038LhsDen := by
  norm_num [t10j32HighBitTailNode038LhsNum, t10j32HighBitTailNode038LhsDen, t10j32HighBitTailNode038Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 38. -/
def t10j32HighBitTailNode038Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode038LhsNum
  lhsDen := t10j32HighBitTailNode038LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode038LhsDen]
  vector := t10j32HighBitTailNode038Vector
  vector_pos := by norm_num [t10j32HighBitTailNode038Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode038Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 38. -/
theorem t10j32HighBitTailNode038MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (38 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode038LhsNum : NNReal) / (t10j32HighBitTailNode038LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode038Support,
      t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (7 : T10J32HighBitTailState) := by
      change (((91 : NNReal) / (32768 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode038Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h015 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (15 : T10J32HighBitTailState) := by
      change (((1477 : NNReal) / (524288 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode038Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h023 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (23 : T10J32HighBitTailState) := by
      change (((611 : NNReal) / (262144 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode038Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h031 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (31 : T10J32HighBitTailState) := by
      change (((105 : NNReal) / (65536 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode038Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h039 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (39 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (39 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (39 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode038Term (39 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h047 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (47 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (47 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (47 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode038Term (47 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h055 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (55 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (55 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (55 : T10J32HighBitTailState) := by
      change (((57 : NNReal) / (65536 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode038Term (55 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h063 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (63 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (63 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (63 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode038Term (63 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h079 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (79 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (79 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (79 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode038Term (79 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h103 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (103 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (103 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (103 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode038Term (103 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h119 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (119 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (119 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (119 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode038Term (119 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    have h135 :
        t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) (135 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (135 : T10J32HighBitTailState) =
          t10j32HighBitTailNode038Term (135 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode038Term (135 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode038Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode038Support,
          t10j32HighBitTailMatrix (38 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode038Support, t10j32HighBitTailNode038Term dst := by
        simp [t10j32HighBitTailNode038Support, h007, h015, h023, h031, h039, h047, h055, h063, h079, h103, h119, h135]
      _ = (t10j32HighBitTailNode038LhsNum : NNReal) / (t10j32HighBitTailNode038LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode038Support, t10j32HighBitTailNode038Term]
        norm_num [t10j32HighBitTailNode038LhsNum, t10j32HighBitTailNode038LhsDen]

/-- Evaluated row certificate for generated row 38. -/
def t10j32HighBitTailNode038Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (38 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode038Row
  lhs_eq := by simpa using t10j32HighBitTailNode038MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode038Row]


/-- State label for generated row 39. -/
def t10j32HighBitTailNode039Label : String :=
  "v2=2|odd=1|h=3"

/-- Destination support of generated row 39. -/
def t10j32HighBitTailNode039Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 36, 44, 52, 60, 76, 100, 116, 132}

/-- Exact generated summand values for row 39. -/
noncomputable def t10j32HighBitTailNode039Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((7462819 : NNReal) / (1024 : NNReal))
  | 12 => ((3184986553 : NNReal) / (524288 : NNReal))
  | 20 => ((857537889 : NNReal) / (262144 : NNReal))
  | 28 => ((201477675 : NNReal) / (65536 : NNReal))
  | 36 => ((4722957 : NNReal) / (16384 : NNReal))
  | 44 => ((37977417 : NNReal) / (8192 : NNReal))
  | 52 => ((63127215 : NNReal) / (32768 : NNReal))
  | 60 => ((958247 : NNReal) / (4096 : NNReal))
  | 76 => ((140625 : NNReal) / (512 : NNReal))
  | 100 => ((239597 : NNReal) / (512 : NNReal))
  | 116 => ((2448779 : NNReal) / (32768 : NNReal))
  | 132 => ((15625 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 39. -/
def t10j32HighBitTailNode039LhsNum : Nat :=
  14603755219

/-- Exact denominator of `(M v)_i` for generated row 39. -/
def t10j32HighBitTailNode039LhsDen : Nat :=
  524288

/-- Exact vector entry for generated row 39. -/
def t10j32HighBitTailNode039Vector : Nat :=
  1574319

/-- Exact cleared-denominator CW inequality for generated row 39. -/
theorem t10j32HighBitTailNode039Bound :
    t10j32HighBitTailNode039LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode039Vector * t10j32HighBitTailNode039LhsDen := by
  norm_num [t10j32HighBitTailNode039LhsNum, t10j32HighBitTailNode039LhsDen, t10j32HighBitTailNode039Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 39. -/
def t10j32HighBitTailNode039Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode039LhsNum
  lhsDen := t10j32HighBitTailNode039LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode039LhsDen]
  vector := t10j32HighBitTailNode039Vector
  vector_pos := by norm_num [t10j32HighBitTailNode039Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode039Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 39. -/
theorem t10j32HighBitTailNode039MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (39 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode039LhsNum : NNReal) / (t10j32HighBitTailNode039LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode039Support,
      t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (4 : T10J32HighBitTailState) := by
      change (((91 : NNReal) / (32768 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode039Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h012 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (12 : T10J32HighBitTailState) := by
      change (((1477 : NNReal) / (524288 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode039Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h020 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (20 : T10J32HighBitTailState) := by
      change (((611 : NNReal) / (262144 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode039Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h028 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (28 : T10J32HighBitTailState) := by
      change (((105 : NNReal) / (65536 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode039Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h036 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (36 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (36 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (36 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (16384 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode039Term (36 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h044 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (44 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (44 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (44 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (8192 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode039Term (44 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h052 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (52 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (52 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (52 : T10J32HighBitTailState) := by
      change (((57 : NNReal) / (65536 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode039Term (52 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h060 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (60 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (60 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (60 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode039Term (60 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h076 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (76 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (76 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (76 : T10J32HighBitTailState) := by
      change (((9 : NNReal) / (32768 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode039Term (76 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h100 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (100 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (100 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (100 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode039Term (100 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h116 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (116 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (116 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (116 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (32768 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode039Term (116 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    have h132 :
        t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) (132 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (132 : T10J32HighBitTailState) =
          t10j32HighBitTailNode039Term (132 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode039Term (132 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode039Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode039Support,
          t10j32HighBitTailMatrix (39 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode039Support, t10j32HighBitTailNode039Term dst := by
        simp [t10j32HighBitTailNode039Support, h004, h012, h020, h028, h036, h044, h052, h060, h076, h100, h116, h132]
      _ = (t10j32HighBitTailNode039LhsNum : NNReal) / (t10j32HighBitTailNode039LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode039Support, t10j32HighBitTailNode039Term]
        norm_num [t10j32HighBitTailNode039LhsNum, t10j32HighBitTailNode039LhsDen]

/-- Evaluated row certificate for generated row 39. -/
def t10j32HighBitTailNode039Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (39 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode039Row
  lhs_eq := by simpa using t10j32HighBitTailNode039MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode039Row]


/-- State label for generated row 40. -/
def t10j32HighBitTailNode040Label : String :=
  "v2=2|odd=2|h=0"

/-- Destination support of generated row 40. -/
def t10j32HighBitTailNode040Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 40. -/
def t10j32HighBitTailNode040LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 40. -/
def t10j32HighBitTailNode040LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 40. -/
def t10j32HighBitTailNode040Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 40. -/
theorem t10j32HighBitTailNode040Bound :
    t10j32HighBitTailNode040LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode040Vector * t10j32HighBitTailNode040LhsDen := by
  norm_num [t10j32HighBitTailNode040LhsNum, t10j32HighBitTailNode040LhsDen, t10j32HighBitTailNode040Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 40. -/
def t10j32HighBitTailNode040Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode040LhsNum
  lhsDen := t10j32HighBitTailNode040LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode040LhsDen]
  vector := t10j32HighBitTailNode040Vector
  vector_pos := by norm_num [t10j32HighBitTailNode040Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode040Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 40. -/
theorem t10j32HighBitTailNode040MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (40 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode040LhsNum : NNReal) / (t10j32HighBitTailNode040LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode040LhsNum, t10j32HighBitTailNode040LhsDen]

/-- Evaluated row certificate for generated row 40. -/
def t10j32HighBitTailNode040Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (40 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode040Row
  lhs_eq := by simpa using t10j32HighBitTailNode040MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode040Row]


/-- State label for generated row 41. -/
def t10j32HighBitTailNode041Label : String :=
  "v2=2|odd=2|h=1"

/-- Destination support of generated row 41. -/
def t10j32HighBitTailNode041Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 41. -/
def t10j32HighBitTailNode041LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 41. -/
def t10j32HighBitTailNode041LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 41. -/
def t10j32HighBitTailNode041Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 41. -/
theorem t10j32HighBitTailNode041Bound :
    t10j32HighBitTailNode041LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode041Vector * t10j32HighBitTailNode041LhsDen := by
  norm_num [t10j32HighBitTailNode041LhsNum, t10j32HighBitTailNode041LhsDen, t10j32HighBitTailNode041Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 41. -/
def t10j32HighBitTailNode041Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode041LhsNum
  lhsDen := t10j32HighBitTailNode041LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode041LhsDen]
  vector := t10j32HighBitTailNode041Vector
  vector_pos := by norm_num [t10j32HighBitTailNode041Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode041Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 41. -/
theorem t10j32HighBitTailNode041MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (41 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode041LhsNum : NNReal) / (t10j32HighBitTailNode041LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode041LhsNum, t10j32HighBitTailNode041LhsDen]

/-- Evaluated row certificate for generated row 41. -/
def t10j32HighBitTailNode041Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (41 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode041Row
  lhs_eq := by simpa using t10j32HighBitTailNode041MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode041Row]


/-- State label for generated row 42. -/
def t10j32HighBitTailNode042Label : String :=
  "v2=2|odd=2|h=2"

/-- Destination support of generated row 42. -/
def t10j32HighBitTailNode042Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 42. -/
def t10j32HighBitTailNode042LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 42. -/
def t10j32HighBitTailNode042LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 42. -/
def t10j32HighBitTailNode042Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 42. -/
theorem t10j32HighBitTailNode042Bound :
    t10j32HighBitTailNode042LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode042Vector * t10j32HighBitTailNode042LhsDen := by
  norm_num [t10j32HighBitTailNode042LhsNum, t10j32HighBitTailNode042LhsDen, t10j32HighBitTailNode042Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 42. -/
def t10j32HighBitTailNode042Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode042LhsNum
  lhsDen := t10j32HighBitTailNode042LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode042LhsDen]
  vector := t10j32HighBitTailNode042Vector
  vector_pos := by norm_num [t10j32HighBitTailNode042Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode042Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 42. -/
theorem t10j32HighBitTailNode042MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (42 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode042LhsNum : NNReal) / (t10j32HighBitTailNode042LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode042LhsNum, t10j32HighBitTailNode042LhsDen]

/-- Evaluated row certificate for generated row 42. -/
def t10j32HighBitTailNode042Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (42 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode042Row
  lhs_eq := by simpa using t10j32HighBitTailNode042MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode042Row]


/-- State label for generated row 43. -/
def t10j32HighBitTailNode043Label : String :=
  "v2=2|odd=2|h=3"

/-- Destination support of generated row 43. -/
def t10j32HighBitTailNode043Support : Finset T10J32HighBitTailState :=
  {}


/-- Exact numerator of `(M v)_i` for generated row 43. -/
def t10j32HighBitTailNode043LhsNum : Nat :=
  0

/-- Exact denominator of `(M v)_i` for generated row 43. -/
def t10j32HighBitTailNode043LhsDen : Nat :=
  1

/-- Exact vector entry for generated row 43. -/
def t10j32HighBitTailNode043Vector : Nat :=
  1000000

/-- Exact cleared-denominator CW inequality for generated row 43. -/
theorem t10j32HighBitTailNode043Bound :
    t10j32HighBitTailNode043LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode043Vector * t10j32HighBitTailNode043LhsDen := by
  norm_num [t10j32HighBitTailNode043LhsNum, t10j32HighBitTailNode043LhsDen, t10j32HighBitTailNode043Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 43. -/
def t10j32HighBitTailNode043Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode043LhsNum
  lhsDen := t10j32HighBitTailNode043LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode043LhsDen]
  vector := t10j32HighBitTailNode043Vector
  vector_pos := by norm_num [t10j32HighBitTailNode043Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode043Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 43. -/
theorem t10j32HighBitTailNode043MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (43 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode043LhsNum : NNReal) / (t10j32HighBitTailNode043LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans (0 : NNReal)
  · exact Finset.sum_eq_zero (by
      intro dst _hdst
      change (0 : NNReal) * _ = 0
      norm_num)
  · norm_num [t10j32HighBitTailNode043LhsNum, t10j32HighBitTailNode043LhsDen]

/-- Evaluated row certificate for generated row 43. -/
def t10j32HighBitTailNode043Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (43 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode043Row
  lhs_eq := by simpa using t10j32HighBitTailNode043MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode043Row]


/-- State label for generated row 44. -/
def t10j32HighBitTailNode044Label : String :=
  "v2=2|odd=3|h=0"

/-- Destination support of generated row 44. -/
def t10j32HighBitTailNode044Support : Finset T10J32HighBitTailState :=
  {5, 13, 21, 29, 37, 45, 53, 61, 69, 77, 85, 93, 101, 109, 117, 125, 133, 141, 157, 197}

/-- Exact generated summand values for row 44. -/
noncomputable def t10j32HighBitTailNode044Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 5 => ((282028951 : NNReal) / (2048 : NNReal))
  | 13 => ((14467213801 : NNReal) / (131072 : NNReal))
  | 21 => ((2437877763 : NNReal) / (65536 : NNReal))
  | 29 => ((3302315035 : NNReal) / (65536 : NNReal))
  | 37 => ((687977403 : NNReal) / (32768 : NNReal))
  | 45 => ((5430770631 : NNReal) / (32768 : NNReal))
  | 53 => ((218176515 : NNReal) / (16384 : NNReal))
  | 61 => ((104448923 : NNReal) / (8192 : NNReal))
  | 69 => ((859375 : NNReal) / (256 : NNReal))
  | 77 => ((953125 : NNReal) / (256 : NNReal))
  | 85 => ((23844431 : NNReal) / (8192 : NNReal))
  | 93 => ((46875 : NNReal) / (32 : NNReal))
  | 101 => ((718791 : NNReal) / (512 : NNReal))
  | 109 => ((109375 : NNReal) / (128 : NNReal))
  | 117 => ((12243895 : NNReal) / (8192 : NNReal))
  | 125 => ((1915527 : NNReal) / (2048 : NNReal))
  | 133 => ((15625 : NNReal) / (128 : NNReal))
  | 141 => ((15625 : NNReal) / (64 : NNReal))
  | 157 => ((15625 : NNReal) / (64 : NNReal))
  | 197 => ((15625 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 44. -/
def t10j32HighBitTailNode044LhsNum : Nat :=
  74117056725

/-- Exact denominator of `(M v)_i` for generated row 44. -/
def t10j32HighBitTailNode044LhsDen : Nat :=
  131072

/-- Exact vector entry for generated row 44. -/
def t10j32HighBitTailNode044Vector : Nat :=
  12659139

/-- Exact cleared-denominator CW inequality for generated row 44. -/
theorem t10j32HighBitTailNode044Bound :
    t10j32HighBitTailNode044LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode044Vector * t10j32HighBitTailNode044LhsDen := by
  norm_num [t10j32HighBitTailNode044LhsNum, t10j32HighBitTailNode044LhsDen, t10j32HighBitTailNode044Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 44. -/
def t10j32HighBitTailNode044Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode044LhsNum
  lhsDen := t10j32HighBitTailNode044LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode044LhsDen]
  vector := t10j32HighBitTailNode044Vector
  vector_pos := by norm_num [t10j32HighBitTailNode044Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode044Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 44. -/
theorem t10j32HighBitTailNode044MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (44 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode044LhsNum : NNReal) / (t10j32HighBitTailNode044LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode044Support,
      t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (5 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (5 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (5 : T10J32HighBitTailState) := by
      change (((3439 : NNReal) / (65536 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode044Term (5 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h013 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (13 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (13 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (13 : T10J32HighBitTailState) := by
      change (((6709 : NNReal) / (131072 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode044Term (13 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h021 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (21 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (21 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (21 : T10J32HighBitTailState) := by
      change (((1737 : NNReal) / (65536 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode044Term (21 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h029 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (29 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (29 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (29 : T10J32HighBitTailState) := by
      change (((1721 : NNReal) / (65536 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode044Term (29 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h037 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (37 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (37 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (37 : T10J32HighBitTailState) := by
      change (((437 : NNReal) / (32768 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode044Term (37 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h045 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (45 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (45 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (45 : T10J32HighBitTailState) := by
      change (((429 : NNReal) / (32768 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode044Term (45 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h053 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (53 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (53 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (53 : T10J32HighBitTailState) := by
      change (((197 : NNReal) / (32768 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode044Term (53 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h061 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (61 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (61 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (61 : T10J32HighBitTailState) := by
      change (((109 : NNReal) / (16384 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode044Term (61 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h069 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (69 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (69 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (69 : T10J32HighBitTailState) := by
      change (((55 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode044Term (69 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h077 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (77 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (77 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (77 : T10J32HighBitTailState) := by
      change (((61 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode044Term (77 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h085 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (85 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (85 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (85 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (8192 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode044Term (85 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h093 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (93 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (93 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (93 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (2048 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode044Term (93 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h101 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (101 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (101 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (101 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode044Term (101 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h109 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (109 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (109 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (109 : T10J32HighBitTailState) := by
      change (((7 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode044Term (109 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h117 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (117 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (117 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (117 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (8192 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode044Term (117 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h125 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (125 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (125 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (125 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (2048 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode044Term (125 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h133 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (133 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (133 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (133 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode044Term (133 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h141 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (141 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (141 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (141 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode044Term (141 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h157 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (157 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (157 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (157 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode044Term (157 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    have h197 :
        t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) (197 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (197 : T10J32HighBitTailState) =
          t10j32HighBitTailNode044Term (197 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode044Term (197 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode044Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode044Support,
          t10j32HighBitTailMatrix (44 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode044Support, t10j32HighBitTailNode044Term dst := by
        simp [t10j32HighBitTailNode044Support, h005, h013, h021, h029, h037, h045, h053, h061, h069, h077, h085, h093, h101, h109, h117, h125, h133, h141, h157, h197]
      _ = (t10j32HighBitTailNode044LhsNum : NNReal) / (t10j32HighBitTailNode044LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode044Support, t10j32HighBitTailNode044Term]
        norm_num [t10j32HighBitTailNode044LhsNum, t10j32HighBitTailNode044LhsDen]

/-- Evaluated row certificate for generated row 44. -/
def t10j32HighBitTailNode044Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (44 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode044Row
  lhs_eq := by simpa using t10j32HighBitTailNode044MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode044Row]


/-- State label for generated row 45. -/
def t10j32HighBitTailNode045Label : String :=
  "v2=2|odd=3|h=1"

/-- Destination support of generated row 45. -/
def t10j32HighBitTailNode045Support : Finset T10J32HighBitTailState :=
  {6, 14, 22, 30, 38, 46, 54, 62, 70, 78, 86, 94, 102, 110, 118, 126, 134, 142, 158, 198}

/-- Exact generated summand values for row 45. -/
noncomputable def t10j32HighBitTailNode045Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 6 => ((282028951 : NNReal) / (2048 : NNReal))
  | 14 => ((14467213801 : NNReal) / (131072 : NNReal))
  | 22 => ((2437877763 : NNReal) / (65536 : NNReal))
  | 30 => ((3302315035 : NNReal) / (65536 : NNReal))
  | 38 => ((687977403 : NNReal) / (32768 : NNReal))
  | 46 => ((5430770631 : NNReal) / (32768 : NNReal))
  | 54 => ((218176515 : NNReal) / (16384 : NNReal))
  | 62 => ((104448923 : NNReal) / (8192 : NNReal))
  | 70 => ((859375 : NNReal) / (256 : NNReal))
  | 78 => ((953125 : NNReal) / (256 : NNReal))
  | 86 => ((23844431 : NNReal) / (8192 : NNReal))
  | 94 => ((46875 : NNReal) / (32 : NNReal))
  | 102 => ((718791 : NNReal) / (512 : NNReal))
  | 110 => ((109375 : NNReal) / (128 : NNReal))
  | 118 => ((12243895 : NNReal) / (8192 : NNReal))
  | 126 => ((1915527 : NNReal) / (2048 : NNReal))
  | 134 => ((15625 : NNReal) / (128 : NNReal))
  | 142 => ((15625 : NNReal) / (64 : NNReal))
  | 158 => ((15625 : NNReal) / (64 : NNReal))
  | 198 => ((15625 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 45. -/
def t10j32HighBitTailNode045LhsNum : Nat :=
  74117056725

/-- Exact denominator of `(M v)_i` for generated row 45. -/
def t10j32HighBitTailNode045LhsDen : Nat :=
  131072

/-- Exact vector entry for generated row 45. -/
def t10j32HighBitTailNode045Vector : Nat :=
  12659139

/-- Exact cleared-denominator CW inequality for generated row 45. -/
theorem t10j32HighBitTailNode045Bound :
    t10j32HighBitTailNode045LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode045Vector * t10j32HighBitTailNode045LhsDen := by
  norm_num [t10j32HighBitTailNode045LhsNum, t10j32HighBitTailNode045LhsDen, t10j32HighBitTailNode045Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 45. -/
def t10j32HighBitTailNode045Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode045LhsNum
  lhsDen := t10j32HighBitTailNode045LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode045LhsDen]
  vector := t10j32HighBitTailNode045Vector
  vector_pos := by norm_num [t10j32HighBitTailNode045Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode045Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 45. -/
theorem t10j32HighBitTailNode045MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (45 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode045LhsNum : NNReal) / (t10j32HighBitTailNode045LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode045Support,
      t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (6 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (6 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (6 : T10J32HighBitTailState) := by
      change (((3439 : NNReal) / (65536 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode045Term (6 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h014 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (14 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (14 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (14 : T10J32HighBitTailState) := by
      change (((6709 : NNReal) / (131072 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode045Term (14 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h022 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (22 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (22 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (22 : T10J32HighBitTailState) := by
      change (((1737 : NNReal) / (65536 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode045Term (22 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h030 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (30 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (30 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (30 : T10J32HighBitTailState) := by
      change (((1721 : NNReal) / (65536 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode045Term (30 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h038 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (38 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (38 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (38 : T10J32HighBitTailState) := by
      change (((437 : NNReal) / (32768 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode045Term (38 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h046 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (46 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (46 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (46 : T10J32HighBitTailState) := by
      change (((429 : NNReal) / (32768 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode045Term (46 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h054 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (54 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (54 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (54 : T10J32HighBitTailState) := by
      change (((197 : NNReal) / (32768 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode045Term (54 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h062 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (62 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (62 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (62 : T10J32HighBitTailState) := by
      change (((109 : NNReal) / (16384 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode045Term (62 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h070 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (70 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (70 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (70 : T10J32HighBitTailState) := by
      change (((55 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode045Term (70 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h078 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (78 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (78 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (78 : T10J32HighBitTailState) := by
      change (((61 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode045Term (78 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h086 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (86 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (86 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (86 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (8192 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode045Term (86 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h094 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (94 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (94 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (94 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (2048 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode045Term (94 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h102 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (102 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (102 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (102 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode045Term (102 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h110 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (110 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (110 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (110 : T10J32HighBitTailState) := by
      change (((7 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode045Term (110 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h118 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (118 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (118 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (118 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (8192 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode045Term (118 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h126 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (126 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (126 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (126 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (2048 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode045Term (126 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h134 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (134 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (134 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (134 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode045Term (134 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h142 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (142 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (142 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (142 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode045Term (142 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h158 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (158 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (158 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (158 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode045Term (158 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    have h198 :
        t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) (198 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (198 : T10J32HighBitTailState) =
          t10j32HighBitTailNode045Term (198 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode045Term (198 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode045Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode045Support,
          t10j32HighBitTailMatrix (45 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode045Support, t10j32HighBitTailNode045Term dst := by
        simp [t10j32HighBitTailNode045Support, h006, h014, h022, h030, h038, h046, h054, h062, h070, h078, h086, h094, h102, h110, h118, h126, h134, h142, h158, h198]
      _ = (t10j32HighBitTailNode045LhsNum : NNReal) / (t10j32HighBitTailNode045LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode045Support, t10j32HighBitTailNode045Term]
        norm_num [t10j32HighBitTailNode045LhsNum, t10j32HighBitTailNode045LhsDen]

/-- Evaluated row certificate for generated row 45. -/
def t10j32HighBitTailNode045Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (45 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode045Row
  lhs_eq := by simpa using t10j32HighBitTailNode045MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode045Row]


/-- State label for generated row 46. -/
def t10j32HighBitTailNode046Label : String :=
  "v2=2|odd=3|h=2"

/-- Destination support of generated row 46. -/
def t10j32HighBitTailNode046Support : Finset T10J32HighBitTailState :=
  {7, 15, 23, 31, 39, 47, 55, 63, 71, 79, 87, 95, 103, 111, 119, 127, 135, 143, 159, 199}

/-- Exact generated summand values for row 46. -/
noncomputable def t10j32HighBitTailNode046Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 7 => ((282028951 : NNReal) / (2048 : NNReal))
  | 15 => ((14467213801 : NNReal) / (131072 : NNReal))
  | 23 => ((2437877763 : NNReal) / (65536 : NNReal))
  | 31 => ((3302315035 : NNReal) / (65536 : NNReal))
  | 39 => ((687977403 : NNReal) / (32768 : NNReal))
  | 47 => ((5430770631 : NNReal) / (32768 : NNReal))
  | 55 => ((218176515 : NNReal) / (16384 : NNReal))
  | 63 => ((104448923 : NNReal) / (8192 : NNReal))
  | 71 => ((859375 : NNReal) / (256 : NNReal))
  | 79 => ((953125 : NNReal) / (256 : NNReal))
  | 87 => ((23844431 : NNReal) / (8192 : NNReal))
  | 95 => ((46875 : NNReal) / (32 : NNReal))
  | 103 => ((718791 : NNReal) / (512 : NNReal))
  | 111 => ((109375 : NNReal) / (128 : NNReal))
  | 119 => ((12243895 : NNReal) / (8192 : NNReal))
  | 127 => ((1915527 : NNReal) / (2048 : NNReal))
  | 135 => ((15625 : NNReal) / (128 : NNReal))
  | 143 => ((15625 : NNReal) / (64 : NNReal))
  | 159 => ((15625 : NNReal) / (64 : NNReal))
  | 199 => ((15625 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 46. -/
def t10j32HighBitTailNode046LhsNum : Nat :=
  74117056725

/-- Exact denominator of `(M v)_i` for generated row 46. -/
def t10j32HighBitTailNode046LhsDen : Nat :=
  131072

/-- Exact vector entry for generated row 46. -/
def t10j32HighBitTailNode046Vector : Nat :=
  12659139

/-- Exact cleared-denominator CW inequality for generated row 46. -/
theorem t10j32HighBitTailNode046Bound :
    t10j32HighBitTailNode046LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode046Vector * t10j32HighBitTailNode046LhsDen := by
  norm_num [t10j32HighBitTailNode046LhsNum, t10j32HighBitTailNode046LhsDen, t10j32HighBitTailNode046Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 46. -/
def t10j32HighBitTailNode046Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode046LhsNum
  lhsDen := t10j32HighBitTailNode046LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode046LhsDen]
  vector := t10j32HighBitTailNode046Vector
  vector_pos := by norm_num [t10j32HighBitTailNode046Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode046Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 46. -/
theorem t10j32HighBitTailNode046MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (46 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode046LhsNum : NNReal) / (t10j32HighBitTailNode046LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode046Support,
      t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (7 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (7 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (7 : T10J32HighBitTailState) := by
      change (((3439 : NNReal) / (65536 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode046Term (7 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h015 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (15 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (15 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (15 : T10J32HighBitTailState) := by
      change (((6709 : NNReal) / (131072 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode046Term (15 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h023 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (23 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (23 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (23 : T10J32HighBitTailState) := by
      change (((1737 : NNReal) / (65536 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode046Term (23 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h031 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (31 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (31 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (31 : T10J32HighBitTailState) := by
      change (((1721 : NNReal) / (65536 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode046Term (31 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h039 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (39 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (39 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (39 : T10J32HighBitTailState) := by
      change (((437 : NNReal) / (32768 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode046Term (39 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h047 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (47 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (47 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (47 : T10J32HighBitTailState) := by
      change (((429 : NNReal) / (32768 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode046Term (47 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h055 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (55 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (55 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (55 : T10J32HighBitTailState) := by
      change (((197 : NNReal) / (32768 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode046Term (55 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h063 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (63 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (63 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (63 : T10J32HighBitTailState) := by
      change (((109 : NNReal) / (16384 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode046Term (63 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h071 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (71 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (71 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (71 : T10J32HighBitTailState) := by
      change (((55 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode046Term (71 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h079 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (79 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (79 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (79 : T10J32HighBitTailState) := by
      change (((61 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode046Term (79 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h087 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (87 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (87 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (87 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (8192 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode046Term (87 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h095 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (95 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (95 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (95 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (2048 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode046Term (95 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h103 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (103 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (103 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (103 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode046Term (103 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h111 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (111 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (111 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (111 : T10J32HighBitTailState) := by
      change (((7 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode046Term (111 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h119 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (119 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (119 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (119 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (8192 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode046Term (119 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h127 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (127 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (127 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (127 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (2048 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode046Term (127 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h135 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (135 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (135 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (135 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode046Term (135 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h143 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (143 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (143 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (143 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode046Term (143 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h159 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (159 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (159 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (159 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode046Term (159 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    have h199 :
        t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) (199 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (199 : T10J32HighBitTailState) =
          t10j32HighBitTailNode046Term (199 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode046Term (199 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode046Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode046Support,
          t10j32HighBitTailMatrix (46 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode046Support, t10j32HighBitTailNode046Term dst := by
        simp [t10j32HighBitTailNode046Support, h007, h015, h023, h031, h039, h047, h055, h063, h071, h079, h087, h095, h103, h111, h119, h127, h135, h143, h159, h199]
      _ = (t10j32HighBitTailNode046LhsNum : NNReal) / (t10j32HighBitTailNode046LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode046Support, t10j32HighBitTailNode046Term]
        norm_num [t10j32HighBitTailNode046LhsNum, t10j32HighBitTailNode046LhsDen]

/-- Evaluated row certificate for generated row 46. -/
def t10j32HighBitTailNode046Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (46 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode046Row
  lhs_eq := by simpa using t10j32HighBitTailNode046MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode046Row]


/-- State label for generated row 47. -/
def t10j32HighBitTailNode047Label : String :=
  "v2=2|odd=3|h=3"

/-- Destination support of generated row 47. -/
def t10j32HighBitTailNode047Support : Finset T10J32HighBitTailState :=
  {4, 12, 20, 28, 36, 44, 52, 60, 68, 76, 84, 92, 100, 108, 116, 124, 132, 140, 156, 196}

/-- Exact generated summand values for row 47. -/
noncomputable def t10j32HighBitTailNode047Term (dst : T10J32HighBitTailState) : NNReal :=
  match dst.val with
  | 4 => ((282028951 : NNReal) / (2048 : NNReal))
  | 12 => ((14467213801 : NNReal) / (131072 : NNReal))
  | 20 => ((2437877763 : NNReal) / (65536 : NNReal))
  | 28 => ((3302315035 : NNReal) / (65536 : NNReal))
  | 36 => ((687977403 : NNReal) / (32768 : NNReal))
  | 44 => ((5430770631 : NNReal) / (32768 : NNReal))
  | 52 => ((218176515 : NNReal) / (16384 : NNReal))
  | 60 => ((104448923 : NNReal) / (8192 : NNReal))
  | 68 => ((859375 : NNReal) / (256 : NNReal))
  | 76 => ((953125 : NNReal) / (256 : NNReal))
  | 84 => ((23844431 : NNReal) / (8192 : NNReal))
  | 92 => ((46875 : NNReal) / (32 : NNReal))
  | 100 => ((718791 : NNReal) / (512 : NNReal))
  | 108 => ((109375 : NNReal) / (128 : NNReal))
  | 116 => ((12243895 : NNReal) / (8192 : NNReal))
  | 124 => ((1915527 : NNReal) / (2048 : NNReal))
  | 132 => ((15625 : NNReal) / (128 : NNReal))
  | 140 => ((15625 : NNReal) / (64 : NNReal))
  | 156 => ((15625 : NNReal) / (64 : NNReal))
  | 196 => ((15625 : NNReal) / (64 : NNReal))
  | _ => 0


/-- Exact numerator of `(M v)_i` for generated row 47. -/
def t10j32HighBitTailNode047LhsNum : Nat :=
  74117056725

/-- Exact denominator of `(M v)_i` for generated row 47. -/
def t10j32HighBitTailNode047LhsDen : Nat :=
  131072

/-- Exact vector entry for generated row 47. -/
def t10j32HighBitTailNode047Vector : Nat :=
  12659139

/-- Exact cleared-denominator CW inequality for generated row 47. -/
theorem t10j32HighBitTailNode047Bound :
    t10j32HighBitTailNode047LhsNum * t10j32HighBitTailAlpha.denominator ≤
      t10j32HighBitTailAlpha.numerator * t10j32HighBitTailNode047Vector * t10j32HighBitTailNode047LhsDen := by
  norm_num [t10j32HighBitTailNode047LhsNum, t10j32HighBitTailNode047LhsDen, t10j32HighBitTailNode047Vector, t10j32HighBitTailAlpha]

/-- Packaged cleared row certificate for generated row 47. -/
def t10j32HighBitTailNode047Row : ClearedCWRowBound where
  lhsNum := t10j32HighBitTailNode047LhsNum
  lhsDen := t10j32HighBitTailNode047LhsDen
  lhsDen_pos := by norm_num [t10j32HighBitTailNode047LhsDen]
  vector := t10j32HighBitTailNode047Vector
  vector_pos := by norm_num [t10j32HighBitTailNode047Vector]
  alphaNum := 97
  alphaDen := 2000
  alphaDen_pos := by norm_num
  cleared := t10j32HighBitTailNode047Bound

set_option maxHeartbeats 1000000 in
-- Generated `NNReal` row arithmetic can exceed the default heartbeat budget.
/-- Exact row evaluation of `(M v)_i` for generated row 47. -/
theorem t10j32HighBitTailNode047MulVec :
    Matrix.mulVec t10j32HighBitTailMatrix t10j32HighBitTailCWBasis.vector
      (47 : T10J32HighBitTailState) =
      (t10j32HighBitTailNode047LhsNum : NNReal) / (t10j32HighBitTailNode047LhsDen : NNReal) := by
  rw [Matrix.mulVec, dotProduct]
  trans ∑ dst ∈ t10j32HighBitTailNode047Support,
      t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) dst *
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
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (4 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (4 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (4 : T10J32HighBitTailState) := by
      change (((3439 : NNReal) / (65536 : NNReal)) * (2624288 : NNReal)) =
        t10j32HighBitTailNode047Term (4 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h012 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (12 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (12 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (12 : T10J32HighBitTailState) := by
      change (((6709 : NNReal) / (131072 : NNReal)) * (2156389 : NNReal)) =
        t10j32HighBitTailNode047Term (12 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h020 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (20 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (20 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (20 : T10J32HighBitTailState) := by
      change (((1737 : NNReal) / (65536 : NNReal)) * (1403499 : NNReal)) =
        t10j32HighBitTailNode047Term (20 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h028 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (28 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (28 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (28 : T10J32HighBitTailState) := by
      change (((1721 : NNReal) / (65536 : NNReal)) * (1918835 : NNReal)) =
        t10j32HighBitTailNode047Term (28 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h036 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (36 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (36 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (36 : T10J32HighBitTailState) := by
      change (((437 : NNReal) / (32768 : NNReal)) * (1574319 : NNReal)) =
        t10j32HighBitTailNode047Term (36 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h044 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (44 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (44 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (44 : T10J32HighBitTailState) := by
      change (((429 : NNReal) / (32768 : NNReal)) * (12659139 : NNReal)) =
        t10j32HighBitTailNode047Term (44 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h052 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (52 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (52 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (52 : T10J32HighBitTailState) := by
      change (((197 : NNReal) / (32768 : NNReal)) * (2214990 : NNReal)) =
        t10j32HighBitTailNode047Term (52 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h060 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (60 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (60 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (60 : T10J32HighBitTailState) := by
      change (((109 : NNReal) / (16384 : NNReal)) * (1916494 : NNReal)) =
        t10j32HighBitTailNode047Term (60 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h068 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (68 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (68 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (68 : T10J32HighBitTailState) := by
      change (((55 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode047Term (68 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h076 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (76 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (76 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (76 : T10J32HighBitTailState) := by
      change (((61 : NNReal) / (16384 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode047Term (76 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h084 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (84 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (84 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (84 : T10J32HighBitTailState) := by
      change (((13 : NNReal) / (8192 : NNReal)) * (1834187 : NNReal)) =
        t10j32HighBitTailNode047Term (84 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h092 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (92 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (92 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (92 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (2048 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode047Term (92 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h100 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (100 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (100 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (100 : T10J32HighBitTailState) := by
      change (((3 : NNReal) / (4096 : NNReal)) * (1916776 : NNReal)) =
        t10j32HighBitTailNode047Term (100 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h108 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (108 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (108 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (108 : T10J32HighBitTailState) := by
      change (((7 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode047Term (108 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h116 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (116 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (116 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (116 : T10J32HighBitTailState) := by
      change (((5 : NNReal) / (8192 : NNReal)) * (2448779 : NNReal)) =
        t10j32HighBitTailNode047Term (116 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h124 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (124 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (124 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (124 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (2048 : NNReal)) * (1915527 : NNReal)) =
        t10j32HighBitTailNode047Term (124 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h132 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (132 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (132 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (132 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (8192 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode047Term (132 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h140 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (140 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (140 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (140 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode047Term (140 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h156 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (156 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (156 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (156 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode047Term (156 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    have h196 :
        t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) (196 : T10J32HighBitTailState) *
            t10j32HighBitTailCWBasis.vector (196 : T10J32HighBitTailState) =
          t10j32HighBitTailNode047Term (196 : T10J32HighBitTailState) := by
      change (((1 : NNReal) / (4096 : NNReal)) * (1000000 : NNReal)) =
        t10j32HighBitTailNode047Term (196 : T10J32HighBitTailState)
      norm_num [t10j32HighBitTailNode047Term]
    calc
      ∑ dst ∈ t10j32HighBitTailNode047Support,
          t10j32HighBitTailMatrix (47 : T10J32HighBitTailState) dst *
            t10j32HighBitTailCWBasis.vector dst =
          ∑ dst ∈ t10j32HighBitTailNode047Support, t10j32HighBitTailNode047Term dst := by
        simp [t10j32HighBitTailNode047Support, h004, h012, h020, h028, h036, h044, h052, h060, h068, h076, h084, h092, h100, h108, h116, h124, h132, h140, h156, h196]
      _ = (t10j32HighBitTailNode047LhsNum : NNReal) / (t10j32HighBitTailNode047LhsDen : NNReal) := by
        simp [t10j32HighBitTailNode047Support, t10j32HighBitTailNode047Term]
        norm_num [t10j32HighBitTailNode047LhsNum, t10j32HighBitTailNode047LhsDen]

/-- Evaluated row certificate for generated row 47. -/
def t10j32HighBitTailNode047Evaluated :
    EvaluatedCWRowBound t10j32HighBitTailMatrix t10j32HighBitTailCWBasis
      t10j32HighBitTailAlphaNNReal (47 : T10J32HighBitTailState) where
  row := t10j32HighBitTailNode047Row
  lhs_eq := by simpa using t10j32HighBitTailNode047MulVec
  vector_eq := by rfl
  alpha_eq := by
    norm_num [t10j32HighBitTailAlphaNNReal, t10j32HighBitTailAlpha,
      ProbabilityEntry.toNNReal, t10j32HighBitTailNode047Row]

end Generated
end CollatzShadowing
