/-
Algebraic boundary of compatible affine trace switching.

An edge label `(D,C)` represents the rational formal point `-C/D`.  The
compatibility equations from `SwitchingPrecision` do more than preserve a
2-adic valuation: they force those rational points to follow the prescribed
affine Syracuse branch exactly.

Consequently, a scalar compatible trace on a cyclic control graph assigns one
rational point to every node.  Every directed cycle based at a node must fix
the same point.  Two cycles with different formal fixed points therefore
cannot share one scalar affine trace.  This identifies the precise limit of
the new trace mechanism: it certifies a coherent periodic boundary, but it
does not automatically rank arbitrary switching among incompatible phantom
cycles.
-/

import CollatzShadowing.SwitchingPrecision

namespace CollatzShadowing

/-- Rational point encoded by a positive affine trace label `(D,C)`. -/
def switchingFormalPoint (D C : ℕ) : ℚ :=
  -(C : ℚ) / (D : ℚ)

/-- One prescribed-exponent affine Syracuse branch over the rationals. -/
def syracuseAffineStepQ (e : ℕ) (x : ℚ) : ℚ :=
  (3 * x + 1) / (2 : ℚ) ^ e

/--
Compatible label switching transports the encoded rational point along the
same prescribed Syracuse edge.
-/
theorem switchingFormalPoint_transport
    {D C D' C' e q : ℕ}
    (hD : 0 < D) (hD' : 0 < D')
    (hcoeff : 3 * D' = q * D)
    (hconst : D' + 2 ^ e * C' = q * C) :
    syracuseAffineStepQ e (switchingFormalPoint D C)
      = switchingFormalPoint D' C' := by
  have hDq : (D : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  have hD'q : (D' : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD')
  have hpowq : (2 : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcoeffq :
      (3 : ℚ) * (D' : ℚ) = (q : ℚ) * (D : ℚ) := by
    exact_mod_cast hcoeff
  have hconstq :
      (D' : ℚ) + (2 : ℚ) ^ e * (C' : ℚ)
        = (q : ℚ) * (C : ℚ) := by
    exact_mod_cast hconst
  unfold syracuseAffineStepQ switchingFormalPoint
  field_simp [hDq, hD'q, hpowq]
  nlinarith

/--
The formal fixed point of a nondegenerate word is its unique rational fixed
point.
-/
theorem syracuseWordAffineEndpointQ_fixed_eq_formalFixedPoint
    {w : List ℕ} {x : ℚ}
    (hden :
      (((2 ^ w.sum : ℕ) : ℚ) - ((3 ^ w.length : ℕ) : ℚ)) ≠ 0)
    (hfix : syracuseWordAffineEndpointQ w x = x) :
    x = syracuseWordFormalFixedPoint w := by
  have hpow : ((2 ^ w.sum : ℕ) : ℚ) ≠ 0 := by norm_num
  unfold syracuseWordAffineEndpointQ at hfix
  unfold syracuseWordFormalFixedPoint
  field_simp [hpow] at hfix
  field_simp [hden]
  linarith

/--
Two nondegenerate words with distinct formal fixed points cannot both be
cycles of one scalar rational control state.
-/
theorem no_common_rational_fixed_point_of_distinct_words
    {w v : List ℕ}
    (hdenw :
      (((2 ^ w.sum : ℕ) : ℚ) - ((3 ^ w.length : ℕ) : ℚ)) ≠ 0)
    (hdenv :
      (((2 ^ v.sum : ℕ) : ℚ) - ((3 ^ v.length : ℕ) : ℚ)) ≠ 0)
    (hne :
      syracuseWordFormalFixedPoint w
        ≠ syracuseWordFormalFixedPoint v) :
    ¬ ∃ x : ℚ,
      syracuseWordAffineEndpointQ w x = x
        ∧ syracuseWordAffineEndpointQ v x = x := by
  rintro ⟨x, hw, hv⟩
  have hxw :=
    syracuseWordAffineEndpointQ_fixed_eq_formalFixedPoint hdenw hw
  have hxv :=
    syracuseWordAffineEndpointQ_fixed_eq_formalFixedPoint hdenv hv
  exact hne (hxw.symm.trans hxv)

/--
Concrete branching obstruction: the words `[1]` and `[1,2]` cannot be
self-cycles of the same rational control state, since their fixed points are
`-1` and `-5`.
-/
theorem no_common_rational_fixed_point_one_and_one_two :
    ¬ ∃ x : ℚ,
      syracuseWordAffineEndpointQ [1] x = x
        ∧ syracuseWordAffineEndpointQ [1, 2] x = x := by
  apply no_common_rational_fixed_point_of_distinct_words
  · norm_num
  · norm_num
  · rw [syracuseWordFormalFixedPoint_one,
      syracuseWordFormalFixedPoint_one_two]
    norm_num

end CollatzShadowing
