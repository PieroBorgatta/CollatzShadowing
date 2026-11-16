/-
Algebraic interface between actual predecessor densities and an arithmetic
trace.  All density, weight, and trace identities are explicit hypotheses.

For a nonreturning positive odd target n, the external Valbuena development
uses g(n) = delta * n * D(n), with D(n) the mean of reciprocal first-hit
correction products.  This file imports none of that external development.
It proves the exact conditional bridge needed before a transverse trace
comparison could be used for the local relative-mass conjecture H.

Author: AI-assisted (Codex) + Piero Borgatta. Date: 2026-11-15.
-/

import Mathlib.Tactic

namespace CollatzShadowing.TraceDensityBridge

/-- A trace Harnack inequality gives a relative density comparison, losing
only the target height ratio and the first-hit weight comparison constant.
The trace Harnack inequality is an input, not a conclusion. -/
theorem density_of_trace_comparison
    {delta P R L kappa n y d₀ d₁ D₀ D₁ E₀ E₁ : ℝ}
    (hdelta : 0 < delta) (hP : 0 < P) (hR : 0 < R)
    (hL : 0 < L) (hkappa : 0 ≤ kappa) (hn : 0 < n)
    (hheight : y ≤ R * n) (hD₁ : 0 ≤ D₁)
    (hbase : d₀ ≤ P * D₀) (himage : D₁ ≤ d₁)
    (hE₀ : E₀ = delta * n * D₀)
    (hE₁ : E₁ = delta * y * D₁)
    (htrace : kappa * E₀ ≤ L * E₁) :
    (kappa / (R * P * L)) * d₀ ≤ d₁ := by
  have hdn : 0 < delta * n := mul_pos hdelta hn
  have hfirst : (delta * n) * (kappa * d₀) ≤ P * L * E₁ := by
    calc
      (delta * n) * (kappa * d₀)
          ≤ (delta * n) * (kappa * (P * D₀)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbase hkappa) hdn.le
      _ = P * (kappa * E₀) := by rw [hE₀]; ring
      _ ≤ P * (L * E₁) := mul_le_mul_of_nonneg_left htrace hP.le
      _ = P * L * E₁ := by ring
  have hsecond : P * L * E₁ ≤
      (delta * n) * (R * P * L * d₁) := by
    have hd : 0 ≤ d₁ := hD₁.trans himage
    calc
      P * L * E₁ = P * L * delta * (y * D₁) := by rw [hE₁]; ring
      _ ≤ P * L * delta * ((R * n) * D₁) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hheight hD₁) (by positivity)
      _ ≤ P * L * delta * ((R * n) * d₁) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left himage (mul_pos hR hn).le) (by positivity)
      _ = (delta * n) * (R * P * L * d₁) := by ring
  have hfinal : kappa * d₀ ≤ (R * P * L) * d₁ :=
    (mul_le_mul_iff_right₀ hdn).mp (hfirst.trans hsecond)
  have hden : 0 < R * P * L := by positivity
  have hdiv := (div_le_iff₀ hden).mpr (by
    simpa only [mul_comm] using hfinal)
  simpa only [div_mul_eq_mul_div] using hdiv

/-- In the reverse direction the trace comparison loses only the weight
constant, provided the second target is at least the first. -/
theorem trace_of_density_comparison
    {delta P L c n y d₀ d₁ D₀ D₁ E₀ E₁ : ℝ}
    (hdelta : 0 < delta) (hP : 0 < P) (hL : 0 < L)
    (hc : 0 ≤ c) (hn : 0 < n) (hheight : n ≤ y)
    (hD₀ : 0 ≤ D₀) (hbase : D₀ ≤ d₀) (himage : d₁ ≤ P * D₁)
    (hE₀ : E₀ = delta * n * D₀)
    (hE₁ : E₁ = delta * y * D₁)
    (hdensity : c * d₀ ≤ L * d₁) :
    (c / (P * L)) * E₀ ≤ E₁ := by
  have hD₁ : 0 ≤ D₁ := by
    have hnonneg : 0 ≤ L * d₁ :=
      (mul_nonneg hc (hD₀.trans hbase)).trans hdensity
    have hd₁ : 0 ≤ d₁ := (mul_nonneg_iff_of_pos_left hL).mp hnonneg
    exact (mul_nonneg_iff_of_pos_left hP).mp (hd₁.trans himage)
  have hfirst : c * E₀ ≤ (delta * n) * (L * P * D₁) := by
    calc
      c * E₀ = (delta * n) * (c * D₀) := by rw [hE₀]; ring
      _ ≤ (delta * n) * (c * d₀) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbase hc) (mul_pos hdelta hn).le
      _ ≤ (delta * n) * (L * d₁) :=
        mul_le_mul_of_nonneg_left hdensity (mul_pos hdelta hn).le
      _ ≤ (delta * n) * (L * (P * D₁)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left himage hL.le) (mul_pos hdelta hn).le
      _ = (delta * n) * (L * P * D₁) := by ring
  have hsecond : (delta * n) * (L * P * D₁) ≤ (P * L) * E₁ := by
    calc
      (delta * n) * (L * P * D₁) = (delta * L * P * D₁) * n := by ring
      _ ≤ (delta * L * P * D₁) * y :=
        mul_le_mul_of_nonneg_left hheight (by positivity)
      _ = (P * L) * E₁ := by rw [hE₁]; ring
  have hden : 0 < P * L := by positivity
  have hdiv := (div_le_iff₀ hden).mpr (by
    simpa only [mul_comm] using hfirst.trans hsecond)
  simpa only [div_mul_eq_mul_div] using hdiv

/-- A uniform trace floor would suffice together with a logarithmic trace
upper bound at the base.  The upper bound remains a separate analytic
obligation; it is not a consequence of positivity of the trace. -/
theorem density_of_trace_floor_and_upper
    {delta P R L C b n y d₀ d₁ D₀ D₁ E₀ E₁ : ℝ}
    (hdelta : 0 < delta) (hP : 0 < P) (hR : 0 < R)
    (hL : 0 < L) (hC : 0 < C) (hb : 0 ≤ b) (hn : 0 < n)
    (hheight : y ≤ R * n) (hD₁ : 0 ≤ D₁)
    (hbase : d₀ ≤ P * D₀) (himage : D₁ ≤ d₁)
    (hE₀ : E₀ = delta * n * D₀)
    (hE₁ : E₁ = delta * y * D₁)
    (hupper : E₀ ≤ C * L) (hfloor : b ≤ E₁) :
    ((b / C) / (R * P * L)) * d₀ ≤ d₁ := by
  apply density_of_trace_comparison hdelta hP hR hL (div_nonneg hb hC.le)
    hn hheight hD₁ hbase himage hE₀ hE₁
  calc
    (b / C) * E₀ ≤ (b / C) * (C * L) :=
      mul_le_mul_of_nonneg_left hupper (div_nonneg hb hC.le)
    _ = L * b := by field_simp [ne_of_gt hC]
    _ ≤ L * E₁ := mul_le_mul_of_nonneg_left hfloor hL.le

/-- The normalized trace E(y)/y is the natural object for aggregated
comparisons.  With several image targets there is no extra target-height
loss: the normalization already keeps it inside the hypothesis. -/
theorem summed_density_of_normalized_trace_comparison
    {ι : Type*} (F : Finset ι)
    {delta P L kappa n d₀ D₀ E₀ : ℝ}
    {y d D E : ι → ℝ}
    (hdelta : 0 < delta) (hP : 0 < P) (hL : 0 < L)
    (hkappa : 0 ≤ kappa) (hn : 0 < n)
    (hy : ∀ i ∈ F, 0 < y i)
    (hbase : d₀ ≤ P * D₀) (himage : ∀ i ∈ F, D i ≤ d i)
    (hE₀ : E₀ = delta * n * D₀)
    (hE : ∀ i ∈ F, E i = delta * y i * D i)
    (htrace : kappa * (E₀ / n) ≤ L * ∑ i ∈ F, E i / y i) :
    (kappa / (P * L)) * d₀ ≤ ∑ i ∈ F, d i := by
  have hsource : E₀ / n = delta * D₀ := by
    rw [hE₀]
    field_simp [ne_of_gt hn]
  have hsum : (∑ i ∈ F, E i / y i) = delta * ∑ i ∈ F, D i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hE i hi]
    field_simp [ne_of_gt (hy i hi)]
  have hweighted : kappa * D₀ ≤ L * ∑ i ∈ F, D i := by
    rw [hsource, hsum] at htrace
    have ht : delta * (kappa * D₀) ≤ delta * (L * ∑ i ∈ F, D i) := by
      nlinarith only [htrace]
    exact (mul_le_mul_iff_right₀ hdelta).mp ht
  have hdsum : (∑ i ∈ F, D i) ≤ ∑ i ∈ F, d i :=
    Finset.sum_le_sum himage
  have hfinal : kappa * d₀ ≤ (P * L) * ∑ i ∈ F, d i := by
    calc
      kappa * d₀ ≤ kappa * (P * D₀) :=
        mul_le_mul_of_nonneg_left hbase hkappa
      _ = P * (kappa * D₀) := by ring
      _ ≤ P * (L * ∑ i ∈ F, D i) :=
        mul_le_mul_of_nonneg_left hweighted hP.le
      _ ≤ P * (L * ∑ i ∈ F, d i) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdsum hL.le) hP.le
      _ = (P * L) * ∑ i ∈ F, d i := by ring
  have hdiv := (div_le_iff₀ (mul_pos hP hL)).mpr (by
    simpa only [mul_comm] using hfinal)
  simpa only [div_mul_eq_mul_div] using hdiv

end CollatzShadowing.TraceDensityBridge
