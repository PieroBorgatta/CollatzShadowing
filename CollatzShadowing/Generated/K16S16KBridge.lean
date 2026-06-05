/-
Bridge facts connecting the generated 37-state `K,b` SCC certificate
and the generated 37-state Collatz-Wielandt matrix certificate.

Both generated modules come from
`../scripts/phantom_taxonomy/orbit_harness_k16_s16_scc_K_cw_certificate.json`.
-/

import CollatzShadowing.Generated.K16S16KExactCWSummary
import CollatzShadowing.Generated.K16S16KSCC

namespace CollatzShadowing
namespace Generated

open scoped ENNReal NNReal

/-- The SCC certificate and CW matrix certificate use the same `Fin 37` index type. -/
def k16s16KSCCNodeToCWState (u : K16S16KSCCNode) : K16S16KState :=
  u.1

/-- The SCC certificate and CW matrix certificate have the same state label order. -/
theorem k16s16KSCCLabel_eq_CWStateLabel (i : Fin 37) :
    k16s16KSCCLabel i = k16s16KStateLabel i := by
  fin_cases i <;> rfl

/-- The node-to-state map preserves generated labels. -/
theorem k16s16KSCCNodeToCWState_label (u : K16S16KSCCNode) :
    k16s16KSCCLabel u.1 = k16s16KStateLabel (k16s16KSCCNodeToCWState u) :=
  k16s16KSCCLabel_eq_CWStateLabel u.1

/-- The generated SCC and CW files report the same number of directed edge types. -/
theorem k16s16K_edge_count_eq_scc_edge_count :
    k16s16KEdgeCount = k16s16KSCCEdgeCount := by
  rfl

/-- The SCC hub is the `K3:b1` state in the CW matrix ordering. -/
theorem k16s16KSCCHub_label :
    k16s16KStateLabel (k16s16KSCCNodeToCWState k16s16KSCCHub) = "K3:b1" := by
  rfl

/--
The generated 37-state finite CW certificate gives the corresponding
Mathlib real spectral-radius bound for the realified non-negative
matrix.
-/
theorem k16s16KSpectralRadiusBound :
    spectralRadius ℝ (nnrealMatrixToReal k16s16KMatrix) ≤
      (k16s16KAlphaNNReal : ℝ≥0∞) :=
  spectralRadius_le_of_finiteCWCertificate
    k16s16KMatrix k16s16KCWBasis k16s16KAlphaNNReal
    k16s16KFiniteCWCertificate

/--
Paper-facing package tying together the generated 37-state SCC
certificate and the generated 37-state finite CW certificate.
-/
structure K16S16KCertifiedComponentWithCW where
  sccCertificate :
    TruncatedEpisodeGraph.CriticalSCCCertificate k16s16KTruncatedGraph
  cwCertificate :
    FiniteCWCertificate k16s16KMatrix k16s16KCWBasis k16s16KAlphaNNReal
  spectralRadiusBound :
    spectralRadius ℝ (nnrealMatrixToReal k16s16KMatrix) ≤
      (k16s16KAlphaNNReal : ℝ≥0∞)
  labelCompatible :
    ∀ i : Fin 37, k16s16KSCCLabel i = k16s16KStateLabel i
  nodeLabelCompatible :
    ∀ u : K16S16KSCCNode,
      k16s16KSCCLabel u.1 = k16s16KStateLabel (k16s16KSCCNodeToCWState u)
  edgeCountCompatible :
    k16s16KEdgeCount = k16s16KSCCEdgeCount
  hubLabel :
    k16s16KStateLabel (k16s16KSCCNodeToCWState k16s16KSCCHub) = "K3:b1"

/--
The generated 37-state `K,b` component with its checked SCC certificate,
checked finite CW certificate, and checked indexing compatibility.
-/
def k16s16KCertifiedComponentWithCW :
    K16S16KCertifiedComponentWithCW where
  sccCertificate := k16s16KCriticalSCCCertificate
  cwCertificate := k16s16KFiniteCWCertificate
  spectralRadiusBound := k16s16KSpectralRadiusBound
  labelCompatible := k16s16KSCCLabel_eq_CWStateLabel
  nodeLabelCompatible := k16s16KSCCNodeToCWState_label
  edgeCountCompatible := k16s16K_edge_count_eq_scc_edge_count
  hubLabel := k16s16KSCCHub_label

end Generated
end CollatzShadowing
