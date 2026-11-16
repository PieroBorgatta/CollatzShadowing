/-
Strict axiom audit of all public theorem declarations in the ten November
integration modules. Run after their pinned incremental builds complete.
The audit fails for any axiom outside propext, Classical.choice, Quot.sound.
This is not an independent-kernel replay or a proof of open analytic inputs.
-/
import CollatzShadowing.RootPoolBudget
import CollatzShadowing.ReturnBlocks
import CollatzShadowing.JointAtomDictionary
import CollatzShadowing.AffinePositivity
import CollatzShadowing.CapacityAllocation
import CollatzShadowing.RelativeMassFlow
import CollatzShadowing.WordSurgery
import CollatzShadowing.SiblingPool
import CollatzShadowing.CycleRotation
import CollatzShadowing.FiniteOrbitTransfer
import Lean

open Lean Elab Command

namespace AllNewDependencyAudit

private def allowed (name : Name) : Bool :=
  name == `propext || name == `Classical.choice || name == `Quot.sound

private def roots : Array Name :=
  #[`CollatzShadowing.RootPoolBudget.normalizedWeight_nonneg,
    `CollatzShadowing.RootPoolBudget.normalizedWeight_eq_loss,
    `CollatzShadowing.RootPoolBudget.sum_normalizedWeight_le,
    `CollatzShadowing.RootPoolBudget.sum_selected_le,
    `CollatzShadowing.RootPoolBudget.sum_labeled_normalizedWeight_le,
    `CollatzShadowing.RootPoolBudget.normalized_source_fiber_bound,
    `CollatzShadowing.RootPoolBudget.distinct_sources_of_normalized_mass,
    `CollatzShadowing.RootPoolBudget.pool_visit_time_unique,
    `CollatzShadowing.RootPoolBudget.word_eq_of_pool,
    `CollatzShadowing.RootPoolBudget.reciprocalWeight_le_initial,
    `CollatzShadowing.RootPoolBudget.sum_reciprocalWeight_pool_le,
    `CollatzShadowing.RootPoolBudget.sum_labeled_reciprocalWeight_pool_le,
    `CollatzShadowing.ReturnBlocks.point_mem_section,
    `CollatzShadowing.ReturnBlocks.middle_not_mem_section,
    `CollatzShadowing.ReturnBlocks.block_steps,
    `CollatzShadowing.ReturnBlocks.point_increment,
    `CollatzShadowing.ReturnBlocks.point_lt_next,
    `CollatzShadowing.ReturnBlocks.first_return,
    `CollatzShadowing.ReturnBlocks.iterate_point,
    `CollatzShadowing.ReturnBlocks.arbitrarily_many_increasing_first_returns,
    `CollatzShadowing.JointAtomDictionary.admissible_iff_residue,
    `CollatzShadowing.JointAtomDictionary.inverseSource_affine,
    `CollatzShadowing.JointAtomDictionary.inverseSource_pos,
    `CollatzShadowing.JointAtomDictionary.source_odd_of_matches,
    `CollatzShadowing.JointAtomDictionary.inverseSource_spec,
    `CollatzShadowing.JointAtomDictionary.admissible_of_exact,
    `CollatzShadowing.JointAtomDictionary.admissible_iff_exact,
    `CollatzShadowing.JointAtomDictionary.inverseSource_le_iff,
    `CollatzShadowing.JointAtomDictionary.inverseSource_injective_at_length,
    `CollatzShadowing.JointAtomDictionary.card_admissible_image,
    `CollatzShadowing.AffinePositivity.integer_source_pos,
    `CollatzShadowing.AffinePositivity.height_of_ternary_congruence,
    `CollatzShadowing.AffinePositivity.admissible_iff_ternary_congruence,
    `CollatzShadowing.AffinePositivity.exact_source_iff_ternary_congruence,
    `CollatzShadowing.AffinePositivity.card_ternary_atom_image,
    `CollatzShadowing.CapacityAllocation.capped_cell_bound,
    `CollatzShadowing.CapacityAllocation.mass_le_threshold_cost,
    `CollatzShadowing.CapacityAllocation.threshold_lower_bound,
    `CollatzShadowing.CapacityAllocation.threshold_cell_identity,
    `CollatzShadowing.CapacityAllocation.threshold_allocation_exact,
    `CollatzShadowing.CapacityAllocation.threshold_certificate_le_competitor,
    `CollatzShadowing.CapacityAllocation.threshold_at_score_upper_bound,
    `CollatzShadowing.RelativeMassFlow.total_flow_le_capacity,
    `CollatzShadowing.RelativeMassFlow.relative_mass_le_image_capacity,
    `CollatzShadowing.RelativeMassFlow.card_images_lower_bound,
    `CollatzShadowing.RelativeMassFlow.scaled_card_images_lower_bound,
    `CollatzShadowing.RelativeMassFlow.sum_card_disjoint_le,
    `CollatzShadowing.RelativeMassFlow.disjoint_block_flow_budget,
    `CollatzShadowing.WordSurgery.constant_append,
    `CollatzShadowing.WordSurgery.interior_constant_shift,
    `CollatzShadowing.WordSurgery.balanced_shift_terminal_congruence,
    `CollatzShadowing.WordSurgery.terminal_depth_budget,
    `CollatzShadowing.SiblingPool.nonrecurrentPool_mono,
    `CollatzShadowing.SiblingPool.sibling_range_nonrecurrent,
    `CollatzShadowing.SiblingPool.sibling_subpool_nonrecurrent,
    `CollatzShadowing.SiblingPool.canonical_range_nonrecurrent,
    `CollatzShadowing.SiblingPool.canonical_finite_nonrecurrent,
    `CollatzShadowing.SiblingPool.canonical_word_charge_le,
    `CollatzShadowing.SiblingPool.canonical_finite_word_charge_le,
    `CollatzShadowing.SiblingPool.canonical_labeled_word_charge_le,
    `CollatzShadowing.CycleRotation.denominator_rotate,
    `CollatzShadowing.CycleRotation.constant_rotate,
    `CollatzShadowing.CycleRotation.dvd_constant_iff_dvd_rotated,
    `CollatzShadowing.CycleRotation.denominator_dvd_constant_iff,
    `CollatzShadowing.CycleRotation.denominator_mul_source,
    `CollatzShadowing.CycleRotation.cycle_divisor_passes_rotated,
    `CollatzShadowing.FiniteOrbitTransfer.iterate_injOn_prefix,
    `CollatzShadowing.FiniteOrbitTransfer.window_card_le_prefix_add,
    `CollatzShadowing.FiniteOrbitTransfer.window_bound_of_iterate_injective_estimate]

private def run : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  for root in roots do
    unless (env.find? root).isSome do
      throwError "Missing audited theorem: {root}"
    let axioms ← Lean.collectAxioms root
    for ax in axioms do
      unless allowed ax do
        throwError "Unexpected axiom in {root}: {ax}"
    logInfo m!"SPRINT_ROOT_AUDIT: PASS {root}; axioms: {axioms.toList}"
  logInfo m!"SPRINT_DEPENDENCY_AUDIT: PASS; roots: {roots.size}"

set_option maxHeartbeats 0 in
run_cmd run

end AllNewDependencyAudit
