import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3.Assembly_F2_3_1
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.FrozenEulerSplitting.PeriodizedCylinderCoord

/-!
# `PartII-b:F2/3` (`FrozenEulerSplitting.lean`): Frozen planar Euler dichotomy and periodized cylinder coordinates

Source of record: `the November 2 reference manuscript` (SP), lines 931–953,
2104–2115, 2145–2171, 2347–2358 (`short-sp:dichotomy`).

This module imports `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_F2_3»`, which provides:
1. `PartIIbF23Sub`:
   * 2×2 Euclidean rotation-scaling operator calculus on `E2 = EuclideanSpace ℝ (Fin 2)`
     (`rotScaleMat`, `rotScaleCLM`, `rotScaleCLM_inv_mul`, `rotScaleCLM_mul_inv`,
     `norm_rotScaleCLM_le`);
   * Block-length threshold selection (`exists_L₀_frozen_dichotomy`);
   * Pointwise frozen planar Gaussian angular velocity `frozenOmega` and radial transport flow
     `frozenRadialFlow` at slow age `σ` (`a = 1 + σ`, SP 931–953, 2104–2115).
2. The two leaf propositions of `PartII-b:F2/3`:
   * `PlanarFrozenEulerStep` (`PartII-b:F2/3/1`,
     `Short/PartII-b/Sub/PartII-b_F2_3/Assembly_F2_3_1.lean`),
   * `PeriodizedCylinderCoordStep` (`PartII-b:F2/3/2`,
     `Short/PartII-b/Tasks/BlockFactorization/FrozenEulerSplitting/PeriodizedCylinderCoord.lean`),
   and the unconditional assembly theorem `frozenEulerSplittingStep_of`.
-/

theorem frozenEulerSplittingStep_proof :
    UnforcedLeray.Short.IIb.FrozenEulerSplittingStep :=
  UnforcedLeray.Short.IIb.frozenEulerSplittingStep_of
    UnforcedLeray.Short.IIb.planarFrozenEulerStep
    periodizedCylinderCoordStep_proof
