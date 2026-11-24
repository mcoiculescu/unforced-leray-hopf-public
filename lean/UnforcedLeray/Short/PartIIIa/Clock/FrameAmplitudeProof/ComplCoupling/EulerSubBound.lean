import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound.GaussCore
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_3_2_1

/-!
# Part III-a, task `PartIII-a:T21/c5/3/2`: moving Euler adjoint residual bound (`MovLamDualEulerSubBound`)

Source of record: `the November 2 reference manuscript` (SP), lines 2866-2897,
2905-2918, and 2990-2997 (`eq:short-causal-damped-complement`, `eq:short-causal-ampl-moving`).

## Reduction to the planar seed duality (all other steps proved, zero `sorry`)

The reduction lives in the helper `EulerSubBound/GaussCore.lean`. This task file cannot import it:
`GaussCore` imports `DirectError/EulerSubBound/Pullback.lean`, which imports
`Sub/PartIII-a_T21_c5_1_1.lean`, which imports this file (only for `Sub/PartIII-a_T21_c5_3_2`).
The final theorem therefore goes in a module that imports `GaussCore` (or this file switches once
that import of `Sub/PartIII-a_T21_c5_1_1.lean` is redirected to `Sub/PartIII-a_T21_c5_3_2`).

`EulerSubCore.movLamDualEulerSubBound_of_dual κ : PlanarSeedEulerDual κ → MovLamDualEulerSubBound κ`
(helper `EulerSubBound/GaussCore.lean`) combines:

* the Gram normalisation and its `O(d⁻²)` inverse error (`ComplCouplingEuler.movLamDualEulerSubBound_of`,
  `Sub/PartIII-a_T21_c5_3_2.lean`);
* the linearity of the moving adjoint on `perLam = G⁻¹ perLam0` in the small-`ν` regime
  (`DirectEulerSub.kerAdj_perLam_eq`, `DirectEulerSub.transCx_perLam_eq_of_diff`);
* the rescaled BUC train comparison `O(ν³/θ)` (`EulerSubTrain.memLp_and_xNorm_movEulerAdj_trainDiff`,
  helper `EulerSubBound/TrainDiff.lean`, from `PartI.trainComparison_proof`);
* the Gaussian-cylinder residual bound `O(d⁻²) = O(ν³/θ)` (`EulerSubCore.gaussSub_bound`): image
  expansion of the paired-image kernel (`EulerSubBound/KerExpansion.lean`, `kerD_sub_kerPl_le`),
  paired translates of the dual kernels and Gaussian columns (`EulerSubBound/Lattice.lean`), and the
  near/far comparison of `K_d^T(P_dλ ∇ curl P_d v₀)` with the planar `K_∞^T(λ ∇ curl v₀)`
  (`EulerSubBound/KernelNear.lean`).

The only remaining input is the planar seed duality `L₀^* λ_k = λ_k λ_k` (SP 593-610, 2891-2918):
```lean
theorem planarSeedEulerDual (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.EulerSubCore.PlanarSeedEulerDual κ
```
after which
```lean
theorem movLamDualEulerSubBound (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.MovLamDualEulerSubBound κ :=
  UnforcedLeray.Short.IIIa.EulerSubCore.movLamDualEulerSubBound_of_dual κ (UnforcedLeray.Short.IIIa.planarSeedEulerDual κ)
```
-/

theorem movLamDualEulerSubBound (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.MovLamDualEulerSubBound κ :=
  UnforcedLeray.Short.IIIa.EulerSubCore.movLamDualEulerSubBound_of_dual κ (UnforcedLeray.Short.IIIa.planarSeedEulerDual κ)

