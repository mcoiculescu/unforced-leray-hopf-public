import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_1_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.GradPerSum.RadialG
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.WeakFTC.CutFTC.GradPerSum.PolarJet

/-!
# Part III-a, task `PartIII-a:T21/c5/1/1/1`: spatial gradient periodization (`SeedLamGradPerSum`)

Source of record: `the November 2 reference manuscript` (SP), lines 593-610,
890-912, 2504-2523, and 2891-2905 (`eq:short-seed-functional`, `eq:short-causal-moving-eq`).

The periodization gradient infrastructure, the identification `κ.lamP = seedDualExplicit lam h`,
and the conditional assembly `seedLamGradPerSum_of_leaves` are in
`Sub/PartIII-a_T21_c5_1_1_1.lean`. The two analytic leaves are proved in
`GradPerSum/RadialG.lean` (`GradPerSumLeaves.seedDualRadialGDerivBounds_proof`: the radial
quotient `G = Δ₂⁻¹h / (Ω - iλ/2)` has `|G'(r)| = O(r)` at `0` and `O(r⁻²)` at `∞`) and
`GradPerSum/PolarJet.lean` (`GradPerSumLeaves.polarKernelJet1Decay_proof`: `c G(|y|) e^{±2iθ}`
is `C¹` with `O((1 + |y₁| + |y₂|)⁻²)` derivative).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`SeedLamGradPerSum κ` (`PartIII-a:T21/c5/1/1/1`, SP 593-610, 2891-2905).** -/
theorem seedLamGradPerSum (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.SeedLamGradPerSum κ :=
  seedLamGradPerSum_of_leaves κ GradPerSumLeaves.seedDualRadialGDerivBounds_proof
    GradPerSumLeaves.polarKernelJet1Decay_proof

end UnforcedLeray.Short.IIIa
