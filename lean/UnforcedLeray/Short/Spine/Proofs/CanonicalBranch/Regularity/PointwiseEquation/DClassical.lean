import UnforcedLeray.Short.Spine.Sub.SP_CAN4_5_3
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.DClassical.TestBeta
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.DClassical.TestBetaDerivBound
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.DClassical.TestMemLp
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.DClassical.ConjOscD
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.DClassical.IntegralXG
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.DClassical.LocIntXG
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch.Regularity.PointwiseEquation.Smoothness

/-!
# Spine: `DClassicalAe` (task `Spine:SP-CAN/4/5/3`, assembly)

Source of record: `the November 2 reference manuscript`, line 1086 and lines
1134-1140. Assembles the proved leaves (`DClassical/TestBeta`, `TestBetaDerivBound`, `TestMemLp`,
`ConjOscD`, `IntegralXG`, `LocIntXG`) and the smoothness facts (`Smoothness`) into the unconditional
statement `DClassicalAe` of `Sub/SP_CAN4_5.lean` through `dClassicalAe_of` and `testDAction_of`
(`Sub/SP_CAN4_5_3.lean`).

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

/-- **`DClassicalAe` (unconditional).** If `u ∈ 𝒟(D)` has a representative `g` that is `C^∞` on
`(0, ∞)`, then `oscillatorD g =ᵐ[xGMeasure] D u`. -/
theorem dClassicalAe_proof : UnforcedLeray.Short.Spine.DClassicalAe :=
  dClassicalAe_of (testDAction_of testBeta_proof testBetaDerivBound_proof testMemLp_proof)
    conjOscillatorD_proof integralXGEq_proof locIntXGMulW_proof smoothnessFacts_proof

end UnforcedLeray.Short.Spine
