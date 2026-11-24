import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.HkAllOf
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.XDerivOfTested
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.TestedOfXDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.HkAllLinear
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.XDerivLinear
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerVelIsBS
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.LopTested
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.CoeffMul
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.CoeffMulDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerMul
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerMulDeriv
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.TrainVCoeff
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.TrainECoeff

/-!
# `PartIII-a:T21/2/7/2/1/1/6`: `AdjTimeJetsOf` from its proved leaves

Source: `the November 2 reference manuscript` (SP) lines 3060-3061, 3052-3058,
270-288, 2866-2870. The assembly is `adjTimeJetsOf_of_leaves` (`Sub/AdjInterior/TimeJets/Assembly.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`AdjTimeJetsOf` from its leaves.** -/
theorem adjTimeJetsOf (m : ℝ) (hm : 8 < m) : AdjTimeJetsOf m :=
  adjTimeJetsOf_of_leaves m adjHkAllOf xDerivOfTested testedOfXDeriv adjHkAllLinear
    hasXDerivOnLinear kerVelIsBS (adjLopTested m) adjHkAllCoeffMul coeffMulDeriv
    (adjHkAllKerMul m (by linarith)) (kerMulDeriv m (by linarith)) (trainVCoeff m)
    (trainECoeff m)

end UnforcedLeray.Short.IIIa
