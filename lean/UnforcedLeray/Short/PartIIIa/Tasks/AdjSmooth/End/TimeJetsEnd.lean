import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_2
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.HkAllOf
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.HkAllLinear
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.XDerivLinear
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerVelIsBS
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.CoeffMul
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.KerMul
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd.adjLopTestedW
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd.coeffMulDerivIco
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd.kerMulDerivIco
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd.testedOfXDerivIco
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd.xDerivOfTestedIco
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd.trainVCoeffW
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd.trainECoeffW

/-!
# `PartIII-a:T21/2/7/2/1/2/1/2`: `AdjTimeJetsEnd` from the leaves

Assembly of `adjTimeJetsEnd_of_leaves` (Sub file) with the proved leaves: the generic leaves
(`adjHkAllOf`, `adjHkAllLinear`, `hasXDerivOnLinear`, `kerVelIsBS`, `adjHkAllCoeffMul`,
`adjHkAllKerMul`) from the Interior TimeJets folder, and the seven End leaves. Source
`the November 2 reference manuscript` 3060-3061.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`AdjTimeJetsEnd` from the leaves**, for `m > 8` (`m > 1` is what the leaves need). -/
theorem adjTimeJetsEnd (m : ℝ) (hm : 8 < m) : UnforcedLeray.Short.IIIa.AdjTimeJetsEnd m :=
  adjTimeJetsEnd_of_leaves m adjHkAllOf xDerivOfTestedIco testedOfXDerivIco adjHkAllLinear
    hasXDerivOnLinear kerVelIsBS (adjLopTestedW m) adjHkAllCoeffMul coeffMulDerivIco
    (adjHkAllKerMul m (by linarith)) (kerMulDerivIco m (by linarith)) (trainVCoeffW m)
    (trainECoeffW m)

end UnforcedLeray.Short.IIIa
