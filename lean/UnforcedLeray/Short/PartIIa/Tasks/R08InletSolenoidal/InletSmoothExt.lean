import UnforcedLeray.Short.PartIIa.Sub.R08_2
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.ThetaRegular
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.ClosedForm
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.FlatSmul
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.FlatAddCongr
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.TameInvRho
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.TameCoord
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.TameLog
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.TameCompBdd
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.FlatExpOfTame
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt.AxisFlatSmooth

/-!
# Part II-a, task `PartII-a:R08` (inlet solenoidal): smooth extension of the inlet

Source of record: `the November 2 reference manuscript`, lines 1330-1334.

Target: `UnforcedLeray.Short.PartIIa.InletSmoothExt` (`Sub/R08.lean`). The proof is the conditional
theorem `inletSmoothExt_of_sub` (`Sub/R08_2.lean`) applied to the ten leaf Props, each proved in its
own module under `Tasks/R08InletSolenoidal/InletSmoothExt/`.
-/

namespace UnforcedLeray.Short.PartIIa

theorem inletSmoothExt_proof : UnforcedLeray.Short.PartIIa.InletSmoothExt :=
  inletSmoothExt_of_sub thetaRegular inletRawClosedForm flatSmul flatAddCongr tameInvRho
    tameCoord tameLog tameCompBdd flatExpOfTame axisFlatSmooth

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.inletSmoothExt_proof
