import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_1_15
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardLimit.Deriv
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardLimit.Cont
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardLimit.SizeAux
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardLimit.ConvLinear
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardLimit.Fix
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.ConvRegular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TranspClass

/-!


Proves `PicardLimit` (`Sub/T22_1/Plan.lean`) from the leaves `picLimDeriv_proof`,
`picLimCont_proof`, `picLimSize_proof`, `convLinear_proof`, `picLimFix_proof`, together with
`convRegular` and `transpClass`, via `picardLimit_of` (`Sub/PartII-b_T22_1_15.lean`).
Source `the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

/-- **`PartII-b:T22/1/15`** `PicardLimit`, assembled from its five leaves and the two
`ConvRegular` / `TranspClass` inputs. -/
theorem picardLimit : UnforcedLeray.Short.IIb.CylPDE.PicardLimit :=
  picardLimit_of picLimDeriv_proof picLimCont_proof picLimSize_proof convRegular transpClass
    convLinear_proof picLimFix_proof

end UnforcedLeray.Short.IIb.CylPDE

#print axioms UnforcedLeray.Short.IIb.CylPDE.picardLimit
