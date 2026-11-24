import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4_org_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.CutoffLimit
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.SliceLoc
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.NormSq
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.AgeSlice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.YoungSlice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.Inequalities.GainLocF

/-!
# `PartIII-b:C/near/delta/8/2/3/4/org/3`: `FreeEnergyFlatSq` from the scalar leaves of `T18/3/2`

Source `the November 2 reference manuscript` lines 1686-1689, 3541-3552.
Instantiates `freeEnergyFlatSq_of'` with the proved scalar leaves `IIIa.cutoffLimit`,
`IIIa.sliceLoc`, `IIIa.normSq`, `IIIa.ageSlice`, `IIIa.youngSlice`, `IIIa.gainLocF`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem freeEnergyFlatSq_of (hW : UnforcedLeray.Short.IIIa.WeightedEnergyIdentity) :
    FreeEnergyFlatSq :=
  freeEnergyFlatSq_of' UnforcedLeray.Short.IIIa.cutoffLimit UnforcedLeray.Short.IIIa.sliceLoc
    UnforcedLeray.Short.IIIa.normSq UnforcedLeray.Short.IIIa.ageSlice
    UnforcedLeray.Short.IIIa.youngSlice UnforcedLeray.Short.IIIa.gainLocF hW

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
