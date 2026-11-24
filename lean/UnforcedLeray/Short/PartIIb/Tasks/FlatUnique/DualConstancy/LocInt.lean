import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.LocInt.Meas
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.LocInt.Pointwise
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.LocInt.AFinite
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.LocInt.BFinite
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.LocInt.ABMeas
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.LocInt.SigmaHolder

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Leaf `PartII-b:T11/2/1` (`DualFLocInt`) from the six leaves. -/
theorem dualFLocInt_proof : UnforcedLeray.Short.IIb.DualFLocInt :=
  dualFLocInt_of DualFMeas_proof DualFPointwise_proof DualFAFinite_proof DualFBFinite_proof
    DualFABMeas_proof SigmaHolder_proof

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.dualFLocInt_proof
