import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p.Slice
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p.LapIBP
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p.TransportIBP
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p.Cont
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p.HasDeriv
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p.RhsBound
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p.FTC

/-!
# Part II-b, task `PartII-b:T22/2/2`: `CylRegularTimeDep` assembled from the leaves

Source of record: `the November 2 reference manuscript`, lines 2074-2105.
The seven leaf theorems (`rtdSlice`, `rtdLapIBP`, `rtdTransportIBP`, `rtdCont`, `rtdHasDeriv`,
`rtdRhsBound`, `rtdFTC`) are fed to the assembly `cylRegularTimeDep_of` of
`Sub/PartIIb_T22_2_2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylRegularTimeDep : UnforcedLeray.Short.IIb.CylRegularTimeDep :=
  cylRegularTimeDep_of rtdSlice rtdLapIBP rtdTransportIBP rtdCont rtdHasDeriv rtdRhsBound rtdFTC

end UnforcedLeray.Short.IIb
