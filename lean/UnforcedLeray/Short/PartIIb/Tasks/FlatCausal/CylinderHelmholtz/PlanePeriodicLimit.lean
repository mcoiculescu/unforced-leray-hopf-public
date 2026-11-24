import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Sequence
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract

/-!
# Part II-b, task `PartII-b:T12/1/4` (`planePeriodicLimit`): assembly

Source of record: `the November 2 reference manuscript` lines 1933-1935.
The two leaves `pplSequence` (`PartII-b:T12/1/4/1`) and `pplExtract` (`PartII-b:T12/1/4/2`) are
combined by `planePeriodicLimit_of` from the decomposition file `Sub/PartII-b_T12_1_4.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem planePeriodicLimit : UnforcedLeray.Short.IIb.PlanePeriodicLimit :=
  planePeriodicLimit_of pplSequence pplExtract

end UnforcedLeray.Short.IIb

end
