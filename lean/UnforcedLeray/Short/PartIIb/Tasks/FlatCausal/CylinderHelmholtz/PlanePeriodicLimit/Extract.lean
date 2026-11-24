import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.WeakLimit
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.Shift
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.Norm
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.Fold
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.Avg
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.Helm
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Extract.Transfer

/-!
# Part II-b, task `PartII-b:T12/1/4/2` (`pplExtract`): weak-limit extraction assembled from its leaves

Source of record: `the November 2 reference manuscript` lines 1933-1935.
The seven leaves `pplWeakLimit`, `pplShift`, `pplNorm`, `pplFold`, `pplAvg`, `pplHelm`,
`pplTransfer` are combined by `pplExtract_of` from the decomposition file.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem pplExtract : UnforcedLeray.Short.IIb.PPLExtract :=
  pplExtract_of pplWeakLimit pplShift pplNorm pplFold pplAvg pplHelm pplTransfer

end UnforcedLeray.Short.IIb
