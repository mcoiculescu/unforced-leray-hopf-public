import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.WeakQ
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.WeakEta
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.NiceClass
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.WeakCongr
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.Ptwise
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.NvCSmooth
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.Green
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.Congr
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.ChartNull

/-!
# Part II-b, task `PartII-b:T09/5` (`LapSmooth`): composition

Source of record: `the November 2 reference manuscript`, lines 1639-1668
and 1912-1916.

Target: `lapSmooth_proof : UnforcedLeray.Short.IIb.LapSmooth`, obtained from the reduction
`lapSmooth_of` (in `Sub/PartII-b_T09_5.lean`) applied to the seven leaves and to the
`DriftNvC` congruence and `ChartNullPullback` inputs.
-/

set_option autoImplicit false

noncomputable section

theorem lapSmooth_proof : UnforcedLeray.Short.IIb.LapSmooth :=
  UnforcedLeray.Short.IIb.lapSmooth_of
    UnforcedLeray.Short.IIb.lapWeakQ_proof
    UnforcedLeray.Short.IIb.lapWeakEta_proof
    UnforcedLeray.Short.IIb.lapNiceClass_proof
    UnforcedLeray.Short.IIb.weakFOCongr_proof
    UnforcedLeray.Short.IIb.lapPtwise_proof
    UnforcedLeray.Short.IIb.lapNvCSmooth_proof
    UnforcedLeray.Short.IIb.lapGreen_proof
    UnforcedLeray.Short.IIb.driftNvCCongr_proof
    UnforcedLeray.Short.IIb.chartNullPullback

#print axioms lapSmooth_proof
