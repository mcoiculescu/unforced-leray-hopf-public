import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_4_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Sequence.CutNorm
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Sequence.AvgBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Sequence.AvgDivFree
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Sequence.AvgTelescope
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Sequence.AvgDual
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlanePeriodicLimit.Sequence.DualLimit
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem pplSequence : UnforcedLeray.Short.IIb.PPLSequence :=
  pplSequence_of ppl_cut_norm ppl_avg_bound ppl_avg_div_free ppl_avg_telescope ppl_avg_dual
    ppl_dual_limit planeHelmholtzLr

end UnforcedLeray.Short.IIb

end
