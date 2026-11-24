import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm.ChartNull
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.WeakS
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.Congr

/-!
# Part II-b, task `PartII-b:T08/1`: the drift identity for nice profiles

Source of record: `the November 2 reference manuscript`, lines 1912-1915.

Target: `driftSmooth_proof : UnforcedLeray.Short.IIb.DriftSmooth`.

The conditional reduction `driftSmooth_of` (in `Sub/PartIIb_T08_1.lean`) takes the three leaves
`DriftWeakS` (`T08/1/1`), `DriftSmoothPt` (`T08/1/2`) and `DriftNvCCongr` (`T08/1/3`), together
with `ChartNullPullback` (`T07/8`), as hypotheses. Each is supplied by its proved theorem.
-/

set_option autoImplicit false

noncomputable section

theorem driftSmooth_proof : UnforcedLeray.Short.IIb.DriftSmooth :=
  UnforcedLeray.Short.IIb.driftSmooth_of
    driftWeakS_proof
    driftSmoothPt_proof
    UnforcedLeray.Short.IIb.driftNvCCongr_proof
    UnforcedLeray.Short.IIb.chartNullPullback

#print axioms driftSmooth_proof
