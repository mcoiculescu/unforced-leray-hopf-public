import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T08_1_2
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.NicePhaseTest
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.DriftPtw
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.DriftIBP

/-!
# Part II-b, task `PartII-b:T08/1/2`: `DriftSmoothPt` from its three leaves

Source of record: `the November 2 reference manuscript`, lines 1912-1915.

Target: `driftSmoothPt_proof : UnforcedLeray.Short.IIb.DriftSmoothPt`.

The conditional reduction `driftSmoothPt_of` (in `Sub/PartIIb_T08_1_2.lean`) takes the three
leaf statements `NvCNicePhaseTest` (`T08/1/2/1`), `NvCDriftPtw` (`T08/1/2/2`) and `DriftIBP`
(`T08/1/2/3`) as hypotheses. Each leaf is supplied by its proved theorem.
-/

set_option autoImplicit false

noncomputable section

theorem driftSmoothPt_proof : UnforcedLeray.Short.IIb.DriftSmoothPt :=
  UnforcedLeray.Short.IIb.driftSmoothPt_of
    UnforcedLeray.Short.IIb.nvCNicePhaseTest_proof
    nvCDriftPtw_proof
    driftIBP_proof

#print axioms driftSmoothPt_proof
