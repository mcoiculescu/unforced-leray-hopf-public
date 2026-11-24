import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_11_2_2.Of
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.SplitMult
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_2
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_3
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_9

/-!
# `PartIII-b:C/rep/11/2/2`: assembly of `nearMUGainBound`

Source `the November 2 reference manuscript` 2703-2713, 2758-2778.
`nearMUGainBound_of_raw` is the conditional assembly from the raw-lift bounds
`RawCoeffLate`, `RawCoeffEarly` (tasks `PartIII-a:T23/1`, `T23/2`); `nearMUGainBound` is the
unconditional target.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst

theorem nearMUGainBound_of_raw (h1 : UnforcedLeray.Short.IIIa.RawCoeffLate)
    (h2 : UnforcedLeray.Short.IIIa.RawCoeffEarly) (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp) : D.NearMUGainBound :=
  nearMUGainBound_of
    (NearInst.splitMultBound_of
      (UnforcedLeray.Short.IIIa.stressCoefficients_of h1 h2
        UnforcedLeray.Short.IIIa.inletCoeffBounds)) D hst

theorem nearMUGainBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.NearMUGainBound :=
  nearMUGainBound_of_raw UnforcedLeray.Short.IIIa.rawCoeffLate
    UnforcedLeray.Short.IIIa.rawCoeffEarly D hst

end UnforcedLeray.Short.PartIIIb.Concrete

end
