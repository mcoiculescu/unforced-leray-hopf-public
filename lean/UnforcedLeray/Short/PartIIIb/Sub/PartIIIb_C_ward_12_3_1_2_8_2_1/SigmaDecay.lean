import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3.PiDecay
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3.ProjPotDtau
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3.ProjPotPeriodic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3.L0TscalSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3.L0TscalPeriodic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3.L0TscalBound

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/3` (`sigmaDecay`): decay of the correction scalar

Source `shorter-proof-2026-11-02.tex` lines 1393-1400, 1409-1412. The six hypotheses of
`sigmaDecay_of` are supplied by the lemma files `PiDecay`, `ProjPotDtau`, `ProjPotPeriodic`,
`L0TscalSmooth`, `L0TscalPeriodic` and `L0TscalBound` of the folder `PartIII-b_C_ward_12_3_1_2_8_2_1_1_3`.
-/

set_option autoImplicit false

noncomputable section

theorem sigmaDecay : UnforcedLeray.Short.PartIIIb.Concrete.SigmaDecay :=
  UnforcedLeray.Short.PartIIIb.Concrete.sigmaDecay_of
    UnforcedLeray.Short.PartIIIb.Concrete.piDecay
    projPotDtau
    UnforcedLeray.Short.PartIIIb.Concrete.projPotPeriodic
    UnforcedLeray.Short.PartIIIb.Concrete.l0TscalSmooth
    l0TscalPeriodic
    l0TscalBound
