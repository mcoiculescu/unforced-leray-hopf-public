import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.Barrier
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple.ExistsMax
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple.Spatial
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.TrainDriftSmoothBdd
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.CutProps
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Lap.LapLocalSub
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Lap.LapZRegular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Lap.LapZTerminal

/-!


Source: `the November 2 reference manuscript` lines 2085-2093 and 2100-2105.
The statement is discharged by the already-proved `bwdWeightedLap_of` applied to the proved
leaves: the maximum principle (`bwdMaxPrincipleSub_of` from `mpExistsMax`, `mpSpatial`), the
barrier `bwdBarrier`, and `trainDriftSmoothBdd`, `lapLocalSub`, `lapZRegular`, `lapZTerminal`,
`cutProps`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem bwdWeightedLap : UnforcedLeray.Short.IIb.BwdWeightedLap :=
  bwdWeightedLap_of (bwdMaxPrincipleSub_of mpExistsMax mpSpatial) bwdBarrier
    trainDriftSmoothBdd lapLocalSub lapZRegular lapZTerminal cutProps

end UnforcedLeray.Short.IIb

end
