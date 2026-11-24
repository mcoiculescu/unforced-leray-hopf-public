import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.Barrier
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple.ExistsMax
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple.Spatial
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.TrainDriftSmoothBdd
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.GradLocalSub
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.GradZRegular
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.GradZTerminal
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad.CutProps

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
The statement is discharged by the already-proved `bwdWeightedGrad_of` applied to the
proved leaves: the maximum principle (`bwdMaxPrincipleSub_of` from `mpExistsMax`, `mpSpatial`),
the barrier `bwdBarrier`, and `trainDriftSmoothBdd`, `gradLocalSub`, `gradZRegular`,
`gradZTerminal`, `cutProps`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem bwdWeightedGrad : UnforcedLeray.Short.IIb.BwdWeightedGrad :=
  bwdWeightedGrad_of (bwdMaxPrincipleSub_of mpExistsMax mpSpatial) bwdBarrier
    trainDriftSmoothBdd gradLocalSub gradZRegular gradZTerminal cutProps

end UnforcedLeray.Short.IIb

end
