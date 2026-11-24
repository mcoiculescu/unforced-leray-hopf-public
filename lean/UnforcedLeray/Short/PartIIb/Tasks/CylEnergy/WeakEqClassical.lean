import UnforcedLeray.Short.PartIIb.Sub.T22_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N4
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N5

/-!


Applies `cylWeakEqClassical_of_parts` to the six named lemmas N1, N1p, N2, N3, N4, N5.
-/

theorem cylWeakEqClassical : UnforcedLeray.Short.IIb.CylWeakEqClassical :=
  UnforcedLeray.Short.IIb.cylWeakEqClassical_of_parts
    UnforcedLeray.Short.IIb.cylWeakTimeDep
    UnforcedLeray.Short.IIb.cylRegularTimeDep
    UnforcedLeray.Short.IIb.cylBackwardSolve
    UnforcedLeray.Short.IIb.cylFundLemma
    UnforcedLeray.Short.IIb.cylTrainBound
    UnforcedLeray.Short.IIb.cylRegularMem
