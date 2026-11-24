import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.InterpSepSum
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.InterpApprox
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.ApproxBand
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums.CutTail

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
Assembly only: the decomposition `TdSums.cylTdApproxSums_of` (Sub/PartIIb_T22_2_1_2_1.lean)
is applied to the four leaves `interpSepSum`, `interpApprox`, `approxBand`, `cutTail`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Approximation by separated sums (task `PartII-b:T22/2/1/2/1`). -/
theorem cylTdApproxSums : UnforcedLeray.Short.IIb.CylTdApproxSums :=
  TdSums.cylTdApproxSums_of TdSums.interpSepSum TdSums.interpApprox TdSums.approxBand
    TdSums.cutTail

end UnforcedLeray.Short.IIb
