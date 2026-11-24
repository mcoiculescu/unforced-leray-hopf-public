import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_1_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.Sums
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.LhsCont
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx.RhsCont

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
Assembly only: `cylTdApprox_of` (Sub/PartIIb_T22_2_1_2.lean) applied to
`cylTdApproxSums`, `cylTdLhsCont` and `cylTdRhsCont`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Approximation of a time-dependent test by separated sums (task `PartII-b:T22/2/1/2`). -/
theorem cylTdApprox : UnforcedLeray.Short.IIb.CylTdApprox :=
  cylTdApprox_of cylTdApproxSums cylTdLhsCont cylTdRhsCont

end UnforcedLeray.Short.IIb
