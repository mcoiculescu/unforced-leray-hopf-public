import UnforcedLeray.Short.PartIIb.Sub.T22_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Separated
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1.Approx

/-!


Source: `the November 2 reference manuscript`, lines 2074-2105.
Assembly only: `cylWeakTimeDep_of` (Sub/T22_2_1.lean) applied to
`cylTdSeparated` (N1/Separated.lean, task `PartII-b:T22/2/1/1`) and
`cylTdApprox` (N1/Approx.lean, task `PartII-b:T22/2/1/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Weak identity of `IsFreeCylFlow` against time-dependent tests (task `PartII-b:T22/2/1`). -/
theorem cylWeakTimeDep : UnforcedLeray.Short.IIb.CylWeakTimeDep :=
  cylWeakTimeDep_of cylTdSeparated cylTdApprox

end UnforcedLeray.Short.IIb
