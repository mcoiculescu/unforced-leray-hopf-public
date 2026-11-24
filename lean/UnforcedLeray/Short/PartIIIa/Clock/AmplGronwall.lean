import UnforcedLeray.Short.PartIIIa.Sub.T21_c4
import UnforcedLeray.Short.PartIIIa.Clock.AmplGronwall.KernelBudget
import UnforcedLeray.Short.PartIIIa.Clock.AmplGronwall.CouplingBudget

/-!
# Part III-a, task `PartIII-a:T21/c4`: the scalar amplitude Gronwall budget

Source: `the November 2 reference manuscript` lines 2998-3016. The reduction
`amplitudeGronwall_of` (`Sub/T21_c4.lean`) is applied to the two integral leaves
`amplKernelBudget` (`Clock/AmplGronwall/KernelBudget.lean`) and `amplCouplingBudget`
(`Clock/AmplGronwall/CouplingBudget.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem amplitudeGronwall : UnforcedLeray.Short.IIIa.AmplitudeGronwall :=
  amplitudeGronwall_of amplKernelBudget amplCouplingBudget

end UnforcedLeray.Short.IIIa
