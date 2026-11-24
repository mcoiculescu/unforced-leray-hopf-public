import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3_1
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutE1DerivUnder
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.LadDtRegular
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutIBP

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- `PartIII-a:T21/2/7/2/3/1`: the derivative of the cut energy, from its three leaves
(`cutE1DerivUnder`, `ladDtRegular`, `cutIBP`) via `cutE1Deriv_of`. -/
theorem cutE1Deriv : UnforcedLeray.Short.IIIa.CutE1Deriv :=
  UnforcedLeray.Short.IIIa.cutE1Deriv_of cutE1DerivUnder ladDtRegular cutIBP

end UnforcedLeray.Short.IIIa
