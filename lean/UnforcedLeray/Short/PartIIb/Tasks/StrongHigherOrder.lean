import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.IteratedDiffEq
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.CorrSliceContDiff
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.RawAndInletL4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawDerivBdd

/-!
# `PartII-b:S2`: `StrongAllOrders`

Source of record: `the November 2 reference manuscript`, lines 2541-2562.

Assembles `strongAllOrders_of` from `strongAllOrders_of_leaves`, `rawJointSmooth`,
`rawDerivBdd`, `iteratedDiffEqInYq_proof`, `corrSliceIteratedContDiff_proof`,
and `rawAndInletIteratedL4Bound_proof`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem strongAllOrders_of (h4 : UnforcedLeray.Short.IIb.AffineInletFacts)
    (hQ1 : UnforcedLeray.Short.IIb.QuadBound)
    (hS1 : UnforcedLeray.Short.IIb.StrongFirstDerivative) :
    UnforcedLeray.Short.IIb.StrongAllOrders :=
  strongAllOrders_of_leaves
    UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth
    UnforcedLeray.Short.PartIIIb.Concrete.rawDerivBdd
    (iteratedDiffEqInYq_proof hS1)
    corrSliceIteratedContDiff_proof
    rawAndInletIteratedL4Bound_proof
    h4 hQ1 hS1

end UnforcedLeray.Short.IIb
