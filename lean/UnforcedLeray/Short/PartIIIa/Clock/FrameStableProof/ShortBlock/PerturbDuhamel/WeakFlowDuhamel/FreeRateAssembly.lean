import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_5_thread
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf4
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf5

/-!
# `PartIII-a:T21/c3/3/1/1`: `WeakFlowComplPerturbDuhamel`

Source of record: `the November 2 reference manuscript` (SP), lines 2085-2090,
2919-2925, 2937-2958, 2982-2988.

Assembles `weakFlowComplPerturbDuhamel_unconditional` from `weakFlowComplPerturbDuhamel_of_leavesTC`
and the five leaves `Leaf1`..`Leaf5`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem weakFlowComplPerturbDuhamel_unconditional (κ : PlanarFrameKernels) :
    WeakFlowComplPerturbDuhamel κ :=
  WeakFlowDuhamelTC.weakFlowComplPerturbDuhamel_of_leavesTC κ
    ComplFreeRateSub.freeMovingPropagatorExists
    (complMildFreeBound κ)
    ComplFreeRateSub.locInteractionBound
    (ComplFreeRateSub.complForcingMeasurable κ)
    freeFlowAvailExists

end UnforcedLeray.Short.IIIa
