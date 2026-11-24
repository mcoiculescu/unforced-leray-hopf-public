import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1a
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1b
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.K1c

/-!
# `PartIII-a:T21/2/2/3/6/1`: leaf `KernelBSExists` from the three leaves K1a, K1b, K1c

Source: `the November 2 reference manuscript` lines 2875-2896 (periodic kernel
`K_d`), 3052-3057.  Composition of the compiled assembly `kernelBSExists_of` (in
`PartIII-a_T21_2_2_3_6_1_1`) with the three leaves `kerVelFarField0` (K1a, far field),
`kerVelDivFree0` (K1b, weak divergence-freeness) and `kerVelCurl0` (K1c, weak curl).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

theorem kernelBSExists : UnforcedLeray.Short.IIIa.AdjE1.KernelBSExists :=
  UnforcedLeray.Short.IIIa.AdjE1.kernelBSExists_of
    UnforcedLeray.Short.IIIa.AdjE1.kerVelFarField0
    UnforcedLeray.Short.IIIa.AdjE1.kerVelDivFree0
    UnforcedLeray.Short.IIIa.AdjE1.kerVelCurl0

#print axioms kernelBSExists
