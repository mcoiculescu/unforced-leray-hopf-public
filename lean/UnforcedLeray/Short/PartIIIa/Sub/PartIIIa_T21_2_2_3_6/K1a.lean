import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarField
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar

/-!
# `PartIII-a:T21/2/2/3/6/1/1/1`: `KerVelFarField0` from the `d ≥ 1` far field

Source: `the November 2 reference manuscript` lines 2875-2896, 3052-3057.
Composition of the compiled scaling reduction `kerVelFarField0_of` with the far-field
`kerVelFarField_of` (from `kerNearFar`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem kerVelFarField0 : UnforcedLeray.Short.IIIa.AdjE1.KerVelFarField0 :=
  kerVelFarField0_of (UnforcedLeray.Short.IIIa.kerVelFarField_of UnforcedLeray.Short.IIIa.kerNearFar)

end UnforcedLeray.Short.IIIa.AdjE1

#print axioms UnforcedLeray.Short.IIIa.AdjE1.kerVelFarField0
