import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelDivFree
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjFubini
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar

/-!
# `PartIII-a:T21/2/2/3/6/1/1/2`: `KerVelDivFree0` from the `d ≥ 1` divergence-free statement

Source: `the November 2 reference manuscript` lines 2875-2896, 3052-3057.
Composition of the compiled scaling reduction `kerVelDivFree0_of` with `kerVelDivFree_of`,
fed by `kerAdjFubini_of` and `kerDivPointwise_of` (both from `kerNearFar`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem kerVelDivFree0 : UnforcedLeray.Short.IIIa.AdjE1.KerVelDivFree0 :=
  kerVelDivFree0_of (UnforcedLeray.Short.IIIa.kerVelDivFree_of
    (UnforcedLeray.Short.IIIa.kerAdjFubini_of UnforcedLeray.Short.IIIa.kerNearFar)
    (UnforcedLeray.Short.IIIa.kerDivPointwise_of UnforcedLeray.Short.IIIa.kerNearFar))

end UnforcedLeray.Short.IIIa.AdjE1

#print axioms UnforcedLeray.Short.IIIa.AdjE1.kerVelDivFree0
