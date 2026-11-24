import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Meas
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Bdd
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarFieldParts.Tail

/-!
# Part III-a, `PartIII-a:T21/2/1/2/7`: `KerVelFarField` from the near/far split

Source of record: `the November 2 reference manuscript` lines 3052-3057, 2084.
Assembly of the three leaves `kerVelMeas`, `kerVelBdd`, `kerVelTail` through
`kerVelFarField_of_leaves`.  The near/far hypothesis `KerNearFar` is not needed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem kerVelFarField_of (h : UnforcedLeray.Short.IIIa.KerNearFar) : UnforcedLeray.Short.IIIa.KerVelFarField :=
  kerVelFarField_of_leaves kerVelMeas kerVelBdd kerVelTail

end UnforcedLeray.Short.IIIa
