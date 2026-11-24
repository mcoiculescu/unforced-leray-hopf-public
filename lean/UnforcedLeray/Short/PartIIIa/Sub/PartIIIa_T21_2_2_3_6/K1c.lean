import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6_1_1_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.ApproxId.Formula
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.ApproxId.Integrable
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.ApproxId.Mass
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.ApproxId.Far

/-!
# `PartIII-a:T21/2/2/3/6/1/1/3`: leaf `KerVelCurl0` from the four Laplacian leaves

Source: `the November 2 reference manuscript` lines 2081-2084, 3052-3057, 3121.
Composition of the compiled assembly `kerVelCurl0_of_leaves` with the four analytic leaves
`kerLapFormula`, `kerLapInt`, `kerLapMass`, `kerLapFar`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem kerVelCurl0 : UnforcedLeray.Short.IIIa.AdjE1.KerVelCurl0 :=
  UnforcedLeray.Short.IIIa.kerVelCurl0_of_leaves UnforcedLeray.Short.IIIa.kerLapFormula
    UnforcedLeray.Short.IIIa.kerLapInt UnforcedLeray.Short.IIIa.kerLapMass
    UnforcedLeray.Short.IIIa.kerLapFar

end UnforcedLeray.Short.IIIa.AdjE1

#print axioms UnforcedLeray.Short.IIIa.AdjE1.kerVelCurl0
