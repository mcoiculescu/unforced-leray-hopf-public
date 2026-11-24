import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_6
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.RegSmooth
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.RegDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.BandInt
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.LatticeNull
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.GradIBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwiseParts.ApproxId

/-!
# `KerCurlPointwise` from `KerNearFar` (SP 2081-2084, 3121)

Assembly of the curl pointwise identity from the compiled leaves.  The hypothesis `KerNearFar`
is not needed: the band integrability `KerBandInt` and the other leaves are proved outright.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **`KerCurlPointwise`** from the regularised stream function (SP 2081-2084, 3121). -/
theorem kerCurlPointwise_of (h : UnforcedLeray.Short.IIIa.KerNearFar) :
    UnforcedLeray.Short.IIIa.KerCurlPointwise :=
  kerCurlPointwise_of_leaves kerRegSmooth kerRegDeriv kerGradIBP kerApproxId kerBandInt
    kerLatticeNull

end UnforcedLeray.Short.IIIa
