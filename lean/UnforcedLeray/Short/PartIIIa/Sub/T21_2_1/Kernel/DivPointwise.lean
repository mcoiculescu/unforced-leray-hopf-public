import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_5
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.RegSmooth
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.RegDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.IBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.BandInt
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwiseParts.LatticeNull

/-!


Source: `the November 2 reference manuscript` (SP 2081-2084, 3121), via the
assembly `kerDivPointwise_of_parts` of `Sub/PartIII-a_T21_2_1_2_5.lean` and the five leaves in
`Kernel/DivPointwiseParts/`. The hypothesis `h : KerNearFar` is not needed (the leaves are
unconditional) and is kept only to match the target statement.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem kerDivPointwise_of (h : UnforcedLeray.Short.IIIa.KerNearFar) :
    UnforcedLeray.Short.IIIa.KerDivPointwise :=
  kerDivPointwise_of_parts kerRegSmooth kerRegDeriv kerIBP kerBandInt kerLatticeNull

end UnforcedLeray.Short.IIIa
