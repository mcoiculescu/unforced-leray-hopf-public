import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.CylUniq
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.FieldBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PairInt
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.Pointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.StrongCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelAdjoint

/-!
# `PartIII-a:T21/2/7/1/7`: `AdjLocalizedCoeff m` (assembly)

Source of record: `the November 2 reference manuscript` (SP) lines 3052-3058
(adjoint localized interaction) and 2875-2896 (periodic kernel `K_c`).

The proof is the term assembly of the compiled component theorems through
`adjLocalizedCoeff_of`: pairing integrability `locPairInt`, pointwise adjoint operators
`locAdjPointwise_of`, and strong continuity `locAdjStrongCont`, with the kernel adjoint
`kernelAdjointBound`, the cylinder fundamental lemma `locCylUniq` and the field bound
`locFieldBound`. No new analysis.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjLocalizedCoeff (m : ℝ) (hm : 8 < m) : AdjLocalizedCoeff m :=
  adjLocalizedCoeff_of m (locPairInt m hm)
    (locAdjPointwise_of m hm (kernelAdjointBound m) locCylUniq (locFieldBound m hm))
    (locAdjStrongCont m hm (kernelAdjointBound m) locCylUniq (locFieldBound m hm))

end UnforcedLeray.Short.IIIa
