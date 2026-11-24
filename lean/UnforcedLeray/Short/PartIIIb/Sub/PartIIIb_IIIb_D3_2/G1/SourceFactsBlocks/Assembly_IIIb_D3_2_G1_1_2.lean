import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2_G1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFactsCompl
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFactsAmp

/-!
# `PartIII-b:IIIb-D3/2/G1/1/2`: `G1.RetainedBlocksActual D`

Source: `the November 2 reference manuscript` lines 4366-4406.
Assembles `retainedBlocksActual` from `retainedBlocksActual_of_parts`,
`actualComplIntegralBound`, and `actualAmpIntegralBound`. Placed in
`Assembly_IIIb_D3_2_G1_1_2.lean` to avoid an import cycle with `PartIII-b_IIIb-D3_2_G1_1_2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

theorem retainedBlocksActual (D : SeqData) : G1.RetainedBlocksActual D :=
  retainedBlocksActual_of_parts D (actualComplIntegralBound D) (actualAmpIntegralBound D)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif
