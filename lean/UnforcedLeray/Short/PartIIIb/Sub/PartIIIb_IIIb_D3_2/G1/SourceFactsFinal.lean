import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFacts
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFactsFrozen
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.SourceFactsBlocks.Assembly_IIIb_D3_2_G1_1_2

/-!
# `PartIII-b:IIIb-D3/2/G1/1`: `G1.YoungSourceFacts D`

Assembles `youngSourceFacts` from `G1.youngSourceFacts_of`,
`frozenPairBoundedActual`, and `retainedBlocksActual`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif

theorem youngSourceFacts (D : SeqData) : G1.YoungSourceFacts D :=
  G1.youngSourceFacts_of D (frozenPairBoundedActual D) (retainedBlocksActual D)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif
