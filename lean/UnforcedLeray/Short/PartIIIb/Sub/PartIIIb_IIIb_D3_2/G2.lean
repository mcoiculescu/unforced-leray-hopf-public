import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2.g2FrozenReduce
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2.g2ModeBounds
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2.g2PairNear
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2.g2SectorOrth

/-!
# `PartIII-b:IIIb-D3/2/G2`: `flatGroupGauss` (source 4650-4654)
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatUnif FlatUnif.G2

/-- Group G2 (the Gaussian comparison, source 4650-4654). -/
theorem flatGroupGauss (D : SeqData) : FlatUnif.GroupGauss D :=
  flatGroupGauss_of g2FrozenReduce g2ModeBounds g2PairNear g2SectorOrth D

end UnforcedLeray.Short.PartIIIb.Concrete
