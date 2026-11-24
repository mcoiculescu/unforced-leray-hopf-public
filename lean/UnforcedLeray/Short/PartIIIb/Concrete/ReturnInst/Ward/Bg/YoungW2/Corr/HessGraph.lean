import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.HessY
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.HessEq

/-!
# `BgCorrHessGraph` from `BgCorrHessY` and `BgCorrHessEq` (source 2525-2562, 2607-2609)

Assembly: `bgCorrHessGraph_of` (Sub/PartIII-b_C_ward_12_3_2.lean) applied to the two leaves
`bgCorrHessY` (HessY.lean) and `bgCorrHessEq` (HessEq.lean).
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `BgCorrHessGraph` (source 2525-2562, 2607-2609). -/
theorem bgCorrHessGraph : BgCorrHessGraph :=
  bgCorrHessGraph_of bgCorrHessY bgCorrHessEq

end UnforcedLeray.Short.PartIIIb.Concrete
