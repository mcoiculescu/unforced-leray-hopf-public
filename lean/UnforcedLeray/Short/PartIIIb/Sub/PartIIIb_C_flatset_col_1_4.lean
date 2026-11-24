import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_4.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2

/-!
# `FlatForceCurlTsum` (decomposition of `PartIII-b:C/flatset/col/1/4`)

`PartIII-b_C_flatset_col_1_4/Bounds.lean`: Gaussian polynomial bounds for `ftF1, ftF2, ftD1, ftD2`
and the locally uniform lattice majorant.  `PartIII-b_C_flatset_col_1_4/Of.lean`:
`flatForceCurlTsum_of : FlatForceSmooth → FlatForceCurlTsum` (termwise differentiation of the
lattice sum, source 4597-4608, 4963-4976, 4988).  The unconditional `flatForceCurlTsum` is
`flatForceCurlTsum_of flatForceSmooth` once task `PartIII-b:C/flatset/col/1/2` is done.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatForceCurlTsum : FlatForceCurlTsum := flatForceCurlTsum_of flatForceSmooth

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
