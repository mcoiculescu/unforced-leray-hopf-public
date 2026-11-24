import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_5.EllCLM
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_5.BochnerInt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_5.TriMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_5.TriBound

/-!
# Proof of `FcvFubini` (source `shorter-proof-2026-11-02.tex` 4610)

The Fubini exchange on the triangle is assembled from the four analytic inputs
`fcvEllCLM`, `fcvBochnerInt`, `fcvTriMeas`, `fcvTriBound` by `fcvFubini_of`
(`Sub/PartIII-b_C_flatset_col_5_5.lean`).  The hypothesis `hReg : FlatXiRegular` is not needed.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem fcvFubini (hReg : FlatXiRegular) : FcvFubini := by
  exact fcvFubini_of fcvEllCLM fcvBochnerInt fcvTriMeas fcvTriBound

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
