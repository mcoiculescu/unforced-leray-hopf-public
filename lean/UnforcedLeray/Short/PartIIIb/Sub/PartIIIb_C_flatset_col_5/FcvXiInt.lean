import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.Unif
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5_4.Cont

/-!
# Proof of `FcvXiInt` (source 4614-4615, 2819-2836)

`ρ ↦ ρ^μ ℓ_ρ(ξ_B(ρ))` is integrable on `(0, s]`.  Assembled from the two analytic lemmas
`fcvEllUnif` (`Sub/PartIII-b_C_flatset_col_5_4/Unif.lean`) and `fcvEllCont`
(`Sub/PartIII-b_C_flatset_col_5_4/Cont.lean`) by `fcvXiInt_of`
(`Sub/PartIII-b_C_flatset_col_5_4.lean`), using the regularity hypothesis `hReg`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem fcvXiInt (hReg : FlatXiRegular) : FcvXiInt := by
  exact fcvXiInt_of hReg fcvEllUnif fcvEllCont

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
