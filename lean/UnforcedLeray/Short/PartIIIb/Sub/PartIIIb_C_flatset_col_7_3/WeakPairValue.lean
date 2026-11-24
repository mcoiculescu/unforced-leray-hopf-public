import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.WeakPairValue.resolventTestZetaPhi
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.WeakPairValue.forcedIntegrandSplit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.WeakPairValue.pairHChart
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.WeakPairValue.zetaPhiCellPtInvariant
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.WeakPairValue.weakPairPiecesIntegrable

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `WeakPairValue` from the five leaf facts (source `shorter-proof-2026-11-02.tex` 1650-1656,
1684-1689). -/
theorem weakPairValue : WeakPairValue :=
  weakPairValue_of resolventTestZetaPhi forcedIntegrandSplit pairHChart
    zetaPhiCellPtInvariant weakPairPiecesIntegrable

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
