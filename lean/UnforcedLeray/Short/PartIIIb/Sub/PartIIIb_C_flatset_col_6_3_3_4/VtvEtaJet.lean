import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.EtaJetPos

/-!
# `vtvEtaJet`: jets of a stream test (source 246-252, 270-288, 4610)

The statement `VtvEtaJet` quantifies over `0 < c`, matching the source choice `c = ν^{-ρ} > 0`.
The proof is the compiled positive-period bound `vtvEtaJet_of_pos`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvEtaJet : VtvEtaJet := by
  intro c hc η h s₁ s₂
  exact vtvEtaJet_of_pos c hc η h s₁ s₂

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

end
