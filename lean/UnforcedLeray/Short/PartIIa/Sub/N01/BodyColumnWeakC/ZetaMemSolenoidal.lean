import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.ZetaPhiSolenoidal

/-!
# `PartII-a:N01/9/2/3/1`: `ZetaMemSolenoidal`

Source `the November 2 reference manuscript` lines 1669-1676.
`zetaFn Φ = s^{1/2}Φ` coincides pointwise with the flat-setting test `zetaPhi Φ`
(PartIII-b), whose solenoidality in `solenoidalHC 0 c` is `zetaPhiSolenoidal` (proved there,
by integration by parts slice by slice in `(q,η)`). This file transports that statement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ContDiff
open UnforcedLeray.B0220 (Profile)

namespace UnforcedLeray.Short.PartIIa.N01

theorem zetaFn_eq_zetaPhi_pt (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : Profile) :
    zetaFn Φ p = UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.zetaPhi Φ p := by
  unfold zetaFn UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.zetaPhi
  ext i
  fin_cases i <;> simp

theorem zetaMemSolenoidal : UnforcedLeray.Short.PartIIa.N01.ZetaMemSolenoidal := by
  intro c hc Φ hΦ
  obtain ⟨ζ', hK, hae⟩ :=
    UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.zetaPhiSolenoidal c hc Φ hΦ
  refine ⟨ζ', hK, ?_⟩
  exact hae.mono fun p hp => hp.trans (zetaFn_eq_zetaPhi_pt Φ p).symm

end UnforcedLeray.Short.PartIIa.N01
