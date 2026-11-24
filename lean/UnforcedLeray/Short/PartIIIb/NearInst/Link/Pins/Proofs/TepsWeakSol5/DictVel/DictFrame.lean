import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_1

/-!
# `DictFrame` (task `PartIII-b:C/near/pins/3/5/1/4`)

Source `the November 2 reference manuscript` line 2683: the complex meridional
frame at `x = ε y` is the complexified real frame at `y`:
`frameC (ε • y) (merC v) = realC (frameL y v)`.

Components: `unitRC (ε y) = realC (eR y)` and `unitZC = realC e3`, since
`(ε y)₀ / radius (ε y) = y₀ / ϱ y` (the factor `ε` cancels in `radius (ε y) = ε ϱ y`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem dictFrame : DictFrame := by
  intro ε hε y hy v
  have hε0 : ε ≠ 0 := hε.ne'
  have hϱ : 0 < UnforcedLeray.Axi.ϱ y := UnforcedLeray.Axi.ϱ_pos hy
  have hϱ0 : UnforcedLeray.Axi.ϱ y ≠ 0 := hϱ.ne'
  have hrad : UnforcedLeray.B0220.radius (ε • y) = ε * UnforcedLeray.Axi.ϱ y := by
    have h1 : UnforcedLeray.B0220.radius (ε • y) = UnforcedLeray.Axi.ϱ (ε • y) := rfl
    rw [h1, UnforcedLeray.Axi.ϱ_smul, abs_of_pos hε]
  ext i
  fin_cases i
  all_goals
    simp [UnforcedLeray.B0223.frameC_apply, UnforcedLeray.B0223.unitRC,
      UnforcedLeray.B0223.unitZC, UnforcedLeray.B0412.realC_apply, UnforcedLeray.Axi.frameL_apply,
      merC, hrad, UnforcedLeray.Axi.eR_apply_zero, UnforcedLeray.Axi.eR_apply_one,
      UnforcedLeray.Axi.eR_apply_two, UnforcedLeray.Axi.e3_apply, hε0, hϱ0,
      mul_div_mul_left]

end UnforcedLeray.Short.PartIIIb.NearInst
