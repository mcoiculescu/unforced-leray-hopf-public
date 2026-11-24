import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_1

/-!
# `DictScalar` (task `PartIII-b:C/near/pins/3/5/1/5`)

Source `the November 2 reference manuscript` line 2683: `liftA (ε y) = √(age ε⁻¹ y)`.
Both sides equal `(ε ϱ y)⁻¹`: `radius (ε • y) = ε * ϱ y` (`Axi.ϱ_smul`, `ε > 0`), and
`√(age R y) = R / ϱ y` for `R > 0` (`Axi.sqrt_age`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem dictScalar : DictScalar := by
  intro ε hε y hy
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hrad : UnforcedLeray.B0220.radius (ε • y) = ε * UnforcedLeray.Axi.ϱ y := by
    have h1 : UnforcedLeray.B0220.radius (ε • y) = UnforcedLeray.Axi.ϱ (ε • y) := rfl
    rw [h1, UnforcedLeray.Axi.ϱ_smul, abs_of_pos hε]
  unfold UnforcedLeray.B0220.liftA
  rw [hrad, UnforcedLeray.Axi.sqrt_age hR hy, mul_inv, div_eq_mul_inv]

end UnforcedLeray.Short.PartIIIb.NearInst
