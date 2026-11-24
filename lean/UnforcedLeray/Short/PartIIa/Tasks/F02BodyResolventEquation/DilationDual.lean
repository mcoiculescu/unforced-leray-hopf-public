import UnforcedLeray.Short.PartIIa.Sub.F02

/-!
# Part II-a, task `PartII-a:F02/2`: dilations under the spatial pairing

Source of record: `the November 2 reference manuscript`, lines 1363-1370
(the dilation `y ↦ e^{t/2} y` in the formula for `S(t)`).

Proves the Prop `DilationDual` of `Sub/F02.lean`: for `b > 0`,
`∫ ⟪u(y), a h(b y)⟫ dy = a b⁻³ ∫ ⟪u(b⁻¹ z), h(z)⟫ dz`. No integrability is needed:
the substitution `z = b y` is `Measure.integral_comp_smul_of_nonneg`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartIIa

/-- **Dilations under the pairing** (task `PartII-a:F02/2`), proved: the Prop `DilationDual`. -/
theorem dilationDual : DilationDual := by
  unfold DilationDual
  intro a b hb u h
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  -- Pointwise: the dilated argument `b • y` is undone by `b⁻¹ • ·` inside `u`.
  have hL : ∀ y : Space, inner ℝ (u y) (SpatialScaling.spatialScale a b h y) =
      inner ℝ (u (b⁻¹ • (b • y))) (a • h (b • y)) := by
    intro y
    simp only [SpatialScaling.spatialScale, inv_smul_smul₀ hb.ne']
  -- The amplitude `a` leaves the inner product.
  have hR : ∀ z : Space, inner ℝ (u (b⁻¹ • z)) (a • h z) =
      a * inner ℝ (u (b⁻¹ • z)) (h z) :=
    fun z => real_inner_smul_right _ _ _
  -- Change of variables `z = b • y` with the Jacobian `|(b³)⁻¹| = (b³)⁻¹`.
  have hJac : ∫ y : Space, inner ℝ (u (b⁻¹ • (b • y))) (a • h (b • y)) =
      (b ^ 3)⁻¹ * ∫ z : Space, inner ℝ (u (b⁻¹ • z)) (a • h z) := by
    have key := Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
      (fun z : Space => inner ℝ (u (b⁻¹ • z)) (a • h z)) b (hR := hb.le)
    rw [hd] at key
    rw [key, smul_eq_mul]
  simp_rw [hL]
  rw [hJac]
  simp_rw [hR]
  rw [integral_const_mul]
  ring

end UnforcedLeray.Short.PartIIa
