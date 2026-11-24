import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem uVDerivLeaf : UVDerivLeaf := by
  intro y hy
  have hy' : y ∉ Axi.axis := notAxis_of_hRad hy
  have hρ0 : Axi.ϱ y ≠ 0 := Axi.ϱ_ne_zero hy'
  have hsq : Axi.ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Axi.ϱ_sq y
  have hinv : HasFDerivAt (fun z : Space => (Axi.ϱ z)⁻¹)
      ((-(Axi.ϱ y ^ 2)⁻¹) • Axi.ϱD y) y :=
    (hasDerivAt_inv hρ0).comp_hasFDerivAt y (Axi.hasFDerivAt_ϱ hy')
  have hp0 : HasFDerivAt (fun z : Space => z 0)
      (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have hp1 : HasFDerivAt (fun z : Space => z 1)
      (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have h0 : HasFDerivAt (fun z : Space => z 0 * (Axi.ϱ z)⁻¹)
      (y 0 • ((-(Axi.ϱ y ^ 2)⁻¹) • Axi.ϱD y) +
        (Axi.ϱ y)⁻¹ • (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ)) y :=
    hp0.mul hinv
  have h1 : HasFDerivAt (fun z : Space => z 1 * (Axi.ϱ z)⁻¹)
      (y 1 • ((-(Axi.ϱ y ^ 2)⁻¹) • Axi.ϱD y) +
        (Axi.ϱ y)⁻¹ • (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)) y :=
    hp1.mul hinv
  have e0 : (fun z : Space => z 0 / hRad z) = fun z => z 0 * (Axi.ϱ z)⁻¹ := by
    funext z; rw [div_eq_mul_inv]; rfl
  have e1 : (fun z : Space => z 1 / hRad z) = fun z => z 1 * (Axi.ϱ z)⁻¹ := by
    funext z; rw [div_eq_mul_inv]; rfl
  rw [e0, e1, hRad_eq]
  refine ⟨h0.differentiableAt, h1.differentiableAt, ?_, ?_⟩
  · intro w
    rw [h0.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul,
      Axi.ϱD_apply, EuclideanSpace.coe_proj]
    field_simp
    linear_combination (w 0) * hsq
  · intro w
    rw [h1.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul,
      Axi.ϱD_apply, EuclideanSpace.coe_proj]
    field_simp
    linear_combination (w 1) * hsq

end UnforcedLeray.Short.PartIIIb.NearInst
