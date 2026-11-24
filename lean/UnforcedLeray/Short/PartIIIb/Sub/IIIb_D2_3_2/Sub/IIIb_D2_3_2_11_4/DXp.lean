import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Lap.Trace

/-!
# Equivariance of `(DX + DXᵀ)∇q` (`PartIII-b:IIIb-D2/3/2/11/4`, source 4280-4282, 6314-6316)

`dxpEqv_proved`: `(DX + DXᵀ)∇q` commutes with a linear isometry `g` when `X` commutes with `g`,
`∇q` commutes with `g`, and `DX(gy) = g DX(y) g⁻¹` (`fderivEqv_proved`).  The identity
`⟪v, (DX + DXᵀ)∇q⟫ = ⟪v, DX ∇q⟫ + ⟪DX v, ∇q⟫` (`dxp_inner`) reduces the vector equality to
inner products, which transform by `LinearIsometryEquiv.inner_map_map`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped RealInnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem inner_coord (a b : Space) : ⟪a, b⟫ = ∑ i : Fin 3, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

theorem dxp_inner (X : Space → Space) (q : Space → ℝ) (y v : Space) :
    ⟪v, physDXp X q y⟫ = ⟪v, fderiv ℝ X y (physGrad q y)⟫ +
      ⟪fderiv ℝ X y v, physGrad q y⟫ := by
  have hA : ⟪v, fderiv ℝ X y (physGrad q y)⟫ =
      ∑ j : Fin 3, physGrad q y j * ⟪v, fderiv ℝ X y (coordinateVector j)⟫ := by
    conv_lhs => rw [← sum_coord (physGrad q y)]
    simp only [map_sum, map_smul, inner_sum, real_inner_smul_right]
  have hB : ⟪fderiv ℝ X y v, physGrad q y⟫ =
      ∑ i : Fin 3, v i * ⟪fderiv ℝ X y (coordinateVector i), physGrad q y⟫ := by
    conv_lhs => rw [← sum_coord v]
    simp only [map_sum, map_smul, sum_inner, real_inner_smul_left]
  rw [hA, hB]
  simp only [inner_coord, physDXp, physGrad, physPd, PiLp.toLp_apply, Fin.sum_univ_three]
  ring

theorem dxpEqv_proved : DXpEqv := by
  intro g X q hX _hq hG hgq y
  have hXd : Differentiable ℝ X := hX.differentiable (by norm_num)
  refine ext_inner_left ℝ fun v => ?_
  obtain ⟨u, rfl⟩ : ∃ u, v = g u := ⟨g.symm v, (g.apply_symm_apply v).symm⟩
  rw [dxp_inner X q (g y) (g u), hgq y, fderivEqv_proved g X hXd hG y (physGrad q y),
    fderivEqv_proved g X hXd hG y u]
  simp only [LinearIsometryEquiv.inner_map_map, dxp_inner X q y u]

end UnforcedLeray.Short.PartIIIb.Concrete
