import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Dense.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T7
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.T10

/-!
# Symmetric fields are lifts of their chart coefficients (`PartIII-b:IIIb-D2/3/2/11/5`)

Source: `the November 2 reference manuscript`,
2666-2689 (the lift `𝒩_v b = √s(b_r e_r + b_z e_z)`), 121-124 (axisymmetry without swirl).

Off the axis this is `velPhysCoefOf_of` (T7) applied to the swirl-free field, whose frame form
comes from `axiNoSwirl_of_pt` (T10).  On the axis `age R y = R² / ϱ y² = 0` in Lean, so the lift
vanishes, and so does `F` by hypothesis.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem axiLiftOfAxi_proved : AxiLiftOfAxi := by
  unfold AxiLiftOfAxi
  intro R c F hR hc hax hper h0
  unfold IsAxiLift
  intro x
  by_cases hx : x.2 ∈ axis
  · have hϱ : ϱ x.2 = 0 := (mem_axis_iff x.2).1 hx
    have hage : UnforcedLeray.Axi.age R x.2 = 0 := by
      unfold UnforcedLeray.Axi.age
      rw [hϱ]
      simp
    have hz : F x.1 x.2 = 0 := h0 x.1 x.2 hx
    unfold velPhys
    simp only [Nv, hage, Real.sqrt_zero, zero_smul, hz]
  · exact velPhysCoefOf_of R c hR hc F (axiNoSwirl_of_pt F hax) hper x hx

end UnforcedLeray.Short.PartIIIb.Concrete
