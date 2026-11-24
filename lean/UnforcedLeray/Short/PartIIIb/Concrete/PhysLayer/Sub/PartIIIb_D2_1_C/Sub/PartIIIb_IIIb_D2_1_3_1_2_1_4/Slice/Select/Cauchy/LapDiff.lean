import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.Integ

/-!
# `cLapDiff`: linearity of the slice Laplacian identity (source 1351-1362, 1470-1480)

Integrability of `f · Δθ` and `h · θ` for `f, h ∈ L²` comes from `integrable_sum_L2` in `Integ.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem cLapDiff : CLapDiff := by
  unfold CLapDiff
  intro ν f₁ f₂ h₁ h₂ hf₁ hf₂ hh₁ hh₂ H₁ H₂ θ hθ hθc
  have I1 : Integrable (fun y => ∑ i : Fin 3, f₁ y i * lapS θ y i) volume :=
    integrable_sum_L2 hf₁ (fun i y => lapS θ y i)
      (fun i => vcomp_cont (vlap_contDiff hθ).continuous i) (fun i => vcomp_cs (vlap_cs hθc) i)
  have I2 : Integrable (fun y => ∑ i : Fin 3, f₂ y i * lapS θ y i) volume :=
    integrable_sum_L2 hf₂ (fun i y => lapS θ y i)
      (fun i => vcomp_cont (vlap_contDiff hθ).continuous i) (fun i => vcomp_cs (vlap_cs hθc) i)
  have J1 : Integrable (fun y => ∑ i : Fin 3, h₁ y i * θ y i) volume :=
    integrable_sum_L2 hh₁ (fun i y => θ y i)
      (fun i => vcomp_cont hθ.continuous i) (fun i => vcomp_cs hθc i)
  have J2 : Integrable (fun y => ∑ i : Fin 3, h₂ y i * θ y i) volume :=
    integrable_sum_L2 hh₂ (fun i y => θ y i)
      (fun i => vcomp_cont hθ.continuous i) (fun i => vcomp_cs hθc i)
  have eL : ∫ y : Space, ∑ i : Fin 3, (f₁ - f₂) y i * lapS θ y i
      = (∫ y : Space, ∑ i : Fin 3, f₁ y i * lapS θ y i)
        - ∫ y : Space, ∑ i : Fin 3, f₂ y i * lapS θ y i := by
    rw [← integral_sub I1 I2]
    congr 1
    funext y
    simp only [Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have eR : ∫ y : Space, ∑ i : Fin 3, (h₁ - h₂) y i * θ y i
      = (∫ y : Space, ∑ i : Fin 3, h₁ y i * θ y i)
        - ∫ y : Space, ∑ i : Fin 3, h₂ y i * θ y i := by
    rw [← integral_sub J1 J2]
    congr 1
    funext y
    simp only [Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [eL, eR, mul_sub, H₁ θ hθ hθc, H₂ θ hθ hθc]

end UnforcedLeray.Short.PartIIIb.Concrete
