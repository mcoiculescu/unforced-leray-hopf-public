import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy.Integ

/-!
# `cWeakDiff`: linearity of the weak-derivative identity (source 1351-1362, 1470-1480)

Integrability of `f · ∂ⱼθ` and `g · θ` for `f, g ∈ L²` comes from `integrable_sum_L2` in `Integ.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem wd_contDiff {θ : Space → CVec3} (hθ : ContDiff ℝ ∞ θ) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))) := by
  have hθi : ContDiff ℝ ∞ (fun z => θ z i) :=
    ((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hθ
  exact (hθi.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cWeakDiff : CWeakDiff := by
  unfold CWeakDiff
  intro j f₁ f₂ g₁ g₂ hf₁ hf₂ hg₁ hg₂ H₁ H₂ θ hθ hθc
  have I1 : Integrable (fun y => ∑ i : Fin 3, f₁ y i
      * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))) volume :=
    integrable_sum_L2 hf₁ (fun i y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
      (fun i => (wd_contDiff hθ i j).continuous)
      (fun i => HasCompactSupport.fderiv_apply ℝ (vcomp_cs hθc i) (EuclideanSpace.single j (1 : ℝ)))
  have I2 : Integrable (fun y => ∑ i : Fin 3, f₂ y i
      * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))) volume :=
    integrable_sum_L2 hf₂ (fun i y => fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
      (fun i => (wd_contDiff hθ i j).continuous)
      (fun i => HasCompactSupport.fderiv_apply ℝ (vcomp_cs hθc i) (EuclideanSpace.single j (1 : ℝ)))
  have J1 : Integrable (fun y => ∑ i : Fin 3, g₁ y i * θ y i) volume :=
    integrable_sum_L2 hg₁ (fun i y => θ y i)
      (fun i => vcomp_cont hθ.continuous i) (fun i => vcomp_cs hθc i)
  have J2 : Integrable (fun y => ∑ i : Fin 3, g₂ y i * θ y i) volume :=
    integrable_sum_L2 hg₂ (fun i y => θ y i)
      (fun i => vcomp_cont hθ.continuous i) (fun i => vcomp_cs hθc i)
  have eL : ∫ y : Space, ∑ i : Fin 3, (f₁ - f₂) y i
      * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ))
      = (∫ y : Space, ∑ i : Fin 3, f₁ y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)))
        - ∫ y : Space, ∑ i : Fin 3, f₂ y i * fderiv ℝ (fun z => θ z i) y (EuclideanSpace.single j (1 : ℝ)) := by
    rw [← integral_sub I1 I2]
    congr 1
    funext y
    simp only [Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have eR : ∫ y : Space, ∑ i : Fin 3, (g₁ - g₂) y i * θ y i
      = (∫ y : Space, ∑ i : Fin 3, g₁ y i * θ y i) - ∫ y : Space, ∑ i : Fin 3, g₂ y i * θ y i := by
    rw [← integral_sub J1 J2]
    congr 1
    funext y
    simp only [Pi.sub_apply, PiLp.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have e1 := H₁ θ hθ hθc
  have e2 := H₂ θ hθ hθc
  rw [eL, eR]
  linear_combination e1 - e2

end UnforcedLeray.Short.PartIIIb.Concrete
