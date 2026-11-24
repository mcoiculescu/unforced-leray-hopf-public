import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2.VtvRLinAE

/-!
# `VtvPSub`: `p_s` is a seminorm on cylinder tests (source 4610)

`p_s(φ) = ∫_{(0,s]} ‖R(r,φ)‖ dr`. Linearity of `φ ↦ R(r,φ)` holds for a.e. `r > 0`
(`vtvRLinAE`), and `r ↦ R(r,φ)` is integrable on `(0,s]` (last clause of `VtvHyps`), so the
triangle inequality and homogeneity pass through the integral.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvPSub : VtvPSub := by
  intro ν c μ tr ω g b G f H s hs φ ψ hφ hψ
  have hLin : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) s)), ∀ φ ψ : ℝ × ℝ → ℝ,
      B0579.IsCylTest c φ → B0579.IsCylTest c ψ → ∀ a : ℝ,
        vtvR μ tr ω g b r (φ + ψ) = vtvR μ tr ω g b r φ + vtvR μ tr ω g b r ψ ∧
        vtvR μ tr ω g b r (a • φ) = (a : ℂ) * vtvR μ tr ω g b r φ :=
    ae_restrict_of_ae_restrict_of_subset (fun r hr => hr.1) (vtvRLinAE ν c μ tr ω g b G f H)
  have hint : ∀ χ : ℝ × ℝ → ℝ, B0579.IsCylTest c χ →
      IntegrableOn (fun r => vtvR μ tr ω g b r χ) (Ioc 0 s) := by
    intro χ hχ
    obtain ⟨h1, h2, _⟩ := H.2.2.2.2.2.2.2.1 χ hχ s hs
    refine (h1.add h2).congr_fun (fun r _ => ?_) measurableSet_Ioc
    simp only [vtvR, mul_add, Pi.add_apply]
  refine ⟨?_, fun a => ?_⟩
  · simp only [vtvP]
    have hcongr : ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r (φ + ψ)‖ =
        ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r φ + vtvR μ tr ω g b r ψ‖ := by
      refine integral_congr_ae ?_
      filter_upwards [hLin] with r hr
      rw [(hr φ ψ hφ hψ 0).1]
    rw [hcongr]
    calc (∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r φ + vtvR μ tr ω g b r ψ‖)
        ≤ ∫ r in Ioc 0 s, (‖vtvR μ tr ω g b r φ‖ + ‖vtvR μ tr ω g b r ψ‖) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => norm_nonneg _)
            (Integrable.add (Integrable.norm (hint φ hφ)) (Integrable.norm (hint ψ hψ)))
            (Filter.Eventually.of_forall fun r => norm_add_le _ _)
      _ = (∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r φ‖) + (∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r ψ‖) :=
          integral_add (Integrable.norm (hint φ hφ)) (Integrable.norm (hint ψ hψ))
  · simp only [vtvP]
    have hcongr : ∫ r in Ioc 0 s, ‖vtvR μ tr ω g b r (a • φ)‖ =
        ∫ r in Ioc 0 s, |a| * ‖vtvR μ tr ω g b r φ‖ := by
      refine integral_congr_ae ?_
      filter_upwards [hLin] with r hr
      rw [(hr φ φ hφ hφ a).2, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hcongr, integral_const_mul]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
