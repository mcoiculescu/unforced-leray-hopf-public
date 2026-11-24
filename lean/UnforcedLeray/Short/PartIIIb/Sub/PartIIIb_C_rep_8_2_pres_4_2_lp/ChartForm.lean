import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp_org
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1

/-!
# Piece 1: the ring-chart form of the phase norm (`PartIII-b:C/rep/8/2/pres/4/2/lp/1`)

Source `the November 2 reference manuscript` 2681-2688.  The chart reading is only
a.e.-measurable for the chart measure `ageμ c (-5/2)`; it is replaced by a measurable version, and
the exceptional chart-null set pulls back to a null set of `(τ, y)` (`chartOfNullPullback`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem chartFormPhaseLr : ChartFormPhaseLr := by
  intro ε c hε hc F hF
  obtain ⟨hmeas, hae⟩ := hF
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by field_simp
  have hP0 : 0 < 2 * c / ε⁻¹ := div_pos (mul_pos two_pos hc) hR
  have hpR : (11 / 4 : ℝ≥0∞).toReal = 11 / 4 := by
    rw [ENNReal.toReal_div]; norm_num
  have hp0 : (11 / 4 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpt : (11 / 4 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  set g : Chart → ℝ := hmeas.mk (ringRead ε⁻¹ F) with hg
  have hgm : Measurable g := hmeas.measurable_mk
  have hge : ringRead ε⁻¹ F =ᵐ[ageμ c (-5 / 2)] g := hmeas.ae_eq_mk
  have hN : ageμ c (-1 / 2) {p | ¬ ringRead ε⁻¹ F p = g p} = 0 :=
    NearInst.ageμ_absCont c (-1 / 2) (-5 / 2) (ae_iff.1 hge)
  have hpull := chartOfNullPullback ε⁻¹ c hR hc _ hN
  have hae' : ∀ᵐ x : ℝ × Space ∂volume, F x.1 x.2 = g (NearInst.chartOf ε⁻¹ c x.2 x.1) := by
    filter_upwards [hae, hpull] with x hx hx'
    rw [hx]
    simpa only [Set.mem_ofPred_eq, not_not] using hx'
  set G : Chart → ℝ≥0∞ := fun p => ‖g p‖ₑ ^ (11 / 4 : ℝ) with hG
  have hGm : Measurable G := hgm.enorm.pow_const _
  have hL : eLpNorm (ringRead ε⁻¹ F) (11 / 4) (ringPhysμ ε⁻¹ c)
      = (ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))) ^ (1 / (11 / 4 : ℝ)) := by
    have hge' : ringRead ε⁻¹ F =ᵐ[ringPhysμ ε⁻¹ c] g := by
      unfold ringPhysμ
      exact Measure.ae_smul_measure hge _
    rw [eLpNorm_congr_ae hge', eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, hpR, ringPhysμ,
      lintegral_smul_measure]
    rfl
  have hae2 : ∀ᵐ τ ∂(volume : Measure ℝ), ∀ᵐ y ∂(volume : Measure Space),
      F τ y = g (NearInst.chartOf ε⁻¹ c y τ) :=
    Measure.ae_ae_of_ae_prod (p := fun z : ℝ × Space => F z.1 z.2 = g (NearInst.chartOf ε⁻¹ c z.2 z.1)) hae'
  have key : ∫⁻ τ in Ioc 0 (2 * c / ε⁻¹), ∫⁻ y, ENNReal.ofReal |F τ y| ^ (11 / 4 : ℝ)
      = ∫⁻ τ in Ioc 0 (2 * c / ε⁻¹), ∫⁻ y, G (NearInst.chartOf ε⁻¹ c y τ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hae2] with τ hτ
    refine lintegral_congr_ae ?_
    filter_upwards [hτ] with y hy
    simp only [G]
    rw [hy, ← Real.enorm_eq_ofReal_abs]
  have hR2 : phaseLr (2 * ε * c) (11 / 4) (fun x => F x.1 x.2)
      = (ENNReal.ofReal (2 * c / ε⁻¹)⁻¹ *
          ∫⁻ τ in Ioc 0 (2 * c / ε⁻¹), ∫⁻ y, G (NearInst.chartOf ε⁻¹ c y τ)) ^ (1 / (11 / 4 : ℝ)) := by
    unfold phaseLr
    rw [hP]
    dsimp only
    rw [key]
  have hchart := chartPhaseLIntegral ε⁻¹ c hR hc G hGm
  have hinv : ENNReal.ofReal (2 * c / ε⁻¹)⁻¹ * ENNReal.ofReal (2 * c / ε⁻¹) = 1 := by
    rw [ENNReal.ofReal_inv_of_pos hP0]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hP0).ne' ENNReal.ofReal_ne_top
  rw [hL, hR2, hchart]
  congr 1
  calc ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))
      = (ENNReal.ofReal (2 * c / ε⁻¹)⁻¹ * ENNReal.ofReal (2 * c / ε⁻¹)) *
          (ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * ∫⁻ p, G p ∂(ageμ c (-5 / 2))) := by
        rw [hinv, one_mul]
    _ = ENNReal.ofReal (2 * c / ε⁻¹)⁻¹ *
          (ENNReal.ofReal (2 * c / ε⁻¹) * ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) *
            ∫⁻ p, G p ∂(ageμ c (-5 / 2))) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
