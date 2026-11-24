import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_B

/-!
# Lifts of body forces lie in `Y_2` (source 2683-2689, 1341-1344)

Proof of `SrcLiftYr`, following `fwuLiftYr` (`PhysLayer/Sub/PartIIIb-D2_1_B.lean`) with
`b : VelG c γ ν` replaced by `f : SrcG c`.  The finiteness is read off from the `L²` norm of `f`
in `srcMeasure c = ofReal π • ageμ c (-3/2)`, so no density lower bound is needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem srcLiftYr : SrcLiftYr := by
  intro c ε hc hε f
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hR0 : ε⁻¹ ≠ 0 := hR.ne'
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hP0 : 0 < 2 * ε * c := by positivity
  have hc0 : c ≠ 0 := hc.ne'
  have hfm : Measurable (f : Chart → Merid) := (Lp.stronglyMeasurable f).measurable
  have hpm : Measurable (perExt c (f : Chart → Merid)) := measurable_perExt c hfm
  have hm : Measurable (velPhys ε⁻¹ c (f : Chart → Merid)) :=
    realC_continuous_B.measurable.comp (measurable_Nv ε⁻¹ hpm)
  refine ⟨?_, hm.aestronglyMeasurable, ?_⟩
  · -- periodicity in the phase
    refine Filter.Eventually.of_forall fun x => ?_
    have hper := congrFun (Nv_dss (R := ε⁻¹) (c := c) (P := 2 * c / ε⁻¹) hR0 rfl
      (perExt_periodic hc0 (f : Chart → Merid)) x.1) x.2
    show B0412.realC (Nv ε⁻¹ (perExt c (f : Chart → Merid)) (x.1 + 2 * ε * c) x.2) =
      B0412.realC (Nv ε⁻¹ (perExt c (f : Chart → Merid)) x.1 x.2)
    rw [hP, hper]
  · -- finiteness of the phase-normalized `L²` norm
    unfold UnforcedLeray.Short.IIb.phaseLpNorm
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    have hF : Measurable (fun x : ℝ × Space => ‖velPhys ε⁻¹ c (f : Chart → Merid) x‖ₑ ^ (2 : ℝ)) :=
      (hm.enorm).pow_const _
    have hI : ENNReal.ofReal (2 * ε * c)⁻¹ *
        ∫⁻ t in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y, ‖velPhys ε⁻¹ c (f : Chart → Merid) (t, y)‖ₑ ^ (2 : ℝ)
        = ∫⁻ x, ‖velPhys ε⁻¹ c (f : Chart → Merid) x‖ₑ ^ (2 : ℝ) ∂phaseμ (2 * ε * c) := by
      rw [ENNReal.ofReal_inv_of_pos hP0, lintegral_phaseμ _ hF]
    rw [hI]
    have hF' : (fun x : ℝ × Space => ‖velPhys ε⁻¹ c (f : Chart → Merid) x‖ₑ ^ (2 : ℝ)) =
        fun x => ‖Nv ε⁻¹ (perExt c (f : Chart → Merid)) x.1 x.2‖ₑ ^ (2 : ℝ) := by
      funext x
      simp only [velPhys]
      rw [enorm_realC_B]
    rw [hF', lintegral_phaseμ_Nv hR hc hP (by norm_num : (0 : ℝ) < 2) hpm
      (perExt_periodic hc0 (f : Chart → Merid))]
    rw [show ((2 : ℝ) / 2 - 5 / 2) = -3 / 2 by norm_num]
    have hae : ∫⁻ p, ‖perExt c (f : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) =
        ∫⁻ p, ‖(f : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂ageμ c (-3 / 2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [perExt_ae_eq hc (-3 / 2) (f : Chart → Merid)] with p hp
      rw [hp]
    rw [hae]
    -- the source measure has finite `L²` integral
    have hs : ∫⁻ p, ‖(f : Chart → Merid) p‖ₑ ^ (2 : ℝ) ∂srcMeasure c < ⊤ := by
      have h2 : eLpNorm (f : Chart → Merid) 2 (srcMeasure c) < ⊤ :=
        (Lp.memLp f).eLpNorm_lt_top
      have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) (by norm_num)
        (by norm_num) h2
      simpa using this
    have hs' : ∫⁻ p, ‖(f : Chart → Merid) p‖ₑ ^ (2 : ℝ)
        ∂(ENNReal.ofReal Real.pi • ageμ c (-3 / 2)) < ⊤ := hs
    rw [lintegral_smul_measure] at hs'
    have hfin := ENNReal.lt_top_of_mul_ne_top_right hs'.ne
      (ENNReal.ofReal_pos.2 Real.pi_pos).ne'
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne

end UnforcedLeray.Short.PartIIIb.Concrete
