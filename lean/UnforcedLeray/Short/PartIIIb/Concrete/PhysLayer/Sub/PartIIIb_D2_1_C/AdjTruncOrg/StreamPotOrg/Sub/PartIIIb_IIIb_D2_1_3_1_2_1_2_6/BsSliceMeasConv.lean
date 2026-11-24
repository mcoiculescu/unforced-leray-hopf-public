import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.BsSliceMeasConv.NearFinite
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.BSDefined
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.BsK2Norm
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncHardyTendsto
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# `BsSliceMeasConv`: measurability and a.e. absolute convergence of the slice Biot-Savart integral

Source `the November 2 reference manuscript` (stream potential, `L² * |w|⁻² → L⁶`).
(a) Fubini (`AEStronglyMeasurable.integral_prod_right'`) as in `bsDefined`.
(b) For a.e. `y` the integrand `z ↦ crossC (F z) (bsKernel (y - z))` is integrable, since its norm
is bounded by `2 · ‖F z‖ · k(y - z)` and the Riesz potential of `‖F‖` is a.e. finite
(`bsmc_rieszT_ae`, helper file `BsSliceMeasConv/NearFinite.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

set_option maxHeartbeats 1000000 in
theorem bsSliceMeasConv : BsSliceMeasConv := by
  intro F hF
  -- a measurable representative of `F`
  obtain ⟨F', hF'meas, hFae⟩ : ∃ F' : Space → CVec3, Measurable F' ∧ F =ᵐ[volume] F' :=
    ⟨hF.aestronglyMeasurable.mk, hF.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
      hF.aestronglyMeasurable.ae_eq_mk⟩
  -- square integrability of `‖F‖`
  have hsq : ∫⁻ z, ENNReal.ofReal ‖F z‖ ^ 2 < ⊤ := by
    have hI := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
    have h2 := (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z => sq_nonneg ‖F z‖))).mp hI.2
    have hpow : ∀ z : Space, ENNReal.ofReal ‖F z‖ ^ 2 = ENNReal.ofReal (‖F z‖ ^ 2) :=
      fun z => (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
    simp only [hpow]
    exact h2
  have hG'meas : Measurable (fun z => ENNReal.ofReal ‖F' z‖) :=
    (hF'meas.norm).ennreal_ofReal
  have hG'2 : ∫⁻ z, ENNReal.ofReal ‖F' z‖ ^ 2 < ⊤ := by
    have heq : (fun z => ENNReal.ofReal ‖F' z‖ ^ 2) =ᵐ[volume] (fun z => ENNReal.ofReal ‖F z‖ ^ 2) := by
      filter_upwards [hFae] with z hz
      simp only [hz]
    rw [lintegral_congr_ae heq]
    exact hsq
  have hG'_ae : (fun z => ENNReal.ofReal ‖F z‖) =ᵐ[volume] (fun z => ENNReal.ofReal ‖F' z‖) := by
    filter_upwards [hFae] with z hz
    simp only [hz]
  -- (a) measurability of the slice potential
  have hA : AEStronglyMeasurable (fun p : Space × Space => F p.2)
      (volume : Measure (Space × Space)) :=
    hF.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hK : AEStronglyMeasurable (fun p : Space × Space => bsKernel (p.1 - p.2))
      (volume : Measure (Space × Space)) :=
    (measurable_bsKernel.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  have hFK : AEStronglyMeasurable (fun p : Space × Space => crossC (F p.2) (bsKernel (p.1 - p.2)))
      (volume : Measure (Space × Space)) :=
    continuous_crossC'.comp_aestronglyMeasurable (hA.prodMk hK)
  have hpart_a : AEStronglyMeasurable (bsSlice F) volume :=
    AEStronglyMeasurable.integral_prod_right'
      (f := fun p : Space × Space => crossC (F p.2) (bsKernel (p.1 - p.2))) hFK
  -- (b) a.e. integrability of the slice integrand
  have hpart_b : ∀ᵐ y : Space, Integrable (fun z : Space => crossC (F z) (bsKernel (y - z))) volume := by
    filter_upwards [bsmc_rieszT_ae (fun z => ENNReal.ofReal ‖F' z‖) hG'meas hG'2] with y hy
    have hsub : Measurable (fun z : Space => y - z) := measurable_const.sub measurable_id
    have hKm : AEStronglyMeasurable (fun z : Space => bsKernel (y - z)) volume :=
      (measurable_bsKernel.comp hsub).aestronglyMeasurable
    have hpair : AEStronglyMeasurable (fun z : Space => (F z, bsKernel (y - z))) volume :=
      hF.aestronglyMeasurable.prodMk hKm
    have hAESM : AEStronglyMeasurable (fun z : Space => crossC (F z) (bsKernel (y - z))) volume :=
      Continuous.comp_aestronglyMeasurable (g := fun p : CVec3 × CVec3 => crossC p.1 p.2)
        (f := fun z : Space => (F z, bsKernel (y - z))) continuous_crossC' hpair
    refine ⟨hAESM, ?_⟩
    have hpt : ∀ z : Space, ‖crossC (F z) (bsKernel (y - z))‖ₑ
        ≤ 2 * (ENNReal.ofReal ‖F z‖ * bsK2 (y - z)) := by
      intro z
      rw [← ofReal_norm]
      calc ENNReal.ofReal ‖crossC (F z) (bsKernel (y - z))‖
          ≤ ENNReal.ofReal (2 * (‖F z‖ * ‖bsKernel (y - z)‖)) :=
            ENNReal.ofReal_le_ofReal (trh_cross_norm _ _)
        _ = 2 * (ENNReal.ofReal ‖F z‖ * ENNReal.ofReal ‖bsKernel (y - z)‖) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (norm_nonneg _),
              ENNReal.ofReal_ofNat]
        _ = 2 * (ENNReal.ofReal ‖F z‖ * bsK2 (y - z)) := by rw [bsK2Norm (y - z)]
    have hint_eq : ∫⁻ z, ENNReal.ofReal ‖F z‖ * bsK2 (y - z)
        = ∫⁻ z, ENNReal.ofReal ‖F' z‖ * bsK2 (y - z) :=
      lintegral_congr_ae (by filter_upwards [hG'_ae] with z hz; simp only [hz])
    have hlt : ∫⁻ z, ‖crossC (F z) (bsKernel (y - z))‖ₑ < ⊤ := by
      calc ∫⁻ z, ‖crossC (F z) (bsKernel (y - z))‖ₑ
          ≤ ∫⁻ z, 2 * (ENNReal.ofReal ‖F z‖ * bsK2 (y - z)) := lintegral_mono hpt
        _ = 2 * ∫⁻ z, ENNReal.ofReal ‖F z‖ * bsK2 (y - z) :=
            lintegral_const_mul' _ _ (by simp)
        _ = 2 * ∫⁻ z, ENNReal.ofReal ‖F' z‖ * bsK2 (y - z) := by rw [hint_eq]
        _ < ⊤ := ENNReal.mul_lt_top (by simp) hy
    exact hlt
  exact ⟨hpart_a, hpart_b⟩

end UnforcedLeray.Short.PartIIIb.Concrete
