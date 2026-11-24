import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.BsSliceMeasConv
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.BsSlicePtwise
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.RieszL6
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# `BSHLSSlice`: the slice Biot-Savart potential is in `L⁶`

Source `the November 2 reference manuscript` (stream potential of the solenoidal
cutoff, `L² * |w|⁻² → L⁶`). Pointwise `‖bsSlice F y‖ ≤ 2 T(‖F‖)(y)` (`bsSlicePtwise`), the
scalar HLS bound `∫ (T G)⁶ ≤ 64000 (∫G²)³` (`rieszL6`) applied to a measurable representative
`F'` of `F` (`T` only sees `G` up to a.e. equality), and measurability (`bsSliceMeasConv`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Power identity `x ^ (6:ℝ) = x ^ (6:ℕ)` in `ℝ≥0∞`. -/
lemma enorm_rpow_six (x : ℝ≥0∞) : x ^ (6 : ℝ) = x ^ (6 : ℕ) := by
  rw [← ENNReal.rpow_natCast]
  norm_num

theorem bsHLSSlice : BSHLSSlice := by
  intro F hF
  unfold MemLp
  obtain ⟨hmeas, -⟩ := bsSliceMeasConv F hF
  refine ⟨hmeas, ?_⟩
  -- a measurable representative `F'` of `F`
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
  -- the Riesz potential of `‖F‖` and of `‖F'‖` agree (they differ on a null set)
  have hE : ∀ y : Space, rieszT (fun z => ENNReal.ofReal ‖F z‖) y
      = rieszT (fun z => ENNReal.ofReal ‖F' z‖) y := by
    intro y
    unfold rieszT
    apply lintegral_congr_ae
    filter_upwards [hFae] with z hz
    simp only [hz]
  -- pointwise sixth-power bound
  have hptw : ∀ y : Space, ‖bsSlice F y‖ₑ ^ 6 ≤ 64 * rieszT (fun z => ENNReal.ofReal ‖F' z‖) y ^ 6 := by
    intro y
    have h0 := bsSlicePtwise F y
    rw [hE y, ofReal_norm] at h0
    have h1 : ‖bsSlice F y‖ₑ ≤ 2 * rieszT (fun z => ENNReal.ofReal ‖F' z‖) y := h0
    calc ‖bsSlice F y‖ₑ ^ 6 ≤ (2 * rieszT (fun z => ENNReal.ofReal ‖F' z‖) y) ^ 6 :=
          pow_le_pow_left' h1 6
      _ = 64 * rieszT (fun z => ENNReal.ofReal ‖F' z‖) y ^ 6 := by
          rw [mul_pow]
          norm_num
  have hint : ∫⁻ y, ‖bsSlice F y‖ₑ ^ 6
      ≤ ∫⁻ y, 64 * rieszT (fun z => ENNReal.ofReal ‖F' z‖) y ^ 6 := lintegral_mono hptw
  have hint2 : ∫⁻ y, 64 * rieszT (fun z => ENNReal.ofReal ‖F' z‖) y ^ 6
      = 64 * ∫⁻ y, rieszT (fun z => ENNReal.ofReal ‖F' z‖) y ^ 6 :=
    lintegral_const_mul' _ _ (by simp)
  have hR := rieszL6 (fun z => ENNReal.ofReal ‖F' z‖) hG'meas
  have hfin : ∫⁻ y, ‖bsSlice F y‖ₑ ^ 6 < ⊤ := by
    refine lt_of_le_of_lt hint ?_
    rw [hint2]
    refine ENNReal.mul_lt_top (by simp) (lt_of_le_of_lt hR ?_)
    exact ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top hG'2)
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num),
    ENNReal.toReal_ofNat]
  simp only [enorm_rpow_six]
  exact hfin

end UnforcedLeray.Short.PartIIIb.Concrete
