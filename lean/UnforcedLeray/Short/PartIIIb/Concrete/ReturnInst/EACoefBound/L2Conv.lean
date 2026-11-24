import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# `PartIII-b:C/inst/10/6`: `ChartL2Conv` (EACoefBound copy of FACoefBound/ChartConv.lean)

Source `the November 2 reference manuscript`
5063-5079 (cell bound `D² s^5` on `0 < s ≤ T`, zero beyond, into the `L²(π s^{-3/2} dς)` norm):
Tonelli on `ageμ c (-3/2)` and `π ∫_0^T s^{-3/2} D² s^5 ds = π D² (2/9) T^{9/2} ≤ D² T^6`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem chartConv_radial (T D : ℝ) (hT : 0 < T) :
    ∫⁻ s in Ioc (0 : ℝ) T, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal (D ^ 2 * s ^ 5)
      = ENNReal.ofReal (D ^ 2 * (2 / 9) * T ^ (9 / 2 : ℝ)) := by
  have h1 : ∀ s ∈ Ioc (0 : ℝ) T, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal (D ^ 2 * s ^ 5)
      = ENNReal.ofReal (D ^ 2 * s ^ (7 / 2 : ℝ)) := by
    intro s hs
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _)]
    congr 1
    have : s ^ (7 / 2 : ℝ) = s ^ (-3 / 2 : ℝ) * s ^ 5 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hs.1]; norm_num
    rw [this]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioc h1]
  have hint : IntervalIntegrable (fun s : ℝ => D ^ 2 * s ^ (7 / 2 : ℝ)) volume 0 T :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num))]
    rw [Real.zero_rpow (by norm_num)]
    norm_num; ring
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hint
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact mul_nonneg (sq_nonneg D) (Real.rpow_nonneg hs.1.le _)

theorem chartL2Conv : ChartL2Conv := by
  intro c T D F hc hT hD hFa hz hfib
  have hT0 : 0 < T := by linarith
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hk : ENNReal.ofReal Real.pi ≠ 0 := by
    simpa using Real.pi_pos
  have hac : ageμ c (-3 / 2) ≪ srcMeasure c := by
    unfold srcMeasure
    exact Measure.absolutelyContinuous_smul hk
  have hFa' : AEStronglyMeasurable F (ageμ c (-3 / 2)) := hFa.mono_ac hac
  have hae : AEMeasurable (fun p => ENNReal.ofReal (‖F p‖ ^ 2)) (ageμ c (-3 / 2)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hFa'.norm.aemeasurable).pow_const 2)
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  -- the bound on the lintegral
  have hI : ∫⁻ p, ENNReal.ofReal (‖F p‖ ^ 2) ∂(srcMeasure c)
      ≤ ENNReal.ofReal (D ^ 2 * T ^ 6) := by
    unfold srcMeasure
    rw [lintegral_smul_measure, ageμ]
    rw [lintegral_prod _ (by simpa [ageμ] using hae)]
    set w : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) with hw
    have hwm : Measurable w := measurable_ofReal_rpow _
    have hinner : ∀ s : ℝ, ∫⁻ y, ENNReal.ofReal (‖F (s, y)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ c)
        ≤ (Ioc (0 : ℝ) T).indicator (fun s => ENNReal.ofReal (D ^ 2 * s ^ 5)) s ∨ s ≤ 0 := by
      intro s
      by_cases hs : 0 < s
      · left
        by_cases hsT : s ≤ T
        · rw [indicator_of_mem (show s ∈ Ioc (0 : ℝ) T from ⟨hs, hsT⟩)]; exact hfib s hs hsT
        · have hsT' := not_le.1 hsT
          rw [indicator_of_notMem (by simp [hsT])]
          have : ∀ y, ENNReal.ofReal (‖F (s, y)‖ ^ 2) = 0 := by
            intro y; rw [hz s hsT' y]; simp
          simp [this]
      · right; linarith
    have hae0 : ∀ᵐ s ∂((volume.restrict (Ioi (0 : ℝ))).withDensity w), 0 < s := by
      apply (withDensity_absolutelyContinuous _ _).ae_le
      have := ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
      filter_upwards [this] with s hs using hs
    have hstep : ∫⁻ s, ∫⁻ y, ENNReal.ofReal (‖F (s, y)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ c)
        ∂((volume.restrict (Ioi (0 : ℝ))).withDensity w)
        ≤ ∫⁻ s, (Ioc (0 : ℝ) T).indicator (fun s => ENNReal.ofReal (D ^ 2 * s ^ 5)) s
        ∂((volume.restrict (Ioi (0 : ℝ))).withDensity w) := by
      apply lintegral_mono_ae
      filter_upwards [hae0] with s hs
      rcases hinner s with h | h
      · exact h
      · exact absurd hs (not_lt.2 h)
    have hgm : Measurable ((Ioc (0 : ℝ) T).indicator fun s : ℝ => ENNReal.ofReal (D ^ 2 * s ^ 5)) :=
      (ENNReal.measurable_ofReal.comp (by fun_prop)).indicator measurableSet_Ioc
    rw [lintegral_withDensity_eq_lintegral_mul _ hwm hgm] at hstep
    have hrad : ∫⁻ s in Ioi (0 : ℝ), (w * (Ioc (0 : ℝ) T).indicator
        (fun s => ENNReal.ofReal (D ^ 2 * s ^ 5))) s
        = ENNReal.ofReal (D ^ 2 * (2 / 9) * T ^ (9 / 2 : ℝ)) := by
      have : ∀ s : ℝ, (w * (Ioc (0 : ℝ) T).indicator
          (fun s => ENNReal.ofReal (D ^ 2 * s ^ 5))) s
          = (Ioc (0 : ℝ) T).indicator (fun s => w s * ENNReal.ofReal (D ^ 2 * s ^ 5)) s := by
        intro s
        by_cases hs : s ∈ Ioc (0 : ℝ) T <;> simp [hs]
      simp_rw [this]
      rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
        Ioc_inter_Ioi, max_eq_left le_rfl]
      exact chartConv_radial T D hT0
    rw [hrad] at hstep
    calc ENNReal.ofReal Real.pi * _ ≤ ENNReal.ofReal Real.pi *
          ENNReal.ofReal (D ^ 2 * (2 / 9) * T ^ (9 / 2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal (Real.pi * (D ^ 2 * (2 / 9) * T ^ (9 / 2 : ℝ))) :=
          (ENNReal.ofReal_mul Real.pi_pos.le).symm
      _ ≤ ENNReal.ofReal (D ^ 2 * T ^ 6) := by
          apply ENNReal.ofReal_le_ofReal
          have h92 : T ^ (9 / 2 : ℝ) ≤ T ^ (6 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
          have h6 : T ^ (6 : ℝ) = T ^ 6 := by
            rw [← Real.rpow_natCast]; norm_num
          rw [h6] at h92
          have hp := Real.pi_lt_d2
          have hD2 : 0 ≤ D ^ 2 := by positivity
          have hT92 : 0 ≤ T ^ (9 / 2 : ℝ) := by positivity
          nlinarith [mul_nonneg hD2 hT92, mul_nonneg hD2 (sub_nonneg.2 h92)]
  -- from the lintegral bound to the L² norm
  have hnorm : eLpNorm F 2 (srcMeasure c) ≤ ENNReal.ofReal (D * T ^ 3) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have h2 : ∫⁻ p, ‖F p‖ₑ ^ (ENNReal.toReal 2) ∂(srcMeasure c)
        = ∫⁻ p, ENNReal.ofReal (‖F p‖ ^ 2) ∂(srcMeasure c) := by
      refine lintegral_congr fun p => ?_
      rw [ENNReal.toReal_ofNat, ← ofReal_norm, ENNReal.rpow_ofNat,
        ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [h2]
    have hsq : ENNReal.ofReal (D ^ 2 * T ^ 6) = ENNReal.ofReal (D * T ^ 3) ^ (2 : ℝ) := by
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
      congr 1
      ring
    calc _ ≤ (ENNReal.ofReal (D * T ^ 3) ^ (2 : ℝ)) ^ (1 / ENNReal.toReal 2) := by
          gcongr
          exact hI.trans hsq.le
      _ = _ := by
          rw [← ENNReal.rpow_mul, ENNReal.toReal_ofNat]; norm_num
  exact ⟨⟨hFa, lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top⟩, hnorm⟩

end UnforcedLeray.Short.PartIIIb.Concrete
