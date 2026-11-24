import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsKernelNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Convolution bound for the Biot-Savart kernel (BSTestConvBound)

Source `the November 2 reference manuscript` lines 1351-1362.

Helper `absConvPow`: for `0 < α < 3` and a continuous compactly supported `φ`, the convolution
`∫ |φ(y)| |y - z|^{-α} dy` is bounded by `C (1 + |z|)^{-α}`.  Split at `|z| = 2R` where
`supp φ ⊆ closedBall 0 R`: far away the integrand is dominated by a constant times
`1_{closedBall 0 R}`; near, by `M` times a translate of the integrable profile
`1_{ball 0 (3R)} |w|^{-α}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rpow_ball_integrable {α : ℝ} (hα0 : 0 < α) (hα3 : α < 3) (r : ℝ) :
    IntegrableOn (fun w : Space => ‖w‖ ^ (-α)) (ball (0 : Space) r) := by
  have hd : (Module.finrank ℝ Space : ℝ) = 3 := by
    rw [finrank_euclideanSpace_fin]; norm_num
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := α) (r := r)
    (by rw [finrank_euclideanSpace_fin]; norm_num) (by rw [hd]; exact hα3)
    (ae_of_all _ (fun x => ?_)) ((measurable_norm).pow_const _).aestronglyMeasurable
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]

theorem absConvPow {α : ℝ} (hα0 : 0 < α) (hα3 : α < 3) (φ : Space → ℂ)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Space,
      Integrable (fun y : Space => ‖φ y‖ * ‖y - z‖ ^ (-α)) volume ∧
      ∫ y : Space, ‖φ y‖ * ‖y - z‖ ^ (-α) ≤ C * (1 + ‖z‖) ^ (-α) := by
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Space)).1
    hφs.isCompact.isBounded
  obtain ⟨M0, hM0⟩ := hφc.bounded_above_of_compact_support hφs
  set R : ℝ := max R0 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRR0 : R0 ≤ R := le_max_left _ _
  have hsupp : ∀ y : Space, R < ‖y‖ → φ y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h := hR0 hmem
    rw [mem_closedBall, dist_zero_right] at h
    linarith
  set M : ℝ := max M0 0 with hMdef
  have hM : ∀ y : Space, ‖φ y‖ ≤ M := fun y => le_trans (hM0 y) (le_max_left _ _)
  have hM0' : 0 ≤ M := le_max_right _ _
  have hKint : Integrable (fun w : Space => (ball (0 : Space) (3 * R)).indicator
      (fun w : Space => ‖w‖ ^ (-α)) w) :=
    (integrable_indicator_iff measurableSet_ball).2 (rpow_ball_integrable hα0 hα3 _)
  set K : ℝ := ∫ w : Space, (ball (0 : Space) (3 * R)).indicator
      (fun w : Space => ‖w‖ ^ (-α)) w with hKdef
  have hK0 : 0 ≤ K := integral_nonneg (fun w => indicator_nonneg
    (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) w)
  set D : ℝ := (4 : ℝ) ^ (-α) with hD
  have hDpos : 0 < D := Real.rpow_pos_of_pos (by norm_num) _
  set V : ℝ := volume.real (closedBall (0 : Space) R) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  refine ⟨max (V * M / D) (M * K * (1 + 2 * R) ^ α), ?_, fun z => ?_⟩
  · exact le_trans (mul_nonneg (mul_nonneg hM0' hK0) (Real.rpow_nonneg (by linarith) _))
      (le_max_right _ _)
  have hw0 : 0 < (1 + ‖z‖) ^ (-α) := Real.rpow_pos_of_pos (by positivity) _
  have hf_nonneg : ∀ y : Space, 0 ≤ ‖φ y‖ * ‖y - z‖ ^ (-α) := fun y =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hf_meas : AEStronglyMeasurable (fun y : Space => ‖φ y‖ * ‖y - z‖ ^ (-α)) volume := by
    apply AEStronglyMeasurable.mul
    · exact hφc.norm.aestronglyMeasurable
    · exact ((measurable_id.sub_const z).norm.pow_const (-α)).aestronglyMeasurable
  by_cases hz : 2 * R ≤ ‖z‖
  · -- far case: dominate by a constant on `closedBall 0 R`
    have hGint : Integrable (fun y : Space => (closedBall (0 : Space) R).indicator
        (fun _ : Space => M * ((1 + ‖z‖) ^ (-α) / D)) y) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    have hGval : ∫ y : Space, (closedBall (0 : Space) R).indicator
        (fun _ : Space => M * ((1 + ‖z‖) ^ (-α) / D)) y = V * M / D * (1 + ‖z‖) ^ (-α) := by
      rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul]
      rw [hV]
      ring
    have hdom : ∀ y : Space, ‖φ y‖ * ‖y - z‖ ^ (-α) ≤ (closedBall (0 : Space) R).indicator
        (fun _ : Space => M * ((1 + ‖z‖) ^ (-α) / D)) y := by
      intro y
      by_cases hy : ‖y‖ ≤ R
      · have hyc : y ∈ closedBall (0 : Space) R := by
          rw [mem_closedBall, dist_zero_right]; exact hy
        rw [indicator_of_mem hyc]
        have hlow : (1 + ‖z‖) / 4 ≤ ‖y - z‖ := by
          have h1 : ‖z‖ - ‖y‖ ≤ ‖y - z‖ := by
            rw [norm_sub_rev]; exact norm_sub_norm_le z y
          linarith
        have hpos : 0 < (1 + ‖z‖) / 4 := by positivity
        have hrp : ‖y - z‖ ^ (-α) ≤ ((1 + ‖z‖) / 4) ^ (-α) :=
          Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
        have hdiv : ((1 + ‖z‖) / 4) ^ (-α) = (1 + ‖z‖) ^ (-α) / D := by
          rw [Real.div_rpow (by positivity) (by norm_num), hD]
        calc ‖φ y‖ * ‖y - z‖ ^ (-α) ≤ M * ‖y - z‖ ^ (-α) :=
              mul_le_mul_of_nonneg_right (hM y) (Real.rpow_nonneg (norm_nonneg _) _)
          _ ≤ M * ((1 + ‖z‖) / 4) ^ (-α) :=
              mul_le_mul_of_nonneg_left hrp hM0'
          _ = M * ((1 + ‖z‖) ^ (-α) / D) := by rw [hdiv]
      · have hy' : R < ‖y‖ := lt_of_not_ge hy
        have hyc : y ∉ closedBall (0 : Space) R := by
          rw [mem_closedBall, dist_zero_right]; exact not_le.2 hy'
        simp [indicator_of_notMem hyc, hsupp y hy']
    refine ⟨?_, ?_⟩
    · exact Integrable.mono' hGint hf_meas
        (ae_of_all _ fun y => by
          rw [Real.norm_of_nonneg (hf_nonneg y)]; exact hdom y)
    · calc ∫ y : Space, ‖φ y‖ * ‖y - z‖ ^ (-α)
          ≤ ∫ y : Space, (closedBall (0 : Space) R).indicator
              (fun _ : Space => M * ((1 + ‖z‖) ^ (-α) / D)) y :=
            integral_mono_of_nonneg (ae_of_all _ hf_nonneg) hGint (ae_of_all _ hdom)
        _ = V * M / D * (1 + ‖z‖) ^ (-α) := hGval
        _ ≤ max (V * M / D) (M * K * (1 + 2 * R) ^ α) * (1 + ‖z‖) ^ (-α) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hw0.le
  · -- near case: dominate by a translate of the integrable profile
    have hz' : ‖z‖ < 2 * R := lt_of_not_ge hz
    have hGint : Integrable (fun y : Space => M * (ball (0 : Space) (3 * R)).indicator
        (fun w : Space => ‖w‖ ^ (-α)) (y - z)) :=
      (hKint.comp_sub_right z).const_mul M
    have hGval : ∫ y : Space, M * (ball (0 : Space) (3 * R)).indicator
        (fun w : Space => ‖w‖ ^ (-α)) (y - z) = M * K := by
      rw [integral_const_mul, integral_sub_right_eq_self
        (fun w : Space => (ball (0 : Space) (3 * R)).indicator (fun w : Space => ‖w‖ ^ (-α)) w) z]
    have hdom : ∀ y : Space, ‖φ y‖ * ‖y - z‖ ^ (-α) ≤ M * (ball (0 : Space) (3 * R)).indicator
        (fun w : Space => ‖w‖ ^ (-α)) (y - z) := by
      intro y
      by_cases hy : ‖y‖ ≤ R
      · have hyb : y - z ∈ ball (0 : Space) (3 * R) := by
          rw [mem_ball_zero_iff]
          have := norm_sub_le y z
          linarith
        rw [indicator_of_mem hyb]
        exact mul_le_mul_of_nonneg_right (hM y) (Real.rpow_nonneg (norm_nonneg _) _)
      · have hy' : R < ‖y‖ := lt_of_not_ge hy
        rw [hsupp y hy', norm_zero, zero_mul]
        apply mul_nonneg hM0'
        exact indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) _
    have hnear : (1 + 2 * R) ^ α * (1 + 2 * R) ^ (-α) = 1 := by
      rw [← Real.rpow_add (by linarith)]; simp
    have hmono : (1 + 2 * R) ^ (-α) ≤ (1 + ‖z‖) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [norm_nonneg z]) (by linarith) (by linarith)
    have hMK : 0 ≤ M * K := mul_nonneg hM0' hK0
    refine ⟨?_, ?_⟩
    · exact Integrable.mono' hGint hf_meas
        (ae_of_all _ fun y => by
          rw [Real.norm_of_nonneg (hf_nonneg y)]; exact hdom y)
    · calc ∫ y : Space, ‖φ y‖ * ‖y - z‖ ^ (-α)
          ≤ ∫ y : Space, M * (ball (0 : Space) (3 * R)).indicator
              (fun w : Space => ‖w‖ ^ (-α)) (y - z) :=
            integral_mono_of_nonneg (ae_of_all _ hf_nonneg) hGint (ae_of_all _ hdom)
        _ = M * K := hGval
        _ = M * K * ((1 + 2 * R) ^ α * (1 + 2 * R) ^ (-α)) := by rw [hnear, mul_one]
        _ ≤ M * K * (1 + 2 * R) ^ α * (1 + ‖z‖) ^ (-α) := by
            have h2 : (0 : ℝ) ≤ (1 + 2 * R) ^ α := Real.rpow_nonneg (by linarith) _
            calc M * K * ((1 + 2 * R) ^ α * (1 + 2 * R) ^ (-α))
                = (M * K * (1 + 2 * R) ^ α) * (1 + 2 * R) ^ (-α) := by ring
              _ ≤ (M * K * (1 + 2 * R) ^ α) * (1 + ‖z‖) ^ (-α) :=
                  mul_le_mul_of_nonneg_left hmono (mul_nonneg hMK h2)
              _ = M * K * (1 + 2 * R) ^ α * (1 + ‖z‖) ^ (-α) := rfl
        _ ≤ max (V * M / D) (M * K * (1 + 2 * R) ^ α) * (1 + ‖z‖) ^ (-α) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hw0.le

theorem bsTestConvBound : BSTestConvBound := by
  intro φ hφc hφs
  obtain ⟨C0, hC0nn, hC0⟩ := absConvPow (α := 2) (by norm_num) (by norm_num) φ hφc hφs
  refine ⟨(4 * Real.pi)⁻¹ * C0, fun z => ?_⟩
  have hkern : ∀ y : Space, ‖φ y‖ * ‖bsKernel (y - z)‖
      = (4 * Real.pi)⁻¹ * (‖φ y‖ * ‖y - z‖ ^ (-(2 : ℝ))) := by
    intro y
    rw [bsKernelNorm (y - z), Real.rpow_neg (norm_nonneg _), Real.rpow_two]
    ring
  have hfun : (fun y : Space => ‖φ y‖ * ‖bsKernel (y - z)‖)
      = fun y => (4 * Real.pi)⁻¹ * (‖φ y‖ * ‖y - z‖ ^ (-(2 : ℝ))) := funext hkern
  obtain ⟨hint, hle⟩ := hC0 z
  have hw : (1 + ‖z‖) ^ (-(2 : ℝ)) ≤ (1 + ‖z‖ ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    exact inv_anti₀ (by positivity) (by nlinarith [norm_nonneg z])
  have hpi : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hint.const_mul _
  · rw [hfun, integral_const_mul]
    calc (4 * Real.pi)⁻¹ * ∫ y : Space, ‖φ y‖ * ‖y - z‖ ^ (-(2 : ℝ))
        ≤ (4 * Real.pi)⁻¹ * (C0 * (1 + ‖z‖) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hle hpi
      _ ≤ (4 * Real.pi)⁻¹ * (C0 * (1 + ‖z‖ ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hC0nn) hpi
      _ = (4 * Real.pi)⁻¹ * C0 * (1 + ‖z‖ ^ 2)⁻¹ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
