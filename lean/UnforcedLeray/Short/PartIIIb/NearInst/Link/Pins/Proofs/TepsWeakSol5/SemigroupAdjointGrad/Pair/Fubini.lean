import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_4_4
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Leaf S1: fixed-phase Fubini (`AdjSpatialFubini`)

Source `the November 2 reference manuscript`
1339-1362, 3346-3352.  The statement carries the hypothesis that `f` is a.e. strongly measurable
(without it the claim is false: a non-measurable phase makes the left side `0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Gaussian Metric
open UnforcedLeray.PhaseSpace

theorem adjSpatialFubini : AdjSpatialFubini := by
  intro a t ha A f hA hR hfm hf
  set c : ℝ := Real.exp (t / 2) with hc
  set G : Space → ℝ := gaussKernel 3 a with hG
  have hGc : Continuous G := continuous_gaussKernel a
  have hGnn : ∀ x, 0 ≤ G x := fun x => gaussKernel_nonneg ha x
  have hGint : Integrable G := integrable_gaussKernel ha
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x, G x ≤ M := ⟨_, fun x => gaussKernel_le ha x⟩
  obtain ⟨R, hR⟩ := hR
  have hAsupp : HasCompactSupport A :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) (fun x hx => by
      apply hR; simpa [mem_closedBall, dist_zero_right] using hx)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ y, ‖A y‖ ≤ K := by
    obtain ⟨C, hC⟩ := hAsupp.exists_bound_of_continuous hA
    exact ⟨C, hC⟩
  -- the basic slice estimate
  set C0 : ℝ := (M * (∫ x, G x) + ∫ u, ‖f u‖ ^ 2) / 2 with hC0
  have key : ∀ z : Space, Integrable (fun u => G (z - u) • f u) ∧
      ∫ u, ‖G (z - u) • f u‖ ≤ C0 := by
    intro z
    have hGz : Integrable (fun u => G (z - u)) := hGint.comp_sub_left z
    have hmeas : AEStronglyMeasurable (fun u => G (z - u) • f u) volume :=
      (hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul hfm
    have hle : ∀ u, ‖G (z - u) • f u‖ ≤ (M * G (z - u) + ‖f u‖ ^ 2) / 2 := by
      intro u
      rw [norm_smul (G (z - u)) (f u), Real.norm_of_nonneg (hGnn _)]
      have h1 : G (z - u) ≤ M := hM _
      have h2 : 0 ≤ G (z - u) := hGnn _
      nlinarith [sq_nonneg (G (z - u) - ‖f u‖), mul_le_mul_of_nonneg_left h1 h2]
    have hb : Integrable (fun u => (M * G (z - u) + ‖f u‖ ^ 2) / 2) :=
      ((hGz.const_mul M).add hf).div_const 2
    have hI : Integrable (fun u => G (z - u) • f u) :=
      hb.mono' hmeas (Filter.Eventually.of_forall fun u => by
        exact hle u)
    refine ⟨hI, ?_⟩
    calc ∫ u, ‖G (z - u) • f u‖ ≤ ∫ u, (M * G (z - u) + ‖f u‖ ^ 2) / 2 :=
          integral_mono hI.norm hb hle
      _ = C0 := by
          rw [integral_div, integral_add (hGz.const_mul M) hf, integral_const_mul,
            integral_sub_left_eq_self (fun u => G u) volume z]
  -- measurability on the product
  set H : Space × Space → ℂ := fun p => dotL (A p.1) (G (c • p.1 - p.2) • f p.2) with hH
  have hHm : AEStronglyMeasurable H (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : Space × Space => A p.1) (volume.prod volume) :=
      (hA.comp continuous_fst).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : Space × Space => G (c • p.1 - p.2) • f p.2)
        (volume.prod volume) := by
      have : Continuous (fun p : Space × Space => G (c • p.1 - p.2)) :=
        hGc.comp ((continuous_const_smul c).comp continuous_fst |>.sub continuous_snd)
      exact this.aestronglyMeasurable.smul (hfm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    exact dotL.aestronglyMeasurable_comp₂ h1 h2
  have hHint : Integrable H (volume.prod volume) := by
    rw [integrable_prod_iff hHm]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · exact (dotL (A y)).integrable_comp (key (c • y)).1
    · have hmeas := hHm.norm.integral_prod_right'
      set B : ℝ := ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * K * C0 with hB
      have hind : Integrable (fun y : Space => (closedBall (0 : Space) R).indicator (fun _ => B) y) :=
        (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator
          measurableSet_closedBall
      refine hind.mono' hmeas (Filter.Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ closedBall (0 : Space) R
      · rw [indicator_of_mem hy, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        calc ∫ u, ‖H (y, u)‖
            ≤ ∫ u, ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖A y‖ * ‖G (c • y - u) • f u‖ := by
              refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
                (((key (c • y)).1.norm).const_mul _) (Filter.Eventually.of_forall fun u => ?_)
              have := dotL.le_opNorm₂ (A y) (G (c • y - u) • f u)
              simpa [hH, mul_assoc] using this
          _ = ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖A y‖ * ∫ u, ‖G (c • y - u) • f u‖ :=
              integral_const_mul _ _
          _ ≤ B := by
              have h0 : 0 ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖A y‖ := by positivity
              calc _ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖A y‖ * C0 :=
                    mul_le_mul_of_nonneg_left (key (c • y)).2 h0
                _ ≤ B := by
                    rw [hB]
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left (hK y) (norm_nonneg (dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)))
                      (le_trans (integral_nonneg fun _ => norm_nonneg _) (key (c • y)).2)
      · have hAy : A y = 0 := hR y (by simpa [mem_closedBall, dist_zero_right] using hy)
        rw [indicator_of_notMem hy]
        simp [hH, hAy]
  -- assemble
  have e1 : ∀ y : Space, ∫ w : Euc 3, gaussKernel 3 a w • f (c • y - w)
      = ∫ u, G (c • y - u) • f u := by
    intro y
    have := integral_sub_left_eq_self (fun u => G (c • y - u) • f u) volume (c • y)
    simp only [sub_sub_cancel] at this
    exact this
  have e2 : ∀ y : Space, dotL (A y) (c • ∫ w : Euc 3, gaussKernel 3 a w • f (c • y - w))
      = (c : ℂ) * ∫ u, H (y, u) := by
    intro y
    rw [e1 y, ContinuousLinearMap.map_smul_of_tower, Complex.real_smul]
    congr 1
    exact (ContinuousLinearMap.integral_comp_comm (dotL (A y)) (key (c • y)).1).symm
  have e3 : ∀ u : Space, ∫ y, H (y, u) = dotL (∫ y, G (c • y - u) • A y) (f u) := by
    intro u
    have hg : Integrable (fun y : Space => G (c • y - u) • A y) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact (hGc.comp (((continuous_const_smul c)).sub continuous_const)).smul hA
      · refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) (fun x hx => ?_)
        have : A x = 0 := hR x (by simpa [mem_closedBall, dist_zero_right] using hx)
        simp [this]
    obtain ⟨L, hLx⟩ : ∃ L : CVec3 →L[ℂ] ℂ, ∀ x, L x = dotL x (f u) :=
      ⟨ContinuousLinearMap.flip dotL (f u), fun x => rfl⟩
    have := ContinuousLinearMap.integral_comp_comm L hg
    simp only [hLx] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hH, ContinuousLinearMap.map_smul_of_tower, smul_apply]
  refine (integral_congr_ae (Filter.Eventually.of_forall e2)).trans ?_
  rw [integral_const_mul, integral_integral_swap hHint]
  exact congrArg _ (integral_congr_ae (Filter.Eventually.of_forall e3))

end UnforcedLeray.Short.PartIIIb.NearInst
