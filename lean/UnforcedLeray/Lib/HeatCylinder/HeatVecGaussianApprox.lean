import UnforcedLeray.Lib.HeatCylinder.HeatVecZeroAge
import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianScaling
import UnforcedLeray.Lib.HeatCylinder.HeatVecApproxIdentity

/-!
# Gaussian average of the actual cylinder translation modulus

The two-dimensional Gaussian rescales to a fixed unit kernel. Dominated convergence against that
unit Gaussian and strong continuity of centered periodic translations make its translation
average vanish at age zero.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

private theorem measurable_heatVecTranslationModulus {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : Measurable (heatVecTranslationModulus hc x) := by
  let f := normalizedVecHeatRep hc x
  have hf : Measurable f := normalizedVecHeatRep_measurable hc x
  have hjoint : Measurable (Function.uncurry fun z w : Plane => f (z - w) - f z) := by
    exact (hf.comp (measurable_fst.sub measurable_snd)).sub (hf.comp measurable_fst)
  have hmod : Measurable (fun w : Plane =>
      eLpNorm (fun z : Plane => f (z - w) - f z) 2 (cellMeasure c)) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num)]
    refine Measurable.pow_const ?_ _
    exact Measurable.lintegral_prod_left'
      (hjoint.enorm.pow_const (2 : ℝ))
  have hreal : (fun w : Plane =>
      (eLpNorm (fun z : Plane => f (z - w) - f z) 2 (cellMeasure c)).toReal) =
      heatVecTranslationModulus hc x := by
    funext w
    exact eLpNorm_toReal_heatVecTranslationIncrement hc x w
  have hrealmeas := hmod.ennreal_toReal
  rw [hreal] at hrealmeas
  exact hrealmeas

private theorem heatVecTranslationModulus_le {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) :
    heatVecTranslationModulus hc x w ≤
      2 * Real.sqrt c⁻¹ * ‖heatVecCenteredInput hc x‖ := by
  let y := heatVecCenteredInput hc x
  have hη : ‖UnforcedLeray.TrainB.etaShiftL2 c (-w.2) y‖ = ‖y‖ :=
    (UnforcedLeray.TrainB.etaShiftL2 c (-w.2)).norm_map y
  have hq : ‖UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
      (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) y)‖ =
      ‖UnforcedLeray.TrainB.etaShiftL2 c (-w.2) y‖ :=
    (UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)).norm_map _
  have hshift : ‖planeShiftL2 hc w y‖ = ‖y‖ := by
    change ‖UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
      (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) y)‖ = ‖y‖
    exact hq.trans hη
  rw [heatVecTranslationModulus]
  calc
    Real.sqrt c⁻¹ * ‖planeShiftL2 hc w y - y‖ ≤
        Real.sqrt c⁻¹ * (‖planeShiftL2 hc w y‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt c⁻¹ * ‖y‖ := by rw [hshift]; ring

/-- The Gaussian average of the actual normalized-cell vector translation modulus converges to
zero as the spatial scale tends to zero. -/
theorem tendsto_heatVecGaussianTranslationAverage_zero {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    Tendsto (fun θ : ℝ => ∫⁻ w : Plane,
      ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
        eLpNorm (fun z : Plane => normalizedVecHeatRep hc x
          (z - Real.sqrt θ • w) - normalizedVecHeatRep hc x z) 2 (cellMeasure c))
      (𝓝 0) (𝓝 0) := by
  let f := normalizedVecHeatRep hc x
  let Ψ : ℝ → ℝ≥0∞ := fun θ =>
    ∫⁻ w : Plane, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
      eLpNorm (fun z : Plane => f (z - Real.sqrt θ • w) - f z) 2 (cellMeasure c)
  have hΨ : Tendsto Ψ (𝓝 0) (𝓝 0) := by
    have hlim := tendsto_lintegral_filter_of_dominated_convergence
      (μ := (volume : Measure Plane)) (l := 𝓝 (0 : ℝ))
      (F := fun θ w => ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
        eLpNorm (fun z : Plane => f (z - Real.sqrt θ • w) - f z) 2 (cellMeasure c))
      (f := fun _ => 0)
      (fun w => ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
        ENNReal.ofReal (2 * Real.sqrt c⁻¹ * ‖heatVecCenteredInput hc x‖))
      ?_ ?_ ?_ ?_
    · simpa [Ψ] using hlim
    · refine Eventually.of_forall (fun θ => ?_)
      have hmod := measurable_heatVecTranslationModulus hc x
      have hinc : (fun w : Plane =>
          eLpNorm (fun z : Plane => f (z - Real.sqrt θ • w) - f z) 2
            (cellMeasure c)) = fun w =>
          ENNReal.ofReal (heatVecTranslationModulus hc x (Real.sqrt θ • w)) := by
        funext w
        exact eLpNorm_heatVecTranslationIncrement_eq_ofReal hc x (Real.sqrt θ • w)
      have hk := ENNReal.measurable_ofReal.comp
        (UnforcedLeray.B0284.measurable_heatKernel2_right 1)
      have hm := ENNReal.measurable_ofReal.comp
        (hmod.comp (measurable_const_smul (Real.sqrt θ)))
      have hEq : (fun w : Plane =>
          ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
            eLpNorm (fun z : Plane => f (z - Real.sqrt θ • w) - f z) 2
              (cellMeasure c)) = fun w =>
          ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w) *
            ENNReal.ofReal (heatVecTranslationModulus hc x (Real.sqrt θ • w)) := by
        funext w
        rw [eLpNorm_heatVecTranslationIncrement_eq_ofReal hc x (Real.sqrt θ • w)]
      rw [hEq]
      exact hk.mul hm
    · refine Eventually.of_forall (fun θ => Eventually.of_forall (fun w => ?_))
      rw [eLpNorm_heatVecTranslationIncrement_eq_ofReal hc x (Real.sqrt θ • w)]
      apply mul_le_mul_of_nonneg_left
      · exact ENNReal.ofReal_le_ofReal (heatVecTranslationModulus_le hc x _)
      · exact zero_le
    · rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        UnforcedLeray.B0284.lintegral_heatKernel2 one_pos, one_mul]
      exact ENNReal.ofReal_ne_top
    · filter_upwards [] with w
      have hw : Tendsto (fun θ : ℝ => Real.sqrt θ • w) (𝓝 0) (𝓝 0) := by
        have hsqrt : Tendsto (fun θ : ℝ => Real.sqrt θ) (𝓝 0) (𝓝 0) := by
          have h := Real.continuous_sqrt.tendsto (0 : ℝ)
          simpa using h
        simpa using hsqrt.smul_const w
      have hmodLim := (tendsto_heatVecTranslationModulus_zero hc x).comp hw
      have hincLim : Tendsto (fun θ : ℝ =>
          eLpNorm (fun z : Plane => f (z - Real.sqrt θ • w) - f z) 2
            (cellMeasure c)) (𝓝 0) (𝓝 0) := by
        rw [show (fun θ : ℝ =>
            eLpNorm (fun z : Plane => f (z - Real.sqrt θ • w) - f z) 2
              (cellMeasure c)) = fun θ =>
            ENNReal.ofReal (heatVecTranslationModulus hc x (Real.sqrt θ • w)) by
              funext θ
              exact eLpNorm_heatVecTranslationIncrement_eq_ofReal hc x (Real.sqrt θ • w)]
        have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp hmodLim
        have hfun : (fun θ : ℝ => ENNReal.ofReal
            (heatVecTranslationModulus hc x (Real.sqrt θ • w))) =
            ENNReal.ofReal ∘ (fun z : Plane => heatVecTranslationModulus hc x z) ∘
              (fun θ : ℝ => Real.sqrt θ • w) := rfl
        rw [hfun]
        simpa only [ENNReal.ofReal_zero] using hcomp
      simpa [mul_zero] using
        ENNReal.Tendsto.const_mul hincLim (Or.inr ENNReal.ofReal_ne_top)
          (a := ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 1 w))
  simpa [Ψ, f] using hΨ

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.tendsto_heatVecGaussianTranslationAverage_zero
