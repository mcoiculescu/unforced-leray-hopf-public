import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.GradSlice

open MeasureTheory Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem hasCompactSupport_inner_snd {E : Type*} [NormedAddCommGroup E] {a : E → V} {b : E → V}
    (hb : HasCompactSupport b) : HasCompactSupport (fun y => inner ℝ (a y) (b y)) := by
  refine HasCompactSupport.intro hb.isCompact fun y hy => ?_
  have : b y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [this]

theorem hasCompactSupport_inner_fst {E : Type*} [NormedAddCommGroup E] {a : E → V} {b : E → V}
    (ha : HasCompactSupport a) : HasCompactSupport (fun y => inner ℝ (a y) (b y)) := by
  refine HasCompactSupport.intro ha.isCompact fun y hy => ?_
  have : a y = 0 := image_eq_zero_of_notMem_tsupport hy
  simp [this]

/-- Integration by parts against a compactly supported smooth field, real inner product. -/
theorem integral_inner_fderiv_eq_neg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasureSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] [SecondCountableTopology E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {F u : E → V} (hF : ContDiff ℝ 1 F) (hu : ContDiff ℝ ⊤ u)
    (hcs : HasCompactSupport u) (v : E) :
    ∫ y, inner ℝ (F y) (fderiv ℝ u y v) = - ∫ y, inner ℝ (fderiv ℝ F y v) (u y) := by
  have hFc : Continuous F := hF.continuous
  have hdF : Continuous (fun y => fderiv ℝ F y) := hF.continuous_fderiv one_ne_zero
  have hdu : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by simp)
  have huc : Continuous u := hu.continuous
  have i1 : Integrable (fun y => innerSL ℝ (fderiv ℝ F y v) (u y)) := by
    simp only [innerSL_apply_apply]
    refine Continuous.integrable_of_hasCompactSupport ?_ (hasCompactSupport_inner_snd hcs)
    exact (hdF.clm_apply continuous_const).inner huc
  have i2 : Integrable (fun y => innerSL ℝ (F y) (fderiv ℝ u y v)) := by
    simp only [innerSL_apply_apply]
    exact Continuous.integrable_of_hasCompactSupport (hFc.inner (hdu.clm_apply continuous_const))
      (hasCompactSupport_inner_snd (hcs.fderiv_apply (𝕜 := ℝ) v))
  have i3 : Integrable (fun y => innerSL ℝ (F y) (u y)) := by
    simp only [innerSL_apply_apply]
    exact Continuous.integrable_of_hasCompactSupport (hFc.inner huc) (hasCompactSupport_inner_snd hcs)
  have := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := innerSL ℝ) (f := F) (g := u) (v := v) i1 i2 i3
    (fun x _ => hF.differentiable one_ne_zero x)
    (fun x _ => hu.differentiable (by simp) x)
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete.GradSlice
