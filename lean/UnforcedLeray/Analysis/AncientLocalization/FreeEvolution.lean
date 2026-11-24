import UnforcedLeray.Analysis.SpatialScaling
import UnforcedLeray.Analysis.Heat.Flow
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Actual free similarity evolution on R³

This is the manuscript's free evolution S₀(s) on spatial L² fields:
`e^(s/2) H_{h(e^s-1)} f(e^(s/2)y)`. The heat flow is the proved literal
Gaussian convolution at positive times, not an abstract semigroup premise.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace UnforcedLeray.AncientLocalization

/-- The spatial similarity dilation in logarithmic time. -/
def similarityDilation (s : ℝ) : ℝ := Real.exp (s / 2)

/-- The exact free similarity flow in physical coordinates. -/
def freeEvolution (h s : ℝ) (f : SpatialField) : SpatialField :=
  SpatialScaling.spatialScale (similarityDilation s) (similarityDilation s)
    (Heat.flow f (h * (Real.exp s - 1)))

@[simp] theorem similarityDilation_zero : similarityDilation 0 = 1 := by
  simp [similarityDilation]

@[simp] theorem freeEvolution_zero (h : ℝ) (f : SpatialField) :
    freeEvolution h 0 f = f := by
  ext x
  simp [freeEvolution, similarityDilation, SpatialScaling.spatialScale]

/-- A genuine L² field stays in L² under the literal free evolution. -/
theorem freeEvolution_memLp {f : SpatialField} (hf : MemLp f 2 volume)
    (h s : ℝ) : MemLp (freeEvolution h s f) 2 volume := by
  unfold freeEvolution
  exact SpatialScaling.memLp_spatialScale (Heat.flow_memLp hf _)
    _ (Real.exp_pos _).ne'

/-- The exact three-dimensional similarity factor is `e^(-s/4)`. -/
theorem freeEvolution_l2Norm_eq {f : SpatialField} (hf : MemLp f 2 volume)
    (h s : ℝ) :
    l2Norm (freeEvolution h s f) =
      Real.exp (-s / 4) * l2Norm (Heat.flow f (h * (Real.exp s - 1))) := by
  have hd : 0 < similarityDilation s := Real.exp_pos _
  unfold freeEvolution
  rw [SpatialScaling.l2Norm_spatialScale _ (Heat.flow_memLp hf _) _ hd,
    abs_of_pos hd]
  unfold similarityDilation
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The actual heat contraction yields the free similarity decay. -/
theorem freeEvolution_l2Norm_le {f : SpatialField} (hf : MemLp f 2 volume)
    (h s : ℝ) :
    l2Norm (freeEvolution h s f) ≤ Real.exp (-s / 4) * l2Norm f := by
  rw [freeEvolution_l2Norm_eq hf]
  exact mul_le_mul_of_nonneg_left (Heat.flow_l2Norm_le hf _) (Real.exp_pos _).le

end UnforcedLeray.AncientLocalization
