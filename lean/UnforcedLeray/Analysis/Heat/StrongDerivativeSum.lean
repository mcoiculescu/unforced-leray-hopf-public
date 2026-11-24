import UnforcedLeray.Analysis.Heat.TimeBounds
import UnforcedLeray.Analysis.Heat.ConvolutionOrbit
import UnforcedLeray.Analysis.Heat.SobolevContinuity

/-!
# The actual heat time kernel and the sum of weak second derivatives

The equality below identifies genuine convolution operators by their concrete
integrable kernels. The resulting second-derivative sum is continuous in L²
on positive times because the actual heat path is continuous in the H² graph.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Heat

/-- The explicit time kernel equals the sum of the actual diagonal second kernels. -/
theorem timeDerivativeKernel_eq_secondSum {t : ℝ} (ht : 0 < t) (x : Space) :
    timeDerivativeKernel t x = ∑ i : Fin 3, secondDerivativeKernel t i i x := by
  rw [timeDerivativeKernel_eq_laplacian ht]
  simp only [laplacian, kernel_fderiv_coordinate, firstDerivativeKernel_fderiv]

/-- The actual time-derivative convolution is the sum of the actual second-derivative operators. -/
theorem timeDerivativeOperator_eq_secondSum {t : ℝ} (ht : 0 < t) :
    convolutionOperator (timeDerivativeKernel t) (timeDerivativeKernel_integrable ht) =
      ∑ i : Fin 3, secondDerivativeOperator ht i i := by
  apply ContinuousLinearMap.ext
  intro F
  rw [convolutionOperator_eq_integral_translationOrbit]
  simp_rw [timeDerivativeKernel_eq_secondSum ht, Finset.sum_smul]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    convolutionOrbit_integrable (secondDerivativeKernel t i i)
      (secondDerivativeKernel_integrable ht i i) F)]
  simp only [sum_apply, secondDerivativeOperator,
    convolutionOperator_eq_integral_translationOrbit]

/-- The genuine H² heat path has the same diagonal derivative sum at positive times. -/
theorem heatH2_secondSum_pos {t : ℝ} (ht : 0 < t) (F : L2Space) :
    (∑ i : Fin 3, (heatH2Path F t).second i i) =
      convolutionOperator (timeDerivativeKernel t) (timeDerivativeKernel_integrable ht) F := by
  rw [timeDerivativeOperator_eq_secondSum ht]
  simp only [sum_apply, heatH2Path_pos F ht, heatToH2_second]

/-- Continuity of the actual Laplacian in the L² norm on every positive-time interval. -/
theorem heatH2_secondSum_continuousOn (F : L2Space) :
    ContinuousOn (fun t : ℝ => ∑ i : Fin 3, (heatH2Path F t).second i i) (Ioi 0) := by
  apply continuousOn_finsetSum
  intro i _
  exact (SobolevGraph.H2.secondCLM i i).continuous.comp_continuousOn
    (heatH2Path_continuousOn F)

end UnforcedLeray.Heat
