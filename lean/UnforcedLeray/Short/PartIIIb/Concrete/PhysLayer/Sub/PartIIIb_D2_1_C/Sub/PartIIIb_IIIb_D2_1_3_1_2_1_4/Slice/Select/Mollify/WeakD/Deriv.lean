import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_1
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Convolution
namespace UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem convYW_conv_eq (K : Space → ℝ) (f : Space → CVec3) (x : Space) :
    ∫ z : Space, K (x - z) • f z
      = convolution K f (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3) volume x := by
  rw [convolution_def]
  have h := integral_sub_left_eq_self (fun u : Space => K (x - u) • f u) volume x
  simp only [sub_sub_cancel] at h
  rw [← h]
  simp only [ContinuousLinearMap.lsmul_apply]

theorem convYW_fderiv (K : Space → ℝ) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (f : Space → CVec3) (hf : LocallyIntegrable f volume) (x : Space) :
    HasFDerivAt (fun x => ∫ z : Space, K (x - z) • f z)
      ((convolution (fderiv ℝ K) f
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompL Space) volume) x) x := by
  have hconv : (fun x => ∫ z : Space, K (x - z) • f z)
      = convolution K f (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3) volume := by
    funext x
    exact convYW_conv_eq K f x
  rw [hconv]
  exact hKc.hasFDerivAt_convolution_left _ (hK.of_le (by norm_num)) hf x

theorem convYW_fderiv_apply (K : Space → ℝ) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (f : Space → CVec3) (hf : LocallyIntegrable f volume) (x e : Space) :
    (convolution (fderiv ℝ K) f
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompL Space) volume x) e
      = ∫ z : Space, fderiv ℝ K (x - z) e • f z := by
  have hKd : HasCompactSupport (fderiv ℝ K) := HasCompactSupport.fderiv (𝕜 := ℝ) hKc
  have hKd' : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by simp)
  have hint := ((hKd.convolutionExists_left ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompL Space) hKd' hf) x).integrable
  rw [convolution_def, ContinuousLinearMap.integral_apply hint e]
  have h2 := integral_sub_left_eq_self (fun u : Space => fderiv ℝ K (x - u) e • f u) volume x
  simp only [sub_sub_cancel] at h2
  rw [← h2]
  rfl

theorem convYW_D_cont (K : Space → ℝ) (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    (f : Space → CVec3) (hf : LocallyIntegrable f volume) :
    Continuous (convolution (fderiv ℝ K) f
        ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompL Space) volume) := by
  have hKd : HasCompactSupport (fderiv ℝ K) := HasCompactSupport.fderiv (𝕜 := ℝ) hKc
  have hKd' : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by simp)
  exact hKd.continuous_convolution_left ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] CVec3 →L[ℝ] CVec3).precompL Space) hKd' hf

end UnforcedLeray.Short.PartIIIb.Concrete
