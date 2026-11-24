import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
Jet-norm bounds for iterated directional derivatives (helper for `inletSrcDerivBound`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 256
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Jets

variable {X V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem fderiv_apply_const {F : X → (X →L[ℝ] V)} (hF : Differentiable ℝ F) (a y b : X) :
    fderiv ℝ (fun z => F z a) y b = fderiv ℝ F y b a := by
  have h : fderiv ℝ (fun z => F z a) y = (ContinuousLinearMap.apply ℝ V a).comp (fderiv ℝ F y) :=
    ((ContinuousLinearMap.apply ℝ V a).hasFDerivAt.comp y (hF y).hasFDerivAt).fderiv
  rw [h]; rfl

theorem fderiv_apply_const' {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : X → (Y →L[ℝ] W)} (hF : Differentiable ℝ F) (a : Y) (y b : X) :
    fderiv ℝ (fun z => F z a) y b = fderiv ℝ F y b a := by
  have h : fderiv ℝ (fun z => F z a) y = (ContinuousLinearMap.apply ℝ W a).comp (fderiv ℝ F y) :=
    ((ContinuousLinearMap.apply ℝ W a).hasFDerivAt.comp y (hF y).hasFDerivAt).fderiv
  rw [h]; rfl

theorem norm_jet1 {F : X → V} (y v : X) :
    ‖fderiv ℝ F y v‖ ≤ ‖iteratedFDeriv ℝ 1 F y‖ * ‖v‖ := by
  rw [norm_iteratedFDeriv_one]
  exact (fderiv ℝ F y).le_opNorm v

theorem norm_jet2 {F : X → V} (hF : ContDiff ℝ ∞ F) (a y b : X) :
    ‖fderiv ℝ (fun z => fderiv ℝ F z a) y b‖ ≤ ‖iteratedFDeriv ℝ 2 F y‖ * ‖a‖ * ‖b‖ := by
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  rw [fderiv_apply_const hd]
  have h1 : ‖fderiv ℝ (fderiv ℝ F) y b a‖ ≤ ‖fderiv ℝ (fderiv ℝ F) y b‖ * ‖a‖ :=
    (fderiv ℝ (fderiv ℝ F) y b).le_opNorm a
  have h2 : ‖fderiv ℝ (fderiv ℝ F) y b‖ ≤ ‖fderiv ℝ (fderiv ℝ F) y‖ * ‖b‖ :=
    (fderiv ℝ (fderiv ℝ F) y).le_opNorm b
  have h3 : ‖fderiv ℝ (fderiv ℝ F) y‖ = ‖iteratedFDeriv ℝ 2 F y‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rw [h3] at h2
  have := norm_nonneg a
  have := norm_nonneg b
  calc _ ≤ ‖fderiv ℝ (fderiv ℝ F) y b‖ * ‖a‖ := h1
    _ ≤ (‖iteratedFDeriv ℝ 2 F y‖ * ‖b‖) * ‖a‖ := by gcongr
    _ = _ := by ring

theorem norm_jet3 {F : X → V} (hF : ContDiff ℝ ∞ F) (a y b : X) :
    ‖fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ F w a) z a) y b‖ ≤
      ‖iteratedFDeriv ℝ 3 F y‖ * ‖a‖ * ‖a‖ * ‖b‖ := by
  have hG : ContDiff ℝ ∞ (fun w => fderiv ℝ F w a) :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h2 := norm_jet2 hG a y b
  have hcomp : (fun w => fderiv ℝ F w a) =
      (ContinuousLinearMap.apply ℝ V a) ∘ (fderiv ℝ F) := rfl
  have hn : ‖ContinuousLinearMap.apply ℝ V a‖ ≤ ‖a‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
      (fun f => by simpa [mul_comm] using f.le_opNorm a)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by simp)
  have h3 := (ContinuousLinearMap.apply ℝ V a).norm_iteratedFDeriv_comp_left
    (hdf.contDiffAt (x := y)) (n := 2) (by simp)
  rw [← hcomp] at h3
  have h4 : ‖iteratedFDeriv ℝ 2 (fderiv ℝ F) y‖ = ‖iteratedFDeriv ℝ 3 F y‖ :=
    norm_iteratedFDeriv_fderiv
  have h5 : ‖iteratedFDeriv ℝ 2 (fun w => fderiv ℝ F w a) y‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ 3 F y‖ := by
    rw [← h4]; exact h3.trans (by gcongr)
  have := norm_nonneg a
  have := norm_nonneg b
  calc _ ≤ ‖iteratedFDeriv ℝ 2 (fun w => fderiv ℝ F w a) y‖ * ‖a‖ * ‖b‖ := h2
    _ ≤ (‖a‖ * ‖iteratedFDeriv ℝ 3 F y‖) * ‖a‖ * ‖b‖ := by gcongr
    _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.Jets

end
