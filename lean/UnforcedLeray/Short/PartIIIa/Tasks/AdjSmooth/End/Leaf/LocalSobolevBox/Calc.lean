import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_4
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Auxiliary lemmas for `localSobolevBox` (SP 3060-3061): calculus on `ℝ × ℝ`, cutoff, double FTC.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.LSB

lemma contDiff_pdCx (k : Fin 2) {Ψ : ℝ × ℝ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ (pdCx k Ψ) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ Ψ) := (contDiff_infty_iff_fderiv.1 hΨ).2
  exact h1.clm_apply contDiff_const

lemma pdCx_mul {f g : ℝ × ℝ → ℂ} (k : Fin 2) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (y : ℝ × ℝ) :
    pdCx k (fun z => f z * g z) y = pdCx k f y * g y + f y * pdCx k g y := by
  have hf' : DifferentiableAt ℝ f y := (hf.differentiable (by simp)) y
  have hg' : DifferentiableAt ℝ g y := (hg.differentiable (by simp)) y
  unfold pdCx
  rw [fderiv_fun_mul hf' hg']
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma hasDerivAt_slice1 {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (x1 t : ℝ) :
    HasDerivAt (fun s => F (x1, s)) (pdCx 1 F (x1, t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((x1, s) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) t :=
    (hasDerivAt_const t x1).prodMk (hasDerivAt_id t)
  have h2 := ((hF.differentiable (by simp)) (x1, t)).hasFDerivAt.comp_hasDerivAt t h1
  have e : pdCx 1 F (x1, t) = fderiv ℝ F (x1, t) (0, 1) := by simp [pdCx, B0579.dir]
  rw [e]; exact h2

lemma hasDerivAt_slice0 {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (s x2 : ℝ) :
    HasDerivAt (fun r => F (r, x2)) (pdCx 0 F (s, x2)) s := by
  have h1 : HasDerivAt (fun r : ℝ => ((r, x2) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x2)
  have h2 := ((hF.differentiable (by simp)) (s, x2)).hasFDerivAt.comp_hasDerivAt s h1
  have e : pdCx 0 F (s, x2) = fderiv ℝ F (s, x2) (1, 0) := by simp [pdCx, B0579.dir]
  rw [e]; exact h2

/-- FTC in the second variable for a smooth field vanishing on `x₂ = a`. -/
lemma ftc1 {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (a x1 x2 : ℝ) (ha : F (x1, a) = 0) :
    F (x1, x2) = ∫ t in a..x2, pdCx 1 F (x1, t) := by
  have hc : Continuous (fun t => pdCx 1 F (x1, t)) :=
    ((contDiff_pdCx 1 hF).continuous).comp (Continuous.prodMk_right x1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_slice1 hF x1 t)
    (hc.intervalIntegrable _ _), ha, sub_zero]

lemma ftc0 {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (a x1 x2 : ℝ) (ha : F (a, x2) = 0) :
    F (x1, x2) = ∫ s in a..x1, pdCx 0 F (s, x2) := by
  have hc : Continuous (fun s => pdCx 0 F (s, x2)) :=
    ((contDiff_pdCx 0 hF).continuous).comp (Continuous.prodMk_left x2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_slice0 hF t x2)
    (hc.intervalIntegrable _ _), ha, sub_zero]

end UnforcedLeray.Short.IIIa.LSB
