import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1_1
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Units.B0579
import UnforcedLeray.Lib.HeatR3.GroupDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# `SFCGaussIBP` (source 3426-3430): integration by parts against the Gaussian
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)

theorem planeι_sfcE_eq (j : Fin 2) :
    UnforcedLeray.B0224.planeι (sfcE j) = UnforcedLeray.B0579.dir j := by
  fin_cases j <;> ext <;> simp [sfcE, UnforcedLeray.B0579.dir, UnforcedLeray.B0224.planeι_apply]

theorem fderiv_gaussKernel_sfcE' (θ : ℝ) (hθ : 0 < θ) (j : Fin 2) (y : Euc 2) :
    fderiv ℝ (gaussKernel 2 θ) y (sfcE j) = UnforcedLeray.Heat.gaussD1 2 θ j y := by
  have hdiff : DifferentiableAt ℝ (gaussKernel 2 θ) y :=
    ((UnforcedLeray.Gaussian.contDiff_gaussKernel (d := 2) (n := 1) θ).differentiable
      (by norm_num)).differentiableAt
  have hline : HasDerivAt (fun t : ℝ => y + t • sfcE j) (sfcE j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (sfcE j)).const_add y
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have h2 := UnforcedLeray.Heat.hasDerivAt_gaussKernel_shift (d := 2) hθ j y 0
  have h3 := h1.unique h2
  simpa using h3

/-- **Lemma 4 (integration by parts, source 3426-3430).** -/
theorem sfcGaussIBP : SFCGaussIBP := by
  unfold SFCGaussIBP
  intro θ hθ f hf hbd z j hint
  obtain ⟨C, hC⟩ := hbd
  have hfdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hGdiff : Differentiable ℝ (gaussKernel 2 θ) :=
    (UnforcedLeray.Gaussian.contDiff_gaussKernel (d := 2) (n := 1) θ).differentiable (by norm_num)
  have hGc : Continuous (gaussKernel 2 θ) := UnforcedLeray.Gaussian.continuous_gaussKernel θ
  have hcontdG : Continuous (fun y : Euc 2 => fderiv ℝ (gaussKernel 2 θ) y (sfcE j)) :=
    ((UnforcedLeray.Gaussian.contDiff_gaussKernel (d := 2) (n := 1) θ).continuous_fderiv
      (by norm_num)).clm_apply continuous_const
  have hcontF : Continuous (fun y : Euc 2 => f (z - UnforcedLeray.B0224.planeι y)) :=
    hf.continuous.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)
  -- a linear map realising `planeι`
  obtain ⟨L, hL⟩ : ∃ L : Euc 2 →L[ℝ] ℝ × ℝ, ∀ y, L y = UnforcedLeray.B0224.planeι y :=
    ⟨(EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2)), fun y => rfl⟩
  have hfunL : (fun y : Euc 2 => z - UnforcedLeray.B0224.planeι y) = fun y => z - L y := by
    funext y
    rw [hL]
  have hDL : ∀ y : Euc 2, HasFDerivAt (fun y : Euc 2 => z - UnforcedLeray.B0224.planeι y) (-L) y :=
    fun y => by
      rw [hfunL]
      exact L.hasFDerivAt.const_sub z
  have hFc : ∀ y : Euc 2, HasFDerivAt (fun y : Euc 2 => f (z - UnforcedLeray.B0224.planeι y))
      ((fderiv ℝ f (z - UnforcedLeray.B0224.planeι y)).comp (-L)) y :=
    fun y => HasFDerivAt.comp y (hfdiff (z - UnforcedLeray.B0224.planeι y)).hasFDerivAt (hDL y)
  have hdir : ∀ x : Euc 2, fderiv ℝ (fun y : Euc 2 => f (z - UnforcedLeray.B0224.planeι y)) x
      (sfcE j) = -(fderiv ℝ f (z - UnforcedLeray.B0224.planeι x) (UnforcedLeray.B0579.dir j)) := by
    intro x
    rw [(hFc x).fderiv]
    simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg, hL,
      planeι_sfcE_eq]
  -- the Gaussian derivative envelope
  obtain ⟨A, hA0, hA⟩ := UnforcedLeray.Heat.abs_gaussD1_shift_le (d := 2) hθ j
  have hbdG : ∀ y : Euc 2, |fderiv ℝ (gaussKernel 2 θ) y (sfcE j)| ≤
      A * Real.exp (-(1 / (16 * θ)) * ‖y‖ ^ 2) := by
    intro y
    rw [fderiv_gaussKernel_sfcE' θ hθ j y]
    simpa using hA 0 (by simp) y
  have hint0 : Integrable (fun y : Euc 2 => gaussKernel 2 θ y • f (z - UnforcedLeray.B0224.planeι y)) := by
    refine ((UnforcedLeray.Gaussian.integrable_gaussKernel hθ).const_mul C).mono'
      (hGc.smul hcontF).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y), mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ y)
  have hint1 : Integrable (fun y : Euc 2 =>
      fderiv ℝ (gaussKernel 2 θ) y (sfcE j) • f (z - UnforcedLeray.B0224.planeι y)) := by
    refine ((((UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm
      (by positivity : (0 : ℝ) < 1 / (16 * θ)))).const_mul A).mul_const C).mono'
      (hcontdG.smul hcontF).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hbdG y) (hC _) (norm_nonneg _)
      (mul_nonneg hA0 (Real.exp_pos _).le)
  have hint2 : Integrable (fun y : Euc 2 =>
      gaussKernel 2 θ y • fderiv ℝ (fun y : Euc 2 => f (z - UnforcedLeray.B0224.planeι y)) y (sfcE j)) := by
    refine hint.neg.congr (Eventually.of_forall fun y => ?_)
    simp only [hdir y, smul_neg, Pi.neg_apply]
  have hIBP := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (f := gaussKernel 2 θ) (g := fun y : Euc 2 => f (z - UnforcedLeray.B0224.planeι y))
    (v := sfcE j) hint1 hint2 hint0
    (fun x _ => hGdiff x) (fun x _ => (hFc x).differentiableAt)
  beta_reduce at hIBP
  have e : ∫ x : Euc 2, gaussKernel 2 θ x • fderiv ℝ (fun y : Euc 2 => f (z - UnforcedLeray.B0224.planeι y)) x (sfcE j)
      = -∫ x : Euc 2, gaussKernel 2 θ x • fderiv ℝ f (z - UnforcedLeray.B0224.planeι x) (UnforcedLeray.B0579.dir j) := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [hdir x, smul_neg]
  rw [hIBP] at e
  exact neg_inj.1 e

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
