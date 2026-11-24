import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_1
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Units.B0579
import UnforcedLeray.Lib.Gaussian.Kernel
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# `PartII-a:N01/9/1/3/3/2/1/1/2`: integration by parts for the planar heat gradient

Source `the November 2 reference manuscript`,
lines 3373-3383.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.PlaneHeatGradIBPAux

open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The coordinate embedding `Euc 2 → ℝ × ℝ` as a continuous linear map. -/
def coordL : Euc 2 →L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj (1 : Fin 2))

theorem coordL_eq (y : Euc 2) : coordL y = UnforcedLeray.B0224.planeι y := by
  simp [coordL, UnforcedLeray.B0224.planeι_apply]

theorem coordL_single (j : Fin 2) :
    coordL (EuclideanSpace.single j (1 : ℝ)) = UnforcedLeray.B0579.dir j := by
  rw [coordL_eq]
  fin_cases j <;> simp [UnforcedLeray.B0224.planeι_apply, UnforcedLeray.B0579.dir]

theorem sqrt_bound_aux {a r : ℝ} (ha : 0 < a) (_hr : 0 ≤ r) :
    √a * r * Real.exp (-(a / 2) * r ^ 2) ≤ 1 := by
  have hs : √a * √a = a := Real.mul_self_sqrt ha.le
  have h1' : √a * r ≤ 1 + (√a * √a / 2) * r ^ 2 := by
    nlinarith [sq_nonneg (√a * r - 1)]
  rw [hs] at h1'
  have h2 : 1 + (a / 2) * r ^ 2 ≤ Real.exp ((a / 2) * r ^ 2) := by
    linarith [Real.add_one_le_exp ((a / 2) * r ^ 2)]
  have hE : 0 < Real.exp (-(a / 2) * r ^ 2) := Real.exp_pos _
  calc √a * r * Real.exp (-(a / 2) * r ^ 2)
      ≤ Real.exp ((a / 2) * r ^ 2) * Real.exp (-(a / 2) * r ^ 2) :=
        mul_le_mul_of_nonneg_right (h1'.trans h2) hE.le
    _ = 1 := by
        rw [← Real.exp_add]
        simp

theorem abs_coord_mul_gauss_le {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (y : Euc 2) (j : Fin 2) :
    ‖y j * (c * Real.exp (-a * ‖y‖ ^ 2))‖ ≤
      c * (√a)⁻¹ * Real.exp (-(a / 2) * ‖y‖ ^ 2) := by
  have hr0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hjr : |y j| ≤ ‖y‖ := by
    have := PiLp.norm_apply_le y j
    rwa [Real.norm_eq_abs] at this
  have hE : Real.exp (-a * ‖y‖ ^ 2) =
      Real.exp (-(a / 2) * ‖y‖ ^ 2) * Real.exp (-(a / 2) * ‖y‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsa : 0 < √a := Real.sqrt_pos.2 ha
  have hs := sqrt_bound_aux ha hr0
  have hrE2 : ‖y‖ * Real.exp (-(a / 2) * ‖y‖ ^ 2) ≤ (√a)⁻¹ := by
    rw [← one_div, le_div_iff₀ hsa]
    linarith [hs, show ‖y‖ * Real.exp (-(a / 2) * ‖y‖ ^ 2) * √a
      = √a * ‖y‖ * Real.exp (-(a / 2) * ‖y‖ ^ 2) by ring]
  have hcE : 0 ≤ c * Real.exp (-a * ‖y‖ ^ 2) := mul_nonneg hc (Real.exp_pos _).le
  calc ‖y j * (c * Real.exp (-a * ‖y‖ ^ 2))‖
      = |y j| * (c * Real.exp (-a * ‖y‖ ^ 2)) := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcE]
    _ ≤ ‖y‖ * (c * Real.exp (-a * ‖y‖ ^ 2)) := mul_le_mul_of_nonneg_right hjr hcE
    _ = c * ((‖y‖ * Real.exp (-(a / 2) * ‖y‖ ^ 2)) * Real.exp (-(a / 2) * ‖y‖ ^ 2)) := by
        rw [hE]; ring
    _ ≤ c * ((√a)⁻¹ * Real.exp (-(a / 2) * ‖y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hrE2 (Real.exp_pos _).le) hc
    _ = c * (√a)⁻¹ * Real.exp (-(a / 2) * ‖y‖ ^ 2) := by ring

theorem integrable_coord_mul_gauss {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (j : Fin 2) :
    Integrable (fun y : Euc 2 => y j * (c * Real.exp (-a * ‖y‖ ^ 2))) := by
  have hint : Integrable (fun y : Euc 2 => c * (√a)⁻¹ * Real.exp (-(a / 2) * ‖y‖ ^ 2)) :=
    (UnforcedLeray.Gaussian.integrable_exp_neg_mul_sq_norm (d := 2) (half_pos ha)).const_mul _
  have hcj : Continuous fun y : Euc 2 => y j := (EuclideanSpace.proj j).continuous
  have hcont : Continuous fun y : Euc 2 => y j * (c * Real.exp (-a * ‖y‖ ^ 2)) :=
    hcj.mul (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_norm.pow 2))))
  exact Integrable.mono' hint hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => abs_coord_mul_gauss_le ha hc y j)

theorem fderiv_gauss_single {θ : ℝ} (hθ : 0 < θ) (y : Euc 2) (j : Fin 2) :
    fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ)) =
      -(y j / (2 * θ)) * gaussKernel 2 θ y := by
  have hK : gaussKernel 2 θ = fun z : Euc 2 =>
      (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * Real.exp (-(4 * θ)⁻¹ * ‖z‖ ^ 2) :=
    funext fun z => UnforcedLeray.Gaussian.gaussKernel_eq_exp z
  have h1 : HasFDerivAt (fun z : Euc 2 => ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have h2 := ((h1.const_mul (-(4 * θ)⁻¹)).exp).const_mul ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2))
  rw [hK, h2.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem integrable_real_smul_of_bdd {φ : Euc 2 → ℝ} {g : Euc 2 → ℂ} (hφ : Integrable φ)
    (hg : Continuous g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) :
    Integrable (fun y => φ y • g y) := by
  refine Integrable.mono' (hφ.norm.const_mul M)
    (hφ.aestronglyMeasurable.smul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

end UnforcedLeray.Short.PartIIa.N01.PlaneHeatGradIBPAux

open UnforcedLeray.Short.PartIIa.N01.PlaneHeatGradIBPAux in
open UnforcedLeray.Gaussian (Euc gaussKernel) in
theorem planeHeatGradIBP : UnforcedLeray.Short.PartIIa.N01.PlaneHeatGradIBP := by
  intro θ hθ f hf hb hd j x
  obtain ⟨M, hM⟩ := hb
  obtain ⟨N, hN⟩ := hd
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  have hfderc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hgd : ∀ y : Euc 2, HasFDerivAt (fun y : Euc 2 => f (x - UnforcedLeray.B0224.planeι y))
      ((fderiv ℝ f (x - UnforcedLeray.B0224.planeι y)).comp (-coordL)) y := by
    intro y
    have h1 : HasFDerivAt (fun z : Euc 2 => x - coordL z) (-coordL) y :=
      coordL.hasFDerivAt.const_sub x
    have h2 : HasFDerivAt f (fderiv ℝ f (x - coordL y)) (x - coordL y) :=
      (hfd (x - coordL y)).hasFDerivAt
    have h3 : HasFDerivAt (f ∘ fun z : Euc 2 => x - coordL z)
        ((fderiv ℝ f (x - coordL y)).comp (-coordL)) y := h2.comp y h1
    have hfun : (f ∘ fun z : Euc 2 => x - coordL z) =
        fun z : Euc 2 => f (x - UnforcedLeray.B0224.planeι z) := by
      funext z
      simp only [Function.comp_apply, coordL_eq]
    rw [hfun, coordL_eq y] at h3
    exact h3
  have hdg : ∀ y : Euc 2, fderiv ℝ (fun y : Euc 2 => f (x - UnforcedLeray.B0224.planeι y)) y
      (EuclideanSpace.single j (1 : ℝ)) =
      -(fderiv ℝ f (x - UnforcedLeray.B0224.planeι y) (UnforcedLeray.B0579.dir j)) := by
    intro y
    rw [(hgd y).fderiv]
    simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg,
      coordL_single]
  have hKd : ∀ y : Euc 2, DifferentiableAt ℝ (gaussKernel 2 θ) y := fun y =>
    ((UnforcedLeray.Gaussian.contDiff_gaussKernel (d := 2) (n := 1) θ).differentiable
      one_ne_zero) y
  have hKint : Integrable (gaussKernel 2 θ) :=
    UnforcedLeray.Gaussian.integrable_gaussKernel (d := 2) hθ
  have hgcont : Continuous (fun y : Euc 2 => f (x - UnforcedLeray.B0224.planeι y)) :=
    hfc.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)
  have hgbdd : ∀ y : Euc 2, ‖f (x - UnforcedLeray.B0224.planeι y)‖ ≤ M :=
    fun y => hM _
  have hdbdd : ∀ y : Euc 2,
      ‖fderiv ℝ f (x - UnforcedLeray.B0224.planeι y) (UnforcedLeray.B0579.dir j)‖ ≤
        N * ‖UnforcedLeray.B0579.dir j‖ := fun y =>
    ((fderiv ℝ f _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hN _) (norm_nonneg _))
  have hdcont : Continuous (fun y : Euc 2 =>
      fderiv ℝ f (x - UnforcedLeray.B0224.planeι y) (UnforcedLeray.B0579.dir j)) :=
    (hfderc.comp (continuous_const.sub UnforcedLeray.B0224.continuous_planeι)).clm_apply
      continuous_const
  -- integrability of the derivative of the kernel in direction `e_j`
  have hA_phi : Integrable (fun y : Euc 2 =>
      fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))) := by
    have ha : (0 : ℝ) < (4 * θ)⁻¹ := by positivity
    have hc : (0 : ℝ) ≤ (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    have hfun : (fun y : Euc 2 =>
        fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))) =
        fun y : Euc 2 => (-(1 / (2 * θ))) *
          (y j * ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * Real.exp (-(4 * θ)⁻¹ * ‖y‖ ^ 2))) := by
      funext y
      rw [fderiv_gauss_single hθ, UnforcedLeray.Gaussian.gaussKernel_eq_exp]
      ring
    rw [hfun]
    exact (integrable_coord_mul_gauss ha hc j).const_mul _
  have hA : Integrable (fun y : Euc 2 =>
      fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ)) •
        f (x - UnforcedLeray.B0224.planeι y)) :=
    integrable_real_smul_of_bdd hA_phi hgcont hgbdd
  have hBeq : (fun y : Euc 2 => gaussKernel 2 θ y •
      fderiv ℝ (fun y : Euc 2 => f (x - UnforcedLeray.B0224.planeι y)) y
        (EuclideanSpace.single j (1 : ℝ))) =
      fun y : Euc 2 => gaussKernel 2 θ y •
        (-(fderiv ℝ f (x - UnforcedLeray.B0224.planeι y) (UnforcedLeray.B0579.dir j))) := by
    funext y
    rw [hdg y]
  have hB : Integrable (fun y : Euc 2 => gaussKernel 2 θ y •
      fderiv ℝ (fun y : Euc 2 => f (x - UnforcedLeray.B0224.planeι y)) y
        (EuclideanSpace.single j (1 : ℝ))) := by
    rw [hBeq]
    exact integrable_real_smul_of_bdd hKint hdcont.neg (M := N * ‖UnforcedLeray.B0579.dir j‖)
      (fun y => by rw [norm_neg]; exact hdbdd y)
  have hC : Integrable (fun y : Euc 2 =>
      gaussKernel 2 θ y • f (x - UnforcedLeray.B0224.planeι y)) :=
    integrable_real_smul_of_bdd hKint hgcont hgbdd
  have hIBP := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := volume)
    (f := gaussKernel 2 θ) (g := fun y : Euc 2 => f (x - UnforcedLeray.B0224.planeι y))
    (v := EuclideanSpace.single j (1 : ℝ)) hA hB hC
    (fun y _ => hKd y) (fun y _ => (hgd y).differentiableAt)
  have hL : ∫ y : Euc 2, gaussKernel 2 θ y •
      fderiv ℝ f (x - UnforcedLeray.B0224.planeι y) (UnforcedLeray.B0579.dir j) =
      -∫ y : Euc 2, gaussKernel 2 θ y •
        fderiv ℝ (fun y : Euc 2 => f (x - UnforcedLeray.B0224.planeι y)) y
          (EuclideanSpace.single j (1 : ℝ)) := by
    rw [← integral_neg]
    congr 1
    funext y
    rw [hdg y, smul_neg, neg_neg]
  rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
  rw [hL, hIBP, neg_neg]
