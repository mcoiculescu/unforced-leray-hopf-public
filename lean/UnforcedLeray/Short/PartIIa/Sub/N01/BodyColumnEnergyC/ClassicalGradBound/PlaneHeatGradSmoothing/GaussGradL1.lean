import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1_1
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.Gaussian.Kernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# `PartII-a:N01/9/1/3/3/2/1/1/1`: the gradient of the planar Gaussian is in `L¹` with norm `C θ^{-1/2}`

Source `the November 2 reference manuscript`,
lines 3373-3383 and 1684-1689.

The derivative `∂_j G_θ(y) = -(y_j/(2θ)) G_θ(y)` is integrable (domination by a Gaussian), and
the scaling `G_θ(√θ z) = θ^{-1} G_1(z)` gives `∫ |∂_j G_θ| = θ^{-1/2} ∫ |∂_j G_1|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.GaussGradL1Aux

open UnforcedLeray.Gaussian (Euc gaussKernel)

theorem sqrt_bound_aux {a r : ℝ} (ha : 0 < a) :
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
  have hs := sqrt_bound_aux (r := ‖y‖) ha
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

theorem fderiv_gauss_single (y : Euc 2) (j : Fin 2) (θ : ℝ) :
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

/-- The `j`-th derivative of the planar Gaussian is integrable. -/
theorem integrable_fderiv_gauss {θ : ℝ} (hθ : 0 < θ) (j : Fin 2) :
    Integrable (fun y : Euc 2 =>
      fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))) := by
  have ha : (0 : ℝ) < (4 * θ)⁻¹ := by positivity
  have hc : (0 : ℝ) ≤ (4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hfun : (fun y : Euc 2 =>
      fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))) =
      fun y : Euc 2 => (-(1 / (2 * θ))) *
        (y j * ((4 * Real.pi * θ) ^ (-((2 : ℕ) : ℝ) / 2) * Real.exp (-(4 * θ)⁻¹ * ‖y‖ ^ 2))) := by
    funext y
    rw [fderiv_gauss_single, UnforcedLeray.Gaussian.gaussKernel_eq_exp]
    ring
  rw [hfun]
  exact (integrable_coord_mul_gauss ha hc j).const_mul _

/-- The scalar `∫ |∂_j G_1|`. -/
def gaussGradS (j : Fin 2) : ℝ :=
  ∫ z : Euc 2, ‖fderiv ℝ (gaussKernel 2 1) z (EuclideanSpace.single j (1 : ℝ))‖

theorem gaussGradS_nonneg (j : Fin 2) : 0 ≤ gaussGradS j := by
  unfold gaussGradS
  exact integral_nonneg fun z => norm_nonneg _

theorem gaussKernel_scale_sqrt {θ : ℝ} (hθ : 0 < θ) (z : Euc 2) :
    gaussKernel 2 θ (Real.sqrt θ • z) = θ⁻¹ * gaussKernel 2 1 z := by
  have h := UnforcedLeray.Gaussian.gaussKernel_scale (d := 2) (lam := Real.sqrt θ) (θ := 1)
    (Real.sqrt_pos.2 hθ) one_pos z
  rw [mul_one, Real.sq_sqrt hθ.le] at h
  rw [h]
  congr 1
  rw [Real.rpow_neg (Real.sqrt_nonneg θ), Real.rpow_natCast, Real.sq_sqrt hθ.le]

theorem norm_fderiv_scale {θ : ℝ} (hθ : 0 < θ) (z : Euc 2) (j : Fin 2) :
    ‖fderiv ℝ (gaussKernel 2 θ) (Real.sqrt θ • z) (EuclideanSpace.single j (1 : ℝ))‖ =
      (Real.sqrt θ / θ ^ 2) *
        ‖fderiv ℝ (gaussKernel 2 1) z (EuclideanSpace.single j (1 : ℝ))‖ := by
  rw [fderiv_gauss_single, fderiv_gauss_single, gaussKernel_scale_sqrt hθ z,
    PiLp.smul_apply, smul_eq_mul]
  have hid : -(Real.sqrt θ * z j / (2 * θ)) * (θ⁻¹ * gaussKernel 2 1 z) =
      (Real.sqrt θ / θ ^ 2) * (-(z j / (2 * 1)) * gaussKernel 2 1 z) := by
    ring
  rw [hid, norm_mul, Real.norm_of_nonneg (by positivity)]

theorem integral_norm_fderiv {θ : ℝ} (hθ : 0 < θ) (j : Fin 2) :
    ∫ y : Euc 2, ‖fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))‖ =
      θ ^ (-(1 / 2 : ℝ)) * gaussGradS j := by
  have hcomp : ∫ z : Euc 2, ‖fderiv ℝ (gaussKernel 2 θ) (Real.sqrt θ • z)
      (EuclideanSpace.single j (1 : ℝ))‖ =
      θ⁻¹ * ∫ y : Euc 2, ‖fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))‖ := by
    have h := MeasureTheory.Measure.integral_comp_smul
      (μ := (volume : Measure (Euc 2)))
      (fun y : Euc 2 => ‖fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))‖)
      (Real.sqrt θ)
    rw [UnforcedLeray.Gaussian.finrank_euc, Real.sq_sqrt hθ.le, abs_inv, abs_of_pos hθ,
      smul_eq_mul] at h
    exact h
  have h1 : ∫ z : Euc 2, ‖fderiv ℝ (gaussKernel 2 θ) (Real.sqrt θ • z)
      (EuclideanSpace.single j (1 : ℝ))‖ = (Real.sqrt θ / θ ^ 2) * gaussGradS j := by
    simp only [norm_fderiv_scale hθ _ j]
    rw [integral_const_mul]
    rfl
  have hrpow : θ ^ (-(1 / 2 : ℝ)) = (Real.sqrt θ)⁻¹ := by
    rw [Real.rpow_neg hθ.le, ← Real.sqrt_eq_rpow]
  have hs0 : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ
  have hs2 : Real.sqrt θ * Real.sqrt θ = θ := Real.mul_self_sqrt hθ.le
  rw [hrpow]
  have hgen : ∀ s : ℝ, 0 < s → s * s * (s / (s * s) ^ 2) = s⁻¹ := by
    intro s hs
    have hs' : s ≠ 0 := hs.ne'
    field_simp
  have hkey0 : θ * (Real.sqrt θ / θ ^ 2) = (Real.sqrt θ)⁻¹ := by
    have h := hgen _ hs0
    rw [hs2] at h
    exact h
  have key : θ * ((Real.sqrt θ / θ ^ 2) * gaussGradS j) = (Real.sqrt θ)⁻¹ * gaussGradS j := by
    rw [← mul_assoc, hkey0]
  calc ∫ y : Euc 2, ‖fderiv ℝ (gaussKernel 2 θ) y (EuclideanSpace.single j (1 : ℝ))‖
      = θ * (θ⁻¹ * ∫ y : Euc 2, ‖fderiv ℝ (gaussKernel 2 θ) y
          (EuclideanSpace.single j (1 : ℝ))‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul]
    _ = θ * ((Real.sqrt θ / θ ^ 2) * gaussGradS j) := by rw [← h1, hcomp]
    _ = (Real.sqrt θ)⁻¹ * gaussGradS j := key

end UnforcedLeray.Short.PartIIa.N01.GaussGradL1Aux

open UnforcedLeray.Short.PartIIa.N01.GaussGradL1Aux in
open UnforcedLeray.Gaussian (Euc gaussKernel) in
theorem gaussGradL1 : UnforcedLeray.Short.PartIIa.N01.GaussGradL1 := by
  refine ⟨∑ j : Fin 2, gaussGradS j, ?_⟩
  intro θ hθ j
  refine ⟨integrable_fderiv_gauss hθ j, ?_⟩
  rw [integral_norm_fderiv hθ j, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hθ.le _)
  exact Finset.single_le_sum (f := gaussGradS) (fun i _ => gaussGradS_nonneg i)
    (Finset.mem_univ j)
