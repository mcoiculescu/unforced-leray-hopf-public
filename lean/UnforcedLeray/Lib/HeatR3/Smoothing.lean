import UnforcedLeray.Lib.HeatR3.Smooth
import UnforcedLeray.Lib.ConvIneq.YoungGroup
import UnforcedLeray.Lib.Gaussian.LpNorm

/-!
# `L^p` gradient smoothing of the heat flow on `ℝ³` (INF04 T4, the `ℝ³` instance)


`eLpNorm_heatConvK_D1_le`, on `ℝ³` (the generic-group form is not built, see the status report):

`‖∂_w e^{θΔ}u‖_{L^p} ≤ c θ^{-1/2} |w| ‖u‖_{L^p}`,   `1 ≤ p ≤ ∞`, `θ > 0`,

with `c = ‖DG_1‖_{L¹(ℝ³)}` (`Gaussian.derivLpConst 3 1 1`). Proof: the directional derivative is
the convolution with the `L¹` kernel `DG_θ(·)w` (kernel side, `fderiv_kconv_apply`), Young's
`L¹ ⋆ L^p` inequality (`Conv.eLpNorm_convolution_le_L1`), and the exact scaling
`‖DG_θ‖_{L¹} = c θ^{-1/2}` (`Gaussian.eLpNorm_iteratedFDeriv_gaussKernel_toReal`).
Uses: B0142, B0296 (`e^{θΔ}∂_jF` smoothing), B0419–B0420.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The directional derivative of the heat flow of admissible data is a scalar-kernel
convolution: `∂_w e^{θΔ}f(x) = ∫ (DG_θ(x - y) w) f(y) dy`. -/
theorem fderiv_average_apply {f : Space → E} (hf : HeatAdmissible f) {θ : ℝ} (hθ : 0 < θ)
    (x w : Space) :
    fderiv ℝ (average θ f) x w = ∫ y : Space, (fderiv ℝ (kernel θ) (x - y) w) • f y := by
  obtain ⟨m, hm⟩ := hf.integrable_norm
  have hm0 : (0 : ℝ) ≤ m := by positivity
  rw [average_eq_kconv, fderiv_kconv_apply _ hm0 (decayKernel_gaussKernel hθ hm0) hf.1 hm x w]
  rfl

/-- `‖DG_θ(·) w‖_{L¹} ≤ c θ^{-1/2} |w|`. -/
theorem eLpNorm_fderiv_kernel_apply_le {θ : ℝ} (hθ : 0 < θ) (w : Space) :
    eLpNorm (fun z => fderiv ℝ (kernel θ) z w) 1 volume ≤
      ENNReal.ofReal (Gaussian.derivLpConst 3 1 1 * θ ^ (-(1 : ℝ) / 2) * ‖w‖) := by
  have h1 : eLpNorm (fun z => fderiv ℝ (kernel θ) z w) 1 volume ≤
      ENNReal.ofReal ‖w‖ * eLpNorm (iteratedFDeriv ℝ 1 (gaussKernel 3 θ)) 1 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := iteratedFDeriv ℝ 1 (gaussKernel 3 θ))
      (c := ‖w‖) (Eventually.of_forall fun z => ?_) 1
    rw [norm_iteratedFDeriv_one, Gaussian.gaussKernel_three_eq, mul_comm]
    exact (fderiv ℝ (kernel θ) z).le_opNorm w
  refine h1.trans (le_of_eq ?_)
  have hfin : eLpNorm (iteratedFDeriv ℝ 1 (gaussKernel 3 θ)) 1 volume ≠ ∞ :=
    (Gaussian.memLp_iteratedFDeriv_gaussKernel 1 hθ 1).eLpNorm_lt_top.ne
  rw [← ENNReal.ofReal_toReal hfin, Gaussian.eLpNorm_iteratedFDeriv_gaussKernel_toReal 1 hθ 1,
    ← ENNReal.ofReal_mul (norm_nonneg w)]
  congr 1
  norm_num
  ring

/-- **INF04 T4 `eLpNorm_heatConvK_D1_le`, ℝ³ instance.** For `u ∈ L^p(ℝ³)`, `1 ≤ p ≤ ∞`,
`θ > 0` and every direction `w`: `‖∂_w e^{θΔ}u‖_{L^p} ≤ c θ^{-1/2} |w| ‖u‖_{L^p}`. -/
theorem eLpNorm_fderiv_average_apply_le {u : Space → E} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hu : MemLp u p volume) {θ : ℝ} (hθ : 0 < θ) (w : Space) :
    eLpNorm (fun x => fderiv ℝ (average θ u) x w) p volume ≤
      ENNReal.ofReal (Gaussian.derivLpConst 3 1 1 * θ ^ (-(1 : ℝ) / 2) * ‖w‖) *
        eLpNorm u p volume := by
  have hadm := HeatAdmissible.of_memLp hp hu
  have hrep : (fun x => fderiv ℝ (average θ u) x w) =
      fun x => ∫ y : Space, (fderiv ℝ (kernel θ) (x - y) w) • u y :=
    funext fun x => fderiv_average_apply hadm hθ x w
  rw [hrep]
  have hKc : Continuous fun z => fderiv ℝ (kernel θ) z w :=
    (ContinuousLinearMap.apply ℝ ℝ w).continuous.comp
      (decayKernel_gaussKernel hθ le_rfl).fderiv.smooth.continuous
  refine (Conv.eLpNorm_convolution_le_L1 (μ := volume) (K := fun z => fderiv ℝ (kernel θ) z w)
    (f := u) hKc.aestronglyMeasurable hu.1 hp).trans ?_
  exact mul_le_mul_of_nonneg_right (eLpNorm_fderiv_kernel_apply_le hθ w) zero_le

end UnforcedLeray.Heat
