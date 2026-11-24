import UnforcedLeray.Short.PartIIIa.Sub.T20_3

/-!
# Part III-a, task `PartIII-a:T20/3/4`: Fubini formula for the `η`-Fourier transform of a mode

Proves `UnforcedLeray.Short.IIIa.CTE.T20_3.FourierModeFormula` (`Sub/T20_3.lean`, the Prop
`/4` used by `ZeroMassModeBound`). Source of record:
`the November 2 reference manuscript`, lines 3236-3238.

Strategy. Unfold `𝓕` by `Real.fourier_real_eq_integral_exp_smul`; move the `η`-constant phase
`exp(-2πi η ξ)` inside the `q`-integral; swap the two integrals with `integral_prod_symm` on the
product measure `(μq c).prod volume = cellVol c`; then the pointwise identity
`exp(-2πi η ξ) · conj(e_k(q)) = exp(-i(κ_k q + 2πξη))` and `integral_smul`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace Real ComplexConjugate

open UnforcedLeray.B0581

namespace UnforcedLeray.Short.IIIa.CTE.T20_3

/-- The phase-weighted kernel `z ↦ exp(-2πi z₂ ξ) · coeffIntegrand c k u z`. -/
def kernelFT (c : ℝ) (k : ℤ) (u : B0579.Plane → ℂ) (ξ : ℝ) (z : B0579.Plane) : ℂ :=
  Complex.exp (((-2 * π * z.2 * ξ : ℝ) : ℂ) * Complex.I) • coeffIntegrand c k u z

/-- Phase identity: `exp(-2πi v ξ) · conj(e_k(q)) = exp(-i(κ_k q + 2π ξ v))`. -/
theorem exp_mul_conj_eMode_fm (c : ℝ) (k : ℤ) (q v ξ : ℝ) :
    Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) * conj (eMode c k q) =
      Complex.exp (-(Complex.I * ((kappa c k * q + 2 * π * ξ * v : ℝ) : ℂ))) := by
  unfold eMode kappa
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Pointwise form of the kernel: the kernel equals `(√c)⁻¹ · exp(-i(κ_k z₁ + 2πξ z₂)) · u z`. -/
theorem kernelFT_eq_fm (c : ℝ) (k : ℤ) (u : B0579.Plane → ℂ) (ξ : ℝ) (z : B0579.Plane) :
    kernelFT c k u ξ z = (((Real.sqrt c)⁻¹ : ℝ) : ℂ) •
      (Complex.exp (-(Complex.I * ((kappa c k * z.1 + 2 * π * ξ * z.2 : ℝ) : ℂ))) * u z) := by
  rw [← exp_mul_conj_eMode_fm c k z.1 z.2 ξ]
  simp only [kernelFT, coeffIntegrand, smul_eq_mul]
  ring

/-- Integrability of the `k`-th mode integrand `(√c)⁻¹ conj(e_k(q)) u(q, η)` on the product. -/
theorem integrable_coeffIntegrand_prod_fm (c : ℝ) (k : ℤ) {u : B0579.Plane → ℂ}
    (hu : Integrable u (cellVol c)) :
    Integrable (coeffIntegrand c k u) ((μq c).prod volume) := by
  have hu' : Integrable u ((μq c).prod volume) := by
    rw [← cellVol_eq]; exact hu
  refine Integrable.mono' (hu'.norm.const_mul ((Real.sqrt c)⁻¹)) ?_
    (Eventually.of_forall fun x => ?_)
  · have hs : Continuous (fun _ : B0579.Plane => (((Real.sqrt c)⁻¹ : ℝ) : ℂ)) :=
      continuous_const
    have hconj : Continuous (fun x : B0579.Plane => conj (eMode c k x.1)) :=
      Complex.continuous_conj.comp ((continuous_eMode c k).comp continuous_fst)
    exact hs.aestronglyMeasurable.smul (hconj.aestronglyMeasurable.smul hu'.1)
  · simp only [coeffIntegrand, norm_smul, Complex.norm_conj, norm_eMode, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg c)),
      le_refl]

/-- Integrability of the phase-weighted kernel on the product measure. -/
theorem integrable_kernelFT_fm (c : ℝ) (k : ℤ) (ξ : ℝ) {u : B0579.Plane → ℂ}
    (hu : Integrable u (cellVol c)) :
    Integrable (kernelFT c k u ξ) ((μq c).prod volume) := by
  have hF := integrable_coeffIntegrand_prod_fm c k hu
  have hc : Continuous (fun z : B0579.Plane =>
      Complex.exp (((-2 * π * z.2 * ξ : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  refine Integrable.mono' hF.norm ?_ (Eventually.of_forall fun z => ?_)
  · unfold kernelFT
    exact hc.aestronglyMeasurable.smul hF.1
  · simp only [kernelFT, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]

/-- Fubini on the cell: the iterated integral in `(q, η)` is the integral over `cellVol c`. -/
theorem integral_iter_eq_cellVol_fm (c : ℝ) (F : B0579.Plane → ℂ)
    (hF : Integrable F ((μq c).prod volume)) :
    ∫ v : ℝ, ∫ q in qInt c, F (q, v) = ∫ z, F z ∂(cellVol c) := by
  rw [integral_cellVol, integral_prod_symm F hF]

/-- **Fubini formula for the `η`-Fourier transform of a horizontal mode** (task `/4`;
SP 3236-3238). Proves `FourierModeFormula`. -/
theorem fourierModeFormula : FourierModeFormula := by
  intro c hc k u hu
  have hF : Integrable (coeffIntegrand c k u) ((μq c).prod volume) :=
    integrable_coeffIntegrand_prod_fm c k hu
  refine ⟨hF.integral_prod_right, fun ξ => ?_⟩
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc ∫ v : ℝ, Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) •
        ∫ q in qInt c, coeffIntegrand c k u (q, v)
      = ∫ v : ℝ, ∫ q in qInt c,
          Complex.exp (((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I) • coeffIntegrand c k u (q, v) := by
        congr 1
        funext v
        rw [integral_smul]
    _ = ∫ z, kernelFT c k u ξ z ∂(cellVol c) :=
        integral_iter_eq_cellVol_fm c (kernelFT c k u ξ) (integrable_kernelFT_fm c k ξ hu)
    _ = ∫ z, (((Real.sqrt c)⁻¹ : ℝ) : ℂ) •
          (Complex.exp (-(Complex.I * ((kappa c k * z.1 + 2 * π * ξ * z.2 : ℝ) : ℂ))) * u z)
          ∂(cellVol c) := by
        congr 1
        funext z
        exact kernelFT_eq_fm c k u ξ z
    _ = (((Real.sqrt c)⁻¹ : ℝ) : ℂ) • ∫ x, Complex.exp (-(Complex.I *
          ((kappa c k * x.1 + 2 * π * ξ * x.2 : ℝ) : ℂ))) * u x ∂(cellVol c) :=
        integral_smul _ _

end UnforcedLeray.Short.IIIa.CTE.T20_3
