import UnforcedLeray.Units.B0008
import UnforcedLeray.Analysis.GaussianVortex.ProfileBridge
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.LinearPMap

/-!
# B0009: planar Biot–Savart and the full Euler generator

Blueprint unit **B0009**, label `eq:st18-t00004`, `paper/main.tex` lines 662–670.

**Statement (tex 662–670).** `K = ∇^⊥Δ^{-1}` is planar Biot–Savart, with its convolution
realization `Kf(y) = (2π)^{-1} ∫ (y-z)^⊥ / |y-z|² f(z) dz`. The full Euler generator is
`𝓛f = -Ω ∂_ϑ f - (Kf)·∇E₀` with domain `𝒟(𝓛) = {f ∈ X_{j,M} : Ω ∂_ϑ f ∈ H^j_M}`, the derivative
in the domain condition being distributional.

**Conventions.**
* The plane is `ℂ` with Lebesgue measure, as in B0008 (`UnforcedLeray.B0008`); data are complex.
  `toPlane y = (y.re, y.im)` connects with the library's Cartesian Gaussian vortex
  (`UnforcedLeray.GaussianVortex`, blueprint unit B0006): `Ω(|y|)` is `Omega y`
  (`radialOmega ‖y‖`), `E₀` is `E0 y` (`radialVorticity ‖y‖`), and `∇E₀` is `gradE0`, the
  library's actual Cartesian gradient of the planar vorticity.
* `y^⊥ = (-y₂, y₁)`; for a complex `f` the field `Kf` has two complex components
  `biotSavart f 0`, `biotSavart f 1`. Each is a Mathlib convolution
  (`MeasureTheory.convolution`, `biotSavart_apply` gives the manuscript's integral). The kernel
  `kernel i z = (z^⊥)_i / (2π|z|²)` adapts `biotSavartKernel` of the NonUniqueEuler reference
  formalization (`NonUniqueEuler/lean/NonUniqueEuler/Statement/Plane.lean`, there `z^⊥ = i z`
  for real vorticities), split into near and far parts as in its
  `H/Sec2/Velocity/Kernel.lean`. At `z = 0` Lean's division gives `0` (a null set).
* Junk values. The Bochner integral defining `Kf(y)` is `0` where it diverges; for every
  integrable `f`, in particular every `f ∈ H^0_M` with `M > 1`, it converges absolutely for almost
  every `y` (`convolutionExistsAt_kernel`, `convolutionExistsAt_kernel_of_HjM`). This is exactly the
  "convolution realization on `L¹ ∩ L²` data" of the blueprint (INF12).
* `∂_ϑ φ (y) = Dφ(y)(y^⊥)` (`angDeriv`, with `y^⊥ = i y`); `hasDerivAt_rotation` checks that
  it is `d/dθ φ(e^{iθ} y)` at `θ = 0`. Since `div y^⊥ = 0` and `∂_ϑ Ω = 0`, the distribution
  `Ω ∂_ϑ f` is `φ ↦ -∫ f Ω ∂_ϑ φ`; `HasWeakTransport f g` says that it is the function `g`.
  `hasWeakTransport_of_contDiff` checks that classical `C¹` data satisfy it with
  `g = Ω ∂_ϑ f`.
* `transportDomain j M ⊆ H^j_M` is `{f : Ω ∂_ϑ f ∈ H^j_M}` and `domain j M ⊆ X_{j,M}` is
  `𝒟(𝓛)`. `transportLM` is `D_E = Ω ∂_ϑ` on its domain (well defined: `eq_of_hasWeakTransport`).
* The generator. That `A_E f = (Kf)·∇E₀` lies in `H^j_M` is the later unit B0061
  (`paper/main.tex:1222`), and the generation claim "This is an unbounded generator on the full
  space" is proved at `paper/main.tex:1245` (unit B0064; blueprint critic: B0009 is the
  definition only). Here `generator j hM` is the linear operator
  `𝒟(𝓛) → L⁰(ℝ²)` (`ℂ →ₘ[volume] ℂ`, functions modulo null sets), `f ↦ -Ω∂_ϑ f - (Kf)·∇E₀`, with
  exactly the manuscript's domain; `generatorH j hM` is the same operator on `H^j_M`.
  B0061/B0064 refine its codomain to `X_{j,M}`.

**Main declarations.** `kernel`, `biotSavart`, `biotSavart_apply`, `kernel_eq_perpGrad_newton`,
`convolutionExistsAt_kernel`, `gradE0`, `gradE0_eq`, `perturbation`, `angDeriv`,
`hasDerivAt_rotation`, `HasWeakTransport`, `hasWeakTransport_of_contDiff`,
`eq_of_hasWeakTransport`, `transportDomain`, `transportLM`, `domain`, `generatorH`, `generator`,
`generator_apply`, `testFn_mem_domain`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff

namespace UnforcedLeray.B0009

open NonUniqueEuler.Sob UnforcedLeray.B0008

/-! ### Planar conventions -/

/-- Cartesian coordinates `y ↦ (y₁, y₂)` of a point of the plane `ℂ`. -/
def toPlane (y : ℂ) : GaussianVortex.Plane := (y.re, y.im)

theorem radiusSq_toPlane (y : ℂ) : GaussianVortex.radiusSq (toPlane y) = ‖y‖ ^ 2 := by
  rw [GaussianVortex.radiusSq, toPlane, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem sqrt_radiusSq_toPlane (y : ℂ) : Real.sqrt (GaussianVortex.radiusSq (toPlane y)) = ‖y‖ := by
  rw [radiusSq_toPlane, Real.sqrt_sq (norm_nonneg y)]

/-- `Ω(|y|) = e^{-|y|²/4}` (`paper/main.tex:643`, unit B0006). -/
def Omega (y : ℂ) : ℝ := GaussianVortex.radialOmega ‖y‖

theorem Omega_eq_planarGaussian (y : ℂ) :
    Omega y = GaussianVortex.planarGaussian (toPlane y) := by
  rw [GaussianVortex.planarGaussian_eq_radialOmega, sqrt_radiusSq_toPlane, Omega]

theorem contDiff_Omega : ContDiff ℝ ∞ Omega := by
  have h : Omega = fun y : ℂ => Real.exp (-(‖y‖ ^ 2 / 4)) := rfl
  rw [h]
  exact Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).div_const 4).neg

/-- The background vorticity `E₀(|y|) = (2 - |y|²/2) e^{-|y|²/4}` (unit B0006). -/
def E0 (y : ℂ) : ℝ := GaussianVortex.radialVorticity ‖y‖

theorem E0_eq_vorticity (y : ℂ) : E0 y = GaussianVortex.vorticity (toPlane y) := by
  rw [GaussianVortex.vorticity_eq_radialVorticity, sqrt_radiusSq_toPlane, E0]

/-- `∇E₀(y)`: the library's actual Cartesian gradient of the planar vorticity `E₀`. -/
def gradE0 (y : ℂ) : GaussianVortex.Plane :=
  GaussianVortex.gradient GaussianVortex.vorticity (toPlane y)

/-- `∇E₀(y) = k(|y|) y` with `k(r) = E₀'(r)/r = (r²/4 - 2) e^{-r²/4}` (`paper/main.tex:648`). -/
theorem gradE0_eq (y : ℂ) :
    gradE0 y = (GaussianVortex.radialK ‖y‖ * y.re, GaussianVortex.radialK ‖y‖ * y.im) := by
  rw [gradE0, GaussianVortex.gradient_vorticity_eq_radialK, sqrt_radiusSq_toPlane]
  rfl

theorem continuous_radialK_norm : Continuous fun y : ℂ => GaussianVortex.radialK ‖y‖ := by
  unfold GaussianVortex.radialK GaussianVortex.radialOmega
  fun_prop

theorem continuous_gradE0_fst : Continuous fun y => (gradE0 y).1 := by
  simp only [gradE0_eq]
  exact continuous_radialK_norm.mul Complex.continuous_re

theorem continuous_gradE0_snd : Continuous fun y => (gradE0 y).2 := by
  simp only [gradE0_eq]
  exact continuous_radialK_norm.mul Complex.continuous_im

/-! ### The Biot–Savart kernel -/

/-- The components of `z^⊥ = (-z₂, z₁)` (indices `0, 1` for the manuscript's `1, 2`). -/
def perpComp : Fin 2 → ℂ → ℝ
  | 0, z => -z.im
  | 1, z => z.re

/-- The Biot–Savart kernel `K(z) = z^⊥ / (2π|z|²)`, component `i`, as a complex number. -/
def kernel (i : Fin 2) (z : ℂ) : ℂ := ((perpComp i z / (2 * Real.pi * ‖z‖ ^ 2) : ℝ) : ℂ)

theorem measurable_perpComp (i : Fin 2) : Measurable (perpComp i) := by
  fin_cases i
  · exact Complex.measurable_im.neg
  · exact Complex.measurable_re

theorem abs_perpComp_le (i : Fin 2) (z : ℂ) : |perpComp i z| ≤ ‖z‖ := by
  fin_cases i
  · simpa [perpComp] using Complex.abs_im_le_norm z
  · simpa [perpComp] using Complex.abs_re_le_norm z

theorem measurable_kernel (i : Fin 2) : Measurable (kernel i) :=
  Complex.measurable_ofReal.comp ((measurable_perpComp i).div (by fun_prop))

theorem norm_kernel_le (i : Fin 2) (z : ℂ) : ‖kernel i z‖ ≤ (2 * Real.pi * ‖z‖)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [kernel]
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hd : 0 < 2 * Real.pi * ‖z‖ ^ 2 := by positivity
  rw [kernel, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hd, div_le_iff₀ hd]
  calc |perpComp i z| ≤ ‖z‖ := abs_perpComp_le i z
    _ = (2 * Real.pi * ‖z‖)⁻¹ * (2 * Real.pi * ‖z‖ ^ 2) := by
      field_simp

theorem norm_kernel_le_of_notMem_ball (i : Fin 2) {z : ℂ} (hz : z ∉ ball (0 : ℂ) 1) :
    ‖kernel i z‖ ≤ (2 * Real.pi)⁻¹ := by
  have h1 : 1 ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
  refine (norm_kernel_le i z).trans (inv_anti₀ (by positivity) ?_)
  nlinarith [Real.pi_pos]

/-- The near part `1_{B₁} K` of the kernel is integrable (`|K(z)| ≤ (2π|z|)^{-1}`). -/
theorem integrableOn_kernel_ball (i : Fin 2) :
    IntegrableOn (kernel i) (ball (0 : ℂ) 1) volume := by
  refine integrableOn_ball_of_norm_le_rpow (C := (2 * Real.pi)⁻¹) (α := 1) ?_ ?_ ?_
    (measurable_kernel i).aestronglyMeasurable
  · rw [Complex.finrank_real_complex]; norm_num
  · rw [Complex.finrank_real_complex]; norm_num
  · refine ae_of_all _ fun z => ?_
    rw [Real.rpow_neg_one, ← mul_inv]
    exact norm_kernel_le i z

/-- The Newtonian potential `N(y) = (2π)^{-1} log|y| = (4π)^{-1} log |y|²`, `ΔN = δ`, so that
`K = ∇^⊥ Δ^{-1}` is convolution with `∇^⊥N`. -/
def newtonPotential (p : GaussianVortex.Plane) : ℝ :=
  (4 * Real.pi)⁻¹ * Real.log (GaussianVortex.radiusSq p)

theorem partialX_newtonPotential {p : GaussianVortex.Plane} (hp : GaussianVortex.radiusSq p ≠ 0) :
    GaussianVortex.partialX newtonPotential p =
      p.1 / (2 * Real.pi * GaussianVortex.radiusSq p) := by
  have h := (((hasDerivAt_pow 2 p.1).add_const (p.2 ^ 2)).log
    (by simpa [GaussianVortex.radiusSq] using hp)).const_mul (4 * Real.pi)⁻¹
  change deriv (fun x => (4 * Real.pi)⁻¹ * Real.log (x ^ 2 + p.2 ^ 2)) p.1 = _
  rw [h.deriv]
  simp only [GaussianVortex.radiusSq] at hp ⊢
  field_simp
  ring

theorem partialY_newtonPotential {p : GaussianVortex.Plane} (hp : GaussianVortex.radiusSq p ≠ 0) :
    GaussianVortex.partialY newtonPotential p =
      p.2 / (2 * Real.pi * GaussianVortex.radiusSq p) := by
  have h := (((hasDerivAt_pow 2 p.2).const_add (p.1 ^ 2)).log
    (by simpa [GaussianVortex.radiusSq] using hp)).const_mul (4 * Real.pi)⁻¹
  change deriv (fun y => (4 * Real.pi)⁻¹ * Real.log (p.1 ^ 2 + y ^ 2)) p.2 = _
  rw [h.deriv]
  simp only [GaussianVortex.radiusSq] at hp ⊢
  field_simp
  ring

/-- **`K = ∇^⊥ N` away from the origin**: the convolution kernel is the perpendicular gradient
of the Newtonian potential (`K = ∇^⊥Δ^{-1}`, `paper/main.tex:662`). -/
theorem kernel_eq_perpGrad_newton {z : ℂ} (hz : z ≠ 0) :
    kernel 0 z = ((GaussianVortex.perpendicularGradient newtonPotential (toPlane z)).1 : ℂ) ∧
      kernel 1 z = ((GaussianVortex.perpendicularGradient newtonPotential (toPlane z)).2 : ℂ) := by
  have hr : GaussianVortex.radiusSq (toPlane z) ≠ 0 := by
    rw [radiusSq_toPlane]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 hz)
  refine ⟨?_, ?_⟩
  · rw [GaussianVortex.perpendicularGradient, partialY_newtonPotential hr, radiusSq_toPlane]
    simp [kernel, perpComp, toPlane, neg_div]
  · rw [GaussianVortex.perpendicularGradient, partialX_newtonPotential hr, radiusSq_toPlane]
    simp [kernel, perpComp, toPlane]

/-! ### The Biot–Savart velocity -/

/-- The planar Biot–Savart velocity `Kf`, component `i`: the convolution `f ⋆ K_i`, i.e.
`(Kf)_i(y) = ∫ K_i(y - z) f(z) dz` (`biotSavart_apply`). -/
def biotSavart (f : ℂ → ℂ) (i : Fin 2) : ℂ → ℂ :=
  convolution f (kernel i) (ContinuousLinearMap.mul ℂ ℂ) volume

/-- The manuscript's formula `Kf(y) = (2π)^{-1} ∫ (y-z)^⊥/|y-z|² f(z) dz`, componentwise. -/
theorem biotSavart_apply (f : ℂ → ℂ) (i : Fin 2) (y : ℂ) :
    biotSavart f i y = ∫ z, kernel i (y - z) * f z := by
  simp only [biotSavart, convolution_def, ContinuousLinearMap.mul_apply']
  congr 1
  funext z
  ring

/-- **Convolution realization.** For integrable `f` the Biot–Savart integral converges
absolutely at almost every point. -/
theorem convolutionExistsAt_kernel {f : ℂ → ℂ} (hf : Integrable f volume) (i : Fin 2) :
    ∀ᵐ y ∂volume, ConvolutionExistsAt f (kernel i) y (ContinuousLinearMap.mul ℂ ℂ) volume := by
  set kn : ℂ → ℂ := (ball (0 : ℂ) 1).indicator (kernel i) with hkn
  set kf : ℂ → ℂ := (ball (0 : ℂ) 1)ᶜ.indicator (kernel i) with hkf
  have hn : Integrable kn volume :=
    (integrableOn_kernel_ball i).integrable_indicator measurableSet_ball
  have hkf_meas : Measurable kf := (measurable_kernel i).indicator measurableSet_ball.compl
  have hkf_le : ∀ z, ‖kf z‖ ≤ (2 * Real.pi)⁻¹ := by
    intro z
    by_cases hz : z ∈ ball (0 : ℂ) 1
    · rw [hkf, indicator_of_notMem (Set.notMem_compl_iff.2 hz), norm_zero]
      positivity
    · rw [hkf, indicator_of_mem (mem_compl hz)]
      exact norm_kernel_le_of_notMem_ball i hz
  have hfar : ∀ y, ConvolutionExistsAt f kf y (ContinuousLinearMap.mul ℂ ℂ) volume := by
    intro y
    refine Integrable.mono' (hf.norm.const_mul (2 * Real.pi)⁻¹) ?_ (ae_of_all _ fun t => ?_)
    · exact hf.aestronglyMeasurable.mul
        (hkf_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · simp only [ContinuousLinearMap.mul_apply', norm_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hkf_le _) (norm_nonneg _)
  filter_upwards [hf.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hn] with y hy
  have hsum : kernel i = kn + kf := (indicator_self_add_compl _ _).symm
  unfold ConvolutionExistsAt at hy hfar ⊢
  rw [hsum]
  refine (hy.add (hfar y)).congr (ae_of_all _ fun t => ?_)
  simp only [Pi.add_apply, map_add]

/-- On `H^j_M` with the manuscript's `M > 1` (so `f ∈ L¹ ∩ L²`), `Kf` is an absolutely
convergent convolution at almost every point (`paper/main.tex:657-662`). -/
theorem convolutionExistsAt_kernel_of_HjM {j : ℕ} {M : ℝ} (hM : 1 < M) (F : HjM j M)
    (i : Fin 2) : ∀ᵐ y ∂volume,
      ConvolutionExistsAt (F.value : ℂ → ℂ) (kernel i) y (ContinuousLinearMap.mul ℂ ℂ) volume :=
  convolutionExistsAt_kernel (HjM.integrable_value hM F) i

theorem aestronglyMeasurable_biotSavart {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume)
    (i : Fin 2) : AEStronglyMeasurable (biotSavart f i) volume :=
  (hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ)
    (measurable_kernel i).aestronglyMeasurable).integral_prod_right'

theorem biotSavart_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) (i : Fin 2) :
    biotSavart f i = biotSavart g i := by
  funext y
  simp only [biotSavart, convolution_def]
  refine integral_congr_ae ?_
  filter_upwards [h] with t ht
  rw [ht]

theorem biotSavart_add_ae {f g : ℂ → ℂ} (hf : Integrable f volume) (hg : Integrable g volume)
    (i : Fin 2) : biotSavart (f + g) i =ᵐ[volume] biotSavart f i + biotSavart g i := by
  filter_upwards [convolutionExistsAt_kernel hf i, convolutionExistsAt_kernel hg i]
    with y hfy hgy
  exact hfy.add_distrib hgy

theorem biotSavart_smul (c : ℂ) (f : ℂ → ℂ) (i : Fin 2) :
    biotSavart (c • f) i = c • biotSavart f i :=
  smul_convolution

/-! ### The perturbation `A_E f = (Kf)·∇E₀` -/

/-- `A_E f = (Kf)·∇E₀ = (Kf)₁ ∂₁E₀ + (Kf)₂ ∂₂E₀` (`paper/main.tex:666`, `1222`). -/
def perturbation (f : ℂ → ℂ) (y : ℂ) : ℂ :=
  biotSavart f 0 y * ((gradE0 y).1 : ℂ) + biotSavart f 1 y * ((gradE0 y).2 : ℂ)

theorem perturbation_congr_ae {f g : ℂ → ℂ} (h : f =ᵐ[volume] g) :
    perturbation f = perturbation g := by
  funext y
  simp only [perturbation, biotSavart_congr_ae h]

theorem aestronglyMeasurable_perturbation {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (perturbation f) volume :=
  ((aestronglyMeasurable_biotSavart hf 0).mul
      (Complex.continuous_ofReal.comp continuous_gradE0_fst).aestronglyMeasurable).add
    ((aestronglyMeasurable_biotSavart hf 1).mul
      (Complex.continuous_ofReal.comp continuous_gradE0_snd).aestronglyMeasurable)

theorem perturbation_add_ae {f g : ℂ → ℂ} (hf : Integrable f volume) (hg : Integrable g volume) :
    perturbation (f + g) =ᵐ[volume] fun y => perturbation f y + perturbation g y := by
  filter_upwards [biotSavart_add_ae hf hg 0, biotSavart_add_ae hf hg 1] with y h0 h1
  simp only [perturbation, h0, h1, Pi.add_apply]
  ring

theorem perturbation_smul (c : ℂ) (f : ℂ → ℂ) (y : ℂ) :
    perturbation (c • f) y = c * perturbation f y := by
  simp only [perturbation, biotSavart_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The distributional transport derivative `D_E = Ω ∂_ϑ` -/

/-- The angular derivative `∂_ϑ φ(y) = y^⊥·∇φ(y) = Dφ(y)(i y)`. -/
def angDeriv (φ : ℂ → ℂ) (y : ℂ) : ℂ := fderiv ℝ φ y (Complex.I * y)

/-- `∂_ϑ` is the derivative along rotations: `∂_ϑ φ(y) = d/dθ φ(e^{iθ} y)|_{θ=0}`. -/
theorem hasDerivAt_rotation {φ : ℂ → ℂ} {y : ℂ} (hφ : DifferentiableAt ℝ φ y) :
    HasDerivAt (fun θ : ℝ => φ (Complex.exp ((θ : ℂ) * Complex.I) * y)) (angDeriv φ y) 0 := by
  have h1 : HasDerivAt (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) * y)
      (Complex.I * y) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I).cexp).mul_const y
    simpa using this
  have h2 : Complex.exp (((0 : ℝ) : ℂ) * Complex.I) * y = y := by simp
  exact (hφ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 h2.symm)

/-- `Ω ∂_ϑ φ = V₀·∇φ` for a test function `φ`. -/
def transportOf (φ : ℂ → ℂ) (y : ℂ) : ℂ := (Omega y : ℂ) * angDeriv φ y

/-- **Distributional `Ω ∂_ϑ f = g`.** Since `div y^⊥ = 0` and `∂_ϑ Ω = 0`, the distribution
`Ω ∂_ϑ f` acts by `φ ↦ -∫ f Ω ∂_ϑ φ`; it is the function `g` iff
`∫ f · Ω ∂_ϑ φ = -∫ g φ` for every test function `φ` (`paper/main.tex:668-670`). -/
def HasWeakTransport (f g : ℂ → ℂ) : Prop :=
  ∀ φ : ℂ → ℂ, IsTestFn univ φ → ∫ y, f y * transportOf φ y = -∫ y, g y * φ y

theorem isTestFn_transportOf {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    IsTestFn univ (transportOf φ) := by
  refine ⟨?_, ?_, subset_univ _⟩
  · have hd : ContDiff ℝ ∞ (fderiv ℝ φ) := ContDiff.fderiv_right (m := ∞) hφ.smooth (by simp)
    have hO : ContDiff ℝ ∞ fun y => (Omega y : ℂ) :=
      Complex.ofRealCLM.contDiff.comp contDiff_Omega
    exact hO.mul (hd.clm_apply (contDiff_const.mul contDiff_id))
  · refine hφ.compact.mono' fun y hy => ?_
    by_contra h
    have h0 : fderiv ℝ φ y = 0 := Function.notMem_support.1 fun h' => h (support_fderiv_subset ℝ h')
    exact hy (by simp [transportOf, angDeriv, h0])

theorem isTestFn_ofReal {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    IsTestFn univ (fun y => (g y : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp hg, hc.comp_left Complex.ofReal_zero, subset_univ _⟩

theorem HasWeakTransport.congr {f f' g g' : ℂ → ℂ} (h : HasWeakTransport f g)
    (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') : HasWeakTransport f' g' := by
  intro φ hφ
  calc ∫ y, f' y * transportOf φ y = ∫ y, f y * transportOf φ y :=
        integral_congr_ae (by filter_upwards [hf] with y hy; rw [hy])
    _ = -∫ y, g y * φ y := h φ hφ
    _ = -∫ y, g' y * φ y := by
        rw [integral_congr_ae (by filter_upwards [hg] with y hy; rw [hy])]

/-! ### Classical data: `Ω ∂_ϑ` agrees with its distributional extension -/

/-- `toPlane` is the real-linear map `y ↦ (Re y, Im y)`. -/
def toPlaneCLM : ℂ →L[ℝ] GaussianVortex.Plane := Complex.reCLM.prod Complex.imCLM

theorem toPlane_eq_CLM : toPlane = ⇑toPlaneCLM := by
  funext w
  simp [toPlane, toPlaneCLM]

theorem fderiv_ofReal_comp_toPlane {u : GaussianVortex.Plane → ℝ} {y : ℂ}
    (hu : DifferentiableAt ℝ u (toPlane y)) (v : ℂ) :
    fderiv ℝ (fun y => (u (toPlane y) : ℂ)) y v = (fderiv ℝ u (toPlane y) (toPlane v) : ℂ) := by
  have hT : HasFDerivAt toPlane toPlaneCLM y := by
    rw [toPlane_eq_CLM]; exact toPlaneCLM.hasFDerivAt
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp y (hu.hasFDerivAt.comp y hT)
  have e2 : (fun y => (u (toPlane y) : ℂ)) = ⇑Complex.ofRealCLM ∘ (u ∘ toPlane) := by
    funext w; simp
  rw [e2, h3.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← toPlane_eq_CLM, Complex.ofRealCLM_apply]

/-- First component of `V₀ = Ω y^⊥` (the library's Gaussian velocity), as a complex function. -/
def V1 (y : ℂ) : ℂ := ((GaussianVortex.velocity (toPlane y)).1 : ℂ)

/-- Second component of `V₀ = Ω y^⊥`. -/
def V2 (y : ℂ) : ℂ := ((GaussianVortex.velocity (toPlane y)).2 : ℂ)

theorem contDiff_velocity_fst :
    ContDiff ℝ ∞ fun p : GaussianVortex.Plane => (GaussianVortex.velocity p).1 :=
  contDiff_fst.comp GaussianVortex.contDiff_velocity

theorem contDiff_velocity_snd :
    ContDiff ℝ ∞ fun p : GaussianVortex.Plane => (GaussianVortex.velocity p).2 :=
  contDiff_snd.comp GaussianVortex.contDiff_velocity

theorem contDiff_toPlane : ContDiff ℝ ∞ toPlane := by
  rw [toPlane_eq_CLM]; exact toPlaneCLM.contDiff

theorem contDiff_V1 : ContDiff ℝ ∞ V1 :=
  Complex.ofRealCLM.contDiff.comp (contDiff_velocity_fst.comp contDiff_toPlane)

theorem contDiff_V2 : ContDiff ℝ ∞ V2 :=
  Complex.ofRealCLM.contDiff.comp (contDiff_velocity_snd.comp contDiff_toPlane)

/-- `div V₀ = 0` in complex notation: `∂₁V₁ + ∂₂V₂ = 0` (library `divergence_velocity`). -/
theorem fderiv_V1_add_fderiv_V2 (y : ℂ) : fderiv ℝ V1 y 1 + fderiv ℝ V2 y Complex.I = 0 := by
  have hd1 := (contDiff_velocity_fst.differentiable (by simp)) (toPlane y)
  have hd2 := (contDiff_velocity_snd.differentiable (by simp)) (toPlane y)
  have h1 : fderiv ℝ V1 y 1 =
      ((fderiv ℝ (fun p => (GaussianVortex.velocity p).1) (toPlane y) (toPlane 1)) : ℂ) :=
    fderiv_ofReal_comp_toPlane (u := fun p => (GaussianVortex.velocity p).1) hd1 1
  have h2 : fderiv ℝ V2 y Complex.I =
      ((fderiv ℝ (fun p => (GaussianVortex.velocity p).2) (toPlane y) (toPlane Complex.I)) : ℂ) :=
    fderiv_ofReal_comp_toPlane (u := fun p => (GaussianVortex.velocity p).2) hd2 Complex.I
  have e1 : toPlane 1 = (1, 0) := by simp [toPlane]
  have e2 : toPlane Complex.I = (0, 1) := by simp [toPlane]
  have hdiv := GaussianVortex.divergence_velocity (toPlane y)
  rw [GaussianVortex.divergence, GaussianVortex.partialX_eq_fderiv hd1,
    GaussianVortex.partialY_eq_fderiv hd2] at hdiv
  rw [h1, h2, e1, e2, ← Complex.ofReal_add, hdiv, Complex.ofReal_zero]

/-- `Ω ∂_ϑ φ = V₀ · ∇φ = V₁ ∂₁φ + V₂ ∂₂φ`. -/
theorem Omega_mul_angDeriv (φ : ℂ → ℂ) (y : ℂ) :
    (Omega y : ℂ) * angDeriv φ y = V1 y * fderiv ℝ φ y 1 + V2 y * fderiv ℝ φ y Complex.I := by
  have hIy : Complex.I * y = (-y.im : ℝ) • (1 : ℂ) + (y.re : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  rw [angDeriv, hIy, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  simp only [V1, V2, GaussianVortex.velocity, Omega_eq_planarGaussian, toPlane]
  push_cast
  ring

theorem integral_ibp_dir {a h : ℂ → ℂ} (ha : ContDiff ℝ ∞ a) (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) (v : ℂ) :
    ∫ y, a y * fderiv ℝ h y v = -∫ y, fderiv ℝ a y v * h y := by
  have hda : Continuous fun y => fderiv ℝ a y v :=
    (ha.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdh : Continuous fun y => fderiv ℝ h y v :=
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => ha.differentiable (by simp) x) (fun x _ => hh.differentiable (by simp) x)
  · exact (hda.mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (ha.continuous.mul hdh).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v).mul_left
  · exact (ha.continuous.mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left

/-- `∫ Ω ∂_ϑ h = 0` for compactly supported `C¹` functions (`div (Ω y^⊥) = 0`). -/
theorem integral_Omega_angDeriv {h : ℂ → ℂ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h) :
    ∫ y, (Omega y : ℂ) * angDeriv h y = 0 := by
  have hdh (v : ℂ) : Continuous fun y => fderiv ℝ h y v :=
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdV1 : Continuous fun y => fderiv ℝ V1 y 1 :=
    (contDiff_V1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdV2 : Continuous fun y => fderiv ℝ V2 y Complex.I :=
    (contDiff_V2.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun y => V1 y * fderiv ℝ h y 1) volume :=
    (contDiff_V1.continuous.mul (hdh 1)).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) 1).mul_left
  have i2 : Integrable (fun y => V2 y * fderiv ℝ h y Complex.I) volume :=
    (contDiff_V2.continuous.mul (hdh Complex.I)).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) Complex.I).mul_left
  have j1 : Integrable (fun y => fderiv ℝ V1 y 1 * h y) volume :=
    (hdV1.mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left
  have j2 : Integrable (fun y => fderiv ℝ V2 y Complex.I * h y) volume :=
    (hdV2.mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left
  simp_rw [Omega_mul_angDeriv]
  rw [integral_add i1 i2, integral_ibp_dir contDiff_V1 hh hc 1,
    integral_ibp_dir contDiff_V2 hh hc Complex.I, ← neg_add, ← integral_add j1 j2]
  have hz : (fun y => fderiv ℝ V1 y 1 * h y + fderiv ℝ V2 y Complex.I * h y) = fun _ => 0 := by
    funext y
    rw [← add_mul, fderiv_V1_add_fderiv_V2, zero_mul]
  rw [hz, integral_zero, neg_zero]

/-- **Consistency of the distributional definition**: for `C¹` data the classical
`Ω ∂_ϑ f` is the distributional one. -/
theorem hasWeakTransport_of_contDiff {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) :
    HasWeakTransport f (transportOf f) := by
  intro φ hφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hψ := isTestFn_transportOf hφ
  have h0 := integral_Omega_angDeriv (hf.mul hφ1) hφ.compact.mul_left
  have hpt : ∀ y, (Omega y : ℂ) * angDeriv (fun x => f x * φ x) y =
      f y * transportOf φ y + transportOf f y * φ y := by
    intro y
    have e : (fun x => f x * φ x) = f * φ := rfl
    simp only [angDeriv, transportOf]
    rw [e, fderiv_mul (hf.differentiable (by simp) y) (hφ1.differentiable (by simp) y)]
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hTf : Continuous (transportOf f) :=
    (Complex.continuous_ofReal.comp contDiff_Omega.continuous).mul
      ((hf.continuous_fderiv (by simp)).clm_apply (continuous_const.mul continuous_id))
  have i1 : Integrable (fun y => f y * transportOf φ y) volume :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hψ.compact.mul_left
  have i2 : Integrable (fun y => transportOf f y * φ y) volume :=
    (hTf.mul hφ.continuous).integrable_of_hasCompactSupport hφ.compact.mul_left
  simp_rw [hpt] at h0
  rw [integral_add i1 i2] at h0
  linear_combination h0

section Lp

variable {j : ℕ} {M : ℝ}

theorem integrable_value_mul (F : HjM j M) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    Integrable (fun y => (F.value : ℂ → ℂ) y * φ y) volume :=
  integrable_mul_of_dualFun M (memLp_dualFun_testFn M hφ) F.value

theorem aestronglyMeasurable_value (F : HjM j M) :
    AEStronglyMeasurable (F.value : ℂ → ℂ) volume :=
  (Lp.aestronglyMeasurable F.value).mono_ac (volume_ac M)

theorem coeFn_value_add (F G : HjM j M) :
    ((F + G).value : ℂ → ℂ) =ᵐ[volume] fun y => F.value y + G.value y := by
  rw [HjM.value_add]
  exact (volume_ac M).ae_le (Lp.coeFn_add F.value G.value)

theorem coeFn_value_smul (c : ℂ) (F : HjM j M) :
    ((c • F).value : ℂ → ℂ) =ᵐ[volume] fun y => c * F.value y := by
  rw [HjM.value_smul]
  exact (volume_ac M).ae_le (Lp.coeFn_smul c F.value)

theorem coeFn_value_zero : ((0 : HjM j M).value : ℂ → ℂ) =ᵐ[volume] fun _ => (0 : ℂ) := by
  rw [HjM.value_zero]
  exact (volume_ac M).ae_le (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := wMeasure M))

theorem hasWeakTransport_add {F F' G G' : HjM j M} (h : HasWeakTransport F.value G.value)
    (h' : HasWeakTransport F'.value G'.value) :
    HasWeakTransport (F + F').value (G + G').value := by
  refine HasWeakTransport.congr ?_ (coeFn_value_add F F').symm (coeFn_value_add G G').symm
  intro φ hφ
  have hψ := isTestFn_transportOf hφ
  simp only [add_mul]
  rw [integral_add (integrable_value_mul F hψ) (integrable_value_mul F' hψ),
    integral_add (integrable_value_mul G hφ) (integrable_value_mul G' hφ), h φ hφ, h' φ hφ,
    neg_add]

theorem hasWeakTransport_smul (c : ℂ) {F G : HjM j M} (h : HasWeakTransport F.value G.value) :
    HasWeakTransport (c • F).value (c • G).value := by
  refine HasWeakTransport.congr ?_ (coeFn_value_smul c F).symm (coeFn_value_smul c G).symm
  intro φ hφ
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, h φ hφ, mul_neg]

theorem hasWeakTransport_zero :
    HasWeakTransport (0 : HjM j M).value (0 : HjM j M).value := by
  refine HasWeakTransport.congr ?_ coeFn_value_zero.symm coeFn_value_zero.symm
  intro φ _
  simp

/-- **Uniqueness**: `Ω ∂_ϑ f` determines its representative in `H^j_M`. -/
theorem eq_of_hasWeakTransport {F G G' : HjM j M} (h : HasWeakTransport F.value G.value)
    (h' : HasWeakTransport F.value G'.value) : G = G' := by
  have hae : ∀ᵐ y ∂volume, (G.value : ℂ → ℂ) y - G'.value y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((locallyIntegrable_L2w M G.value).sub (locallyIntegrable_L2w M G'.value)) ?_
    intro g hg hgc
    have hφ := isTestFn_ofReal hg hgc
    have hGG : ∫ y, G.value y * (g y : ℂ) = ∫ y, G'.value y * (g y : ℂ) :=
      neg_inj.1 ((h _ hφ).symm.trans (h' _ hφ))
    have hfun : (fun y => g y • ((G.value : ℂ → ℂ) y - G'.value y)) =
        fun y => G.value y * (g y : ℂ) - G'.value y * (g y : ℂ) := by
      funext y
      rw [Complex.real_smul]
      ring
    rw [hfun, integral_sub (integrable_value_mul G hφ) (integrable_value_mul G' hφ), hGG,
      sub_self]
  apply HjM.ext
  apply Lp.ext
  refine (wMeasure_ac M).ae_le ?_
  filter_upwards [hae] with y hy
  exact sub_eq_zero.1 hy

end Lp

/-! ### The domains and the generator -/

/-- `{f ∈ H^j_M : Ω ∂_ϑ f ∈ H^j_M}` (distributional `∂_ϑ`), the domain of `D_E` on `H^j_M`
(`paper/main.tex:667`, `1238-1239`). -/
def transportDomain (j : ℕ) (M : ℝ) : Submodule ℂ (HjM j M) where
  carrier := {F | ∃ G : HjM j M, HasWeakTransport F.value G.value}
  add_mem' := by
    rintro F F' ⟨G, hG⟩ ⟨G', hG'⟩
    exact ⟨G + G', hasWeakTransport_add hG hG'⟩
  zero_mem' := ⟨0, hasWeakTransport_zero⟩
  smul_mem' := by
    rintro c F ⟨G, hG⟩
    exact ⟨c • G, hasWeakTransport_smul c hG⟩

/-- **The domain `𝒟(𝓛) = {f ∈ X_{j,M} : Ω ∂_ϑ f ∈ H^j_M}`** (`paper/main.tex:667`). -/
def domain (j : ℕ) (M : ℝ) : Submodule ℂ (XjM j M) :=
  (transportDomain j M).comap (XjM j M).subtype

theorem mem_domain_iff {j : ℕ} {M : ℝ} (F : XjM j M) :
    F ∈ domain j M ↔ ∃ G : HjM j M, HasWeakTransport (F : HjM j M).value G.value :=
  Iff.rfl

section Generator

variable {j : ℕ} {M : ℝ}

/-- `D_E f = Ω ∂_ϑ f ∈ H^j_M` for `f` in the transport domain. -/
def transport (F : transportDomain j M) : HjM j M := F.2.choose

theorem hasWeakTransport_transport (F : transportDomain j M) :
    HasWeakTransport (F : HjM j M).value (transport F).value :=
  F.2.choose_spec

theorem transport_eq {F : transportDomain j M} {G : HjM j M}
    (h : HasWeakTransport (F : HjM j M).value G.value) : transport F = G :=
  eq_of_hasWeakTransport (hasWeakTransport_transport F) h

variable (j M) in
/-- `D_E = Ω ∂_ϑ` as a linear map on its domain. -/
def transportLM : transportDomain j M →ₗ[ℂ] HjM j M where
  toFun := transport
  map_add' F F' := transport_eq
    (hasWeakTransport_add (hasWeakTransport_transport F) (hasWeakTransport_transport F'))
  map_smul' c F := transport_eq (hasWeakTransport_smul c (hasWeakTransport_transport F))

/-- The function `𝓛f = -Ω ∂_ϑ f - (Kf)·∇E₀`. -/
def generatorFun (F : transportDomain j M) (y : ℂ) : ℂ :=
  -(transport F).value y - perturbation (F : HjM j M).value y

theorem aestronglyMeasurable_generatorFun (F : transportDomain j M) :
    AEStronglyMeasurable (generatorFun F) volume :=
  (aestronglyMeasurable_value _).neg.sub
    (aestronglyMeasurable_perturbation (aestronglyMeasurable_value _))

theorem generatorFun_add_ae (hM : 1 < M) (F F' : transportDomain j M) :
    generatorFun (F + F') =ᵐ[volume] fun y => generatorFun F y + generatorFun F' y := by
  have hT : transport (F + F') = transport F + transport F' := (transportLM j M).map_add F F'
  have hP : perturbation ((F + F' : transportDomain j M) : HjM j M).value =ᵐ[volume]
      fun y => perturbation (F : HjM j M).value y + perturbation (F' : HjM j M).value y := by
    rw [Submodule.coe_add, perturbation_congr_ae (coeFn_value_add (F : HjM j M) F')]
    exact perturbation_add_ae (HjM.integrable_value hM _) (HjM.integrable_value hM _)
  filter_upwards [hP, coeFn_value_add (transport F) (transport F')] with y hy hy'
  simp only [generatorFun, hT, hy, hy']
  ring

theorem generatorFun_smul_ae (c : ℂ) (F : transportDomain j M) :
    generatorFun (c • F) =ᵐ[volume] fun y => c * generatorFun F y := by
  have hT : transport (c • F) = c • transport F := (transportLM j M).map_smul c F
  have hP : perturbation ((c • F : transportDomain j M) : HjM j M).value =
      fun y => c * perturbation (F : HjM j M).value y := by
    rw [Submodule.coe_smul, perturbation_congr_ae (coeFn_value_smul c (F : HjM j M))]
    funext y
    exact perturbation_smul c _ y
  filter_upwards [coeFn_value_smul c (transport F)] with y hy
  simp only [generatorFun, hT, hy, hP]
  ring

variable (j) in
/-- **The full Euler generator on `H^j_M`**: `𝓛f = -Ω ∂_ϑ f - (Kf)·∇E₀` on
`{f ∈ H^j_M : Ω ∂_ϑ f ∈ H^j_M}`, valued in functions modulo null sets. Requires the
manuscript's `M > 1` (so that `Kf` is an absolutely convergent convolution). -/
def generatorH (hM : 1 < M) : HjM j M →ₗ.[ℂ] (ℂ →ₘ[volume] ℂ) where
  domain := transportDomain j M
  toFun :=
    { toFun := fun F => AEEqFun.mk (generatorFun F) (aestronglyMeasurable_generatorFun F)
      map_add' := fun F F' => by
        rw [AEEqFun.mk_add_mk, AEEqFun.mk_eq_mk]
        exact generatorFun_add_ae hM F F'
      map_smul' := fun c F => by
        rw [RingHom.id_apply, AEEqFun.smul_mk, AEEqFun.mk_eq_mk]
        exact generatorFun_smul_ae c F }

/-- The inclusion `𝒟(𝓛) → {f ∈ H^j_M : Ω ∂_ϑ f ∈ H^j_M}`. -/
def domainIncl : domain j M →ₗ[ℂ] transportDomain j M :=
  LinearMap.codRestrict (transportDomain j M) ((XjM j M).subtype.comp (domain j M).subtype)
    fun F => F.2

variable (j) in
/-- **The full Euler generator** `𝓛f = -Ω ∂_ϑ f - (Kf)·∇E₀` with domain
`𝒟(𝓛) = {f ∈ X_{j,M} : Ω ∂_ϑ f ∈ H^j_M}` (`eq:st18-t00004`, `paper/main.tex:664-668`). -/
def generator (hM : 1 < M) : XjM j M →ₗ.[ℂ] (ℂ →ₘ[volume] ℂ) where
  domain := domain j M
  toFun := (generatorH j hM).toFun.comp domainIncl

theorem generator_domain (hM : 1 < M) : (generator j hM).domain = domain j M := rfl


/-- The value of the generator: for `f ∈ 𝒟(𝓛)`, `𝓛f = -g - (Kf)·∇E₀` a.e., where
`g ∈ H^j_M` is the distributional `Ω ∂_ϑ f`. -/
theorem generator_apply (hM : 1 < M) (F : domain j M) {G : HjM j M}
    (hG : HasWeakTransport ((F : XjM j M) : HjM j M).value G.value) :
    (generator j hM F : ℂ → ℂ) =ᵐ[volume]
      fun y => -G.value y - perturbation ((F : XjM j M) : HjM j M).value y := by
  have hT : transport (domainIncl F) = G := transport_eq hG
  change (AEEqFun.mk (generatorFun (domainIncl F)) _ : ℂ → ℂ) =ᵐ[volume] _
  filter_upwards [AEEqFun.coeFn_mk (generatorFun (domainIncl F))
    (aestronglyMeasurable_generatorFun _)] with y hy
  rw [hy, generatorFun, hT]
  rfl

variable (j M) in
/-- Non-vacuity: every test function lies in `{f ∈ H^j_M : Ω ∂_ϑ f ∈ H^j_M}`, with
`Ω ∂_ϑ φ` the classical one. -/
theorem testFn_mem_transportDomain {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) :
    HjM.ofMemHjM (memHjM_of_testFn j M hφ) ∈ transportDomain j M :=
  ⟨HjM.ofMemHjM (memHjM_of_testFn j M (isTestFn_transportOf hφ)),
    (hasWeakTransport_of_contDiff (hφ.smooth.of_le (by simp))).congr
      (HjM.value_ofMemHjM _).symm (HjM.value_ofMemHjM _).symm⟩

/-- Non-vacuity of `𝒟(𝓛)`: a test function of integral zero lies in `𝒟(𝓛)`, and `𝓛` acts on it
by the classical formula `𝓛φ = -Ω ∂_ϑ φ - (Kφ)·∇E₀`. -/
theorem testFn_mem_domain (hM : 1 < M) {φ : ℂ → ℂ} (hφ : IsTestFn univ φ)
    (h0 : ∫ y, φ y = 0) :
    ∃ F : domain j M, (((F : XjM j M) : HjM j M).value : ℂ → ℂ) =ᵐ[volume] φ ∧
      (generator j hM F : ℂ → ℂ) =ᵐ[volume]
        fun y => -transportOf φ y - perturbation φ y := by
  obtain ⟨F0, hv⟩ : ∃ F0 : HjM j M, (F0.value : ℂ → ℂ) =ᵐ[volume] φ :=
    ⟨_, HjM.value_ofMemHjM (memHjM_of_testFn j M hφ)⟩
  obtain ⟨G0, hG⟩ : ∃ G0 : HjM j M, (G0.value : ℂ → ℂ) =ᵐ[volume] transportOf φ :=
    ⟨_, HjM.value_ofMemHjM (memHjM_of_testFn j M (isTestFn_transportOf hφ))⟩
  have hW : HasWeakTransport F0.value G0.value :=
    (hasWeakTransport_of_contDiff (hφ.smooth.of_le (by simp))).congr hv.symm hG.symm
  have hX : F0 ∈ XjM j M := by
    rw [mem_XjM_iff hM, integral_congr_ae hv]
    exact h0
  have hD : (⟨F0, hX⟩ : XjM j M) ∈ domain j M := ⟨G0, hW⟩
  refine ⟨⟨⟨F0, hX⟩, hD⟩, hv, ?_⟩
  filter_upwards [generator_apply hM ⟨⟨F0, hX⟩, hD⟩ (G := G0) hW, hG] with y hy hy'
  rw [hy, hy', perturbation_congr_ae hv]

end Generator

end UnforcedLeray.B0009
