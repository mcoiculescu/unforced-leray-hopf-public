import UnforcedLeray.Lib.Parabolic.Tests
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Spatial Fourier transform of heat-kernel pairings (INF02 T6, Plancherel step of BP-A)


("spatial Plancherel and 1D Young"), target T6 of §5. Manuscript: the `q = 2` case of
eq:free-stress-11 (`paper/main.tex` lines 7447–7477, blueprint unit B0423).

Mathlib's Fourier transform `𝓕 f ξ = ∫ e^{-2πi⟨x,ξ⟩} f(x) dx` on `ℝ^d` (inner-product
normalisation) is used for complexified real functions.

* `gaussKernel_eq_fourier`: `G_τ(z) = ∫ e^{2πi⟨ξ,z⟩} e^{-4π²τ|ξ|²} dξ` (Gaussian Fourier
  inversion, from `fourier_gaussian_innerProductSpace`).
* `pairing_heat_eq`: for continuous compactly supported real `β, A` and `τ > 0`,
  `∫ β (G_τ ∗ A) = ∫ e^{-4π²τ|ξ|²} Â(ξ) \overline{β̂(ξ)} dξ`.
* `enorm_pairing_heat_le`: the `ℝ≥0∞` bound `‖∫ β (G_τ ∗ A)‖ₑ ≤ ∫⁻ e^{-4π²τ|ξ|²} ‖Â‖ₑ ‖β̂‖ₑ`.
* `fourier_dirDeriv`: `(∂_m a)^(ξ) = 2πi⟨ξ,m⟩ â(ξ)` for `C¹` compactly supported `a`.
* `lintegral_enorm_fourier_sq`: Plancherel, `∫⁻ |α̂|² = ∫⁻ |α|²` for real `C_c^∞` `α`.
* `continuous_fourier_slice`: `(s, ξ) ↦ (f(s,·))^(ξ)` is continuous for continuous compactly
  supported `f` on `ℝ × ℝ^d`.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Complex
open scoped ENNReal NNReal ContDiff RealInnerProductSpace FourierTransform

open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ}

/-- The unimodular exponential `e^{ia}`. -/
def ec (a : ℝ) : ℂ := Complex.exp (↑a * I)

theorem ec_add (a b : ℝ) : ec (a + b) = ec a * ec b := by
  simp only [ec, ofReal_add, add_mul, Complex.exp_add]

theorem norm_ec (a : ℝ) : ‖ec a‖ = 1 := by
  rw [ec, Complex.norm_exp_ofReal_mul_I]

theorem conj_ec (a : ℝ) : (starRingEnd ℂ) (ec a) = ec (-a) := by
  rw [ec, ec, ← Complex.exp_conj]
  simp [Complex.conj_ofReal]

theorem continuous_ec : Continuous ec := by
  unfold ec; fun_prop

/-- The complexification of a real function. -/
abbrev cplx {α : Type*} (f : α → ℝ) : α → ℂ := fun x => (f x : ℂ)

theorem fourier_eq_ec (f : Euc d → ℂ) (ξ : Euc d) :
    𝓕 f ξ = ∫ x, ec (-2 * π * ⟪x, ξ⟫) * f x := by
  rw [Real.fourier_eq']
  rfl

/-- The Fourier transform of a compactly supported continuous function is bounded by its
`L¹` norm. -/
theorem norm_fourier_le (f : Euc d → ℂ) (ξ : Euc d) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [fourier_eq_ec]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext x; rw [norm_mul, norm_ec, one_mul]

section Gauss

/-- **Gaussian Fourier inversion.** `G_τ(z) = ∫ e^{2πi⟨ξ,z⟩} e^{-4π²τ|ξ|²} dξ`. -/
theorem gaussKernel_eq_fourier {τ : ℝ} (hτ : 0 < τ) (z : Euc d) :
    (gaussKernel d τ z : ℂ) =
      ∫ ξ : Euc d, ec (2 * π * ⟪ξ, z⟫) * ((Real.exp (-(4 * π ^ 2 * τ) * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  set b : ℂ := ((4 * π ^ 2 * τ : ℝ) : ℂ) with hb
  have hbre : 0 < b.re := by rw [hb, Complex.ofReal_re]; positivity
  have h := fourier_gaussian_innerProductSpace (V := Euc d) hbre (-z)
  rw [fourier_eq_ec] at h
  have hlhs : (∫ x : Euc d, ec (-2 * π * ⟪x, -z⟫) * Complex.exp (-b * ‖x‖ ^ 2)) =
      ∫ ξ : Euc d, ec (2 * π * ⟪ξ, z⟫) * ((Real.exp (-(4 * π ^ 2 * τ) * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
    congr 1; funext ξ
    rw [inner_neg_right, show -2 * π * -⟪ξ, z⟫ = 2 * π * ⟪ξ, z⟫ by ring, hb, Complex.ofReal_exp]
    push_cast; ring_nf
  rw [hlhs] at h
  rw [h, Gaussian.gaussKernel, Gaussian.finrank_euc, norm_neg]
  -- the constants
  have hπb : (↑π : ℂ) / b = (((4 * π * τ)⁻¹ : ℝ) : ℂ) := by
    rw [hb]; push_cast; field_simp
  rw [hπb, show ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), Real.inv_rpow (by positivity), ← Real.rpow_neg
      (by positivity), Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  · congr 1; ring
  · rw [hb]; push_cast; field_simp

end Gauss

section Pairing

variable {β A : Euc d → ℝ}

/-- The Fourier multiplier `e^{-4π²τ|ξ|²}` of the heat kernel, as a complex number. -/
def gaussExp (τ : ℝ) (ξ : Euc d) : ℂ := ((Real.exp (-(4 * π ^ 2 * τ) * ‖ξ‖ ^ 2) : ℝ) : ℂ)

theorem continuous_gaussExp (τ : ℝ) : Continuous (gaussExp (d := d) τ) := by
  unfold gaussExp; fun_prop

theorem norm_gaussExp (τ : ℝ) (ξ : Euc d) :
    ‖gaussExp τ ξ‖ = Real.exp (-(4 * π ^ 2 * τ) * ‖ξ‖ ^ 2) := by
  rw [gaussExp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem integrable_gaussExp {τ : ℝ} (hτ : 0 < τ) : Integrable (gaussExp (d := d) τ) volume := by
  have := Gaussian.integrable_exp_neg_mul_sq_norm (d := d) (b := 4 * π ^ 2 * τ) (by positivity)
  have h2 : Integrable (fun ξ : Euc d => Real.exp (-(4 * π ^ 2 * τ) * ‖ξ‖ ^ 2)) volume := by
    simpa [neg_mul] using this
  exact h2.ofReal

/-- **Spatial Fourier inversion of `G_τ ∗ A`.** For continuous compactly supported `A`,
`(G_τ ∗ A)(x) = ∫ e^{-4π²τ|ξ|²} Â(ξ) e^{2πi⟨ξ,x⟩} dξ`. -/
theorem heatConv_eq_fourier {τ : ℝ} (hτ : 0 < τ) (hA : Continuous A) (hAc : HasCompactSupport A)
    (x : Euc d) :
    ((∫ z, gaussKernel d τ z * A (x - z) : ℝ) : ℂ) =
      ∫ ξ, gaussExp τ ξ * (ec (2 * π * ⟪ξ, x⟫) * 𝓕 (cplx A) ξ) := by
  have hγi : Integrable (gaussExp (d := d) τ) volume := integrable_gaussExp hτ
  have hAi : Integrable A volume := hA.integrable_of_hasCompactSupport hAc
  have hAx : Integrable (fun z => A (x - z)) volume := hAi.comp_sub_left x
  rw [← integral_complex_ofReal]
  have step1 : ∀ z, (((gaussKernel d τ z * A (x - z) : ℝ)) : ℂ) =
      ∫ ξ, ec (2 * π * ⟪ξ, z⟫) * gaussExp τ ξ * (A (x - z) : ℂ) := by
    intro z
    rw [Complex.ofReal_mul, gaussKernel_eq_fourier hτ z, ← integral_mul_const]
    rfl
  simp_rw [step1]
  have hcont : Continuous fun p : Euc d × Euc d =>
      ec (2 * π * ⟪p.2, p.1⟫) * gaussExp τ p.2 * (A (x - p.1) : ℂ) := by
    have h1 : Continuous fun p : Euc d × Euc d => ec (2 * π * ⟪p.2, p.1⟫) :=
      continuous_ec.comp (by fun_prop)
    have h2 : Continuous fun p : Euc d × Euc d => gaussExp (d := d) τ p.2 :=
      (continuous_gaussExp τ).comp continuous_snd
    have h3 : Continuous fun p : Euc d × Euc d => (A (x - p.1) : ℂ) :=
      Complex.continuous_ofReal.comp (hA.comp (by fun_prop))
    exact (h1.mul h2).mul h3
  have hint : Integrable (Function.uncurry fun (z ξ : Euc d) =>
      ec (2 * π * ⟪ξ, z⟫) * gaussExp τ ξ * (A (x - z) : ℂ)) (volume.prod volume) := by
    refine (hAx.ofReal.mul_prod hγi).norm.mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => le_of_eq ?_)
    simp only [Function.uncurry, norm_mul, norm_ec, one_mul, Complex.norm_real,
      RCLike.norm_ofReal, Real.norm_eq_abs]
    try ring
  rw [integral_integral_swap hint]
  congr 1; funext ξ
  have h1 : ∀ z, ec (2 * π * ⟪ξ, z⟫) * gaussExp τ ξ * (A (x - z) : ℂ) =
      gaussExp τ ξ * (ec (2 * π * ⟪ξ, x⟫) *
        (fun w => ec (-2 * π * ⟪w, ξ⟫) * (A w : ℂ)) (x - z)) := by
    intro z
    have he : ec (2 * π * ⟪ξ, z⟫) = ec (2 * π * ⟪ξ, x⟫) * ec (-2 * π * ⟪x - z, ξ⟫) := by
      rw [← ec_add]; congr 1
      rw [inner_sub_left, real_inner_comm ξ x, real_inner_comm ξ z]; ring
    rw [he]; ring
  simp_rw [h1]
  rw [integral_const_mul, integral_const_mul,
    integral_sub_left_eq_self (fun w => ec (-2 * π * ⟪w, ξ⟫) * (A w : ℂ)) volume x,
    fourier_eq_ec]

/-- **The Fourier form of the heat pairing.** For continuous compactly supported real `β, A`
and `τ > 0`: `∫ β (G_τ ∗ A) = ∫ e^{-4π²τ|ξ|²} Â(ξ) \overline{β̂(ξ)} dξ`. -/
theorem pairing_heat_eq {τ : ℝ} (hτ : 0 < τ) (hβ : Continuous β) (hβc : HasCompactSupport β)
    (hA : Continuous A) (hAc : HasCompactSupport A) :
    ((∫ x, β x * ∫ z, gaussKernel d τ z * A (x - z) : ℝ) : ℂ) =
      ∫ ξ, gaussExp τ ξ * 𝓕 (cplx A) ξ * (starRingEnd ℂ) (𝓕 (cplx β) ξ) := by
  have hγi : Integrable (gaussExp (d := d) τ) volume := integrable_gaussExp hτ
  have hβi : Integrable β volume := hβ.integrable_of_hasCompactSupport hβc
  have hAi : Integrable A volume := hA.integrable_of_hasCompactSupport hAc
  have hFA : ∀ ξ, ‖𝓕 (cplx A) ξ‖ ≤ ∫ x, ‖(A x : ℂ)‖ := fun ξ => norm_fourier_le _ ξ
  have hFAc : Continuous (𝓕 (cplx A)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hAi.ofReal
  rw [← integral_complex_ofReal]
  have step1 : ∀ x, (((β x * ∫ z, gaussKernel d τ z * A (x - z) : ℝ)) : ℂ) =
      ∫ ξ, (β x : ℂ) * (gaussExp τ ξ * 𝓕 (cplx A) ξ * ec (2 * π * ⟪ξ, x⟫)) := by
    intro x
    rw [Complex.ofReal_mul, heatConv_eq_fourier hτ hA hAc x, ← integral_const_mul]
    congr 1; funext ξ; ring
  simp_rw [step1]
  have hγA : Integrable (fun ξ => gaussExp τ ξ * 𝓕 (cplx A) ξ) volume :=
    hγi.mul_bdd hFAc.aestronglyMeasurable (Filter.Eventually.of_forall hFA)
  have hcont : Continuous fun p : Euc d × Euc d =>
      (β p.1 : ℂ) * (gaussExp τ p.2 * 𝓕 (cplx A) p.2 * ec (2 * π * ⟪p.2, p.1⟫)) := by
    have h1 : Continuous fun p : Euc d × Euc d => (β p.1 : ℂ) :=
      Complex.continuous_ofReal.comp (hβ.comp continuous_fst)
    have h2 : Continuous fun p : Euc d × Euc d => gaussExp (d := d) τ p.2 :=
      (continuous_gaussExp τ).comp continuous_snd
    have h3 : Continuous fun p : Euc d × Euc d => 𝓕 (cplx A) p.2 := hFAc.comp continuous_snd
    have h4 : Continuous fun p : Euc d × Euc d => ec (2 * π * ⟪p.2, p.1⟫) :=
      continuous_ec.comp (by fun_prop)
    exact h1.mul ((h2.mul h3).mul h4)
  have hint : Integrable (Function.uncurry fun (x ξ : Euc d) =>
      (β x : ℂ) * (gaussExp τ ξ * 𝓕 (cplx A) ξ * ec (2 * π * ⟪ξ, x⟫))) (volume.prod volume) := by
    refine (hβi.ofReal.mul_prod hγA).norm.mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => le_of_eq ?_)
    simp only [Function.uncurry, norm_mul, norm_ec, mul_one, Complex.norm_real,
      RCLike.norm_ofReal, Real.norm_eq_abs]
    try ring
  rw [integral_integral_swap hint]
  congr 1; funext ξ
  have hconj : (starRingEnd ℂ) (𝓕 (cplx β) ξ) = ∫ x, (β x : ℂ) * ec (2 * π * ⟪ξ, x⟫) := by
    rw [fourier_eq_ec, ← integral_conj]
    congr 1; funext x
    rw [map_mul, conj_ec, Complex.conj_ofReal, real_inner_comm]
    ring_nf
  rw [hconj, ← integral_const_mul]
  congr 1; funext x; ring

/-- **ℝ≥0∞ bound for the heat pairing.** -/
theorem enorm_pairing_heat_le {τ : ℝ} (hτ : 0 < τ) (hβ : Continuous β)
    (hβc : HasCompactSupport β) (hA : Continuous A) (hAc : HasCompactSupport A) :
    ‖∫ x, β x * ∫ z, gaussKernel d τ z * A (x - z)‖ₑ ≤
      ∫⁻ ξ, ENNReal.ofReal (Real.exp (-(4 * π ^ 2 * τ) * ‖ξ‖ ^ 2)) *
        ‖𝓕 (cplx A) ξ‖ₑ * ‖𝓕 (cplx β) ξ‖ₑ := by
  have h := pairing_heat_eq hτ hβ hβc hA hAc
  have h2 : ‖∫ x, β x * ∫ z, gaussKernel d τ z * A (x - z)‖ₑ =
      ‖((∫ x, β x * ∫ z, gaussKernel d τ z * A (x - z) : ℝ) : ℂ)‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  rw [h2, h]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1; funext ξ
  rw [enorm_mul, enorm_mul, RCLike.enorm_conj, ← ofReal_norm (gaussExp τ ξ), norm_gaussExp]

end Pairing

section Deriv

/-- **Fourier transform of a directional derivative.** For `C¹` compactly supported `a`,
`(∂_m a)^(ξ) = 2πi ⟨ξ, m⟩ â(ξ)`. -/
theorem fourier_dirDeriv {a : Euc d → ℂ} (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (m ξ : Euc d) :
    𝓕 (fun x => fderiv ℝ a x m) ξ = (2 * π * I * (⟪ξ, m⟫ : ℂ)) * 𝓕 a ξ := by
  have hai : Integrable a volume := ha.continuous.integrable_of_hasCompactSupport hac
  have hdi : Integrable (fderiv ℝ a) volume :=
    (ha.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hac.fderiv (𝕜 := ℝ))
  rw [← Real.fourier_continuousLinearMap_apply hdi,
    Real.fourier_fderiv hai (ha.differentiable (by simp)) hdi,
    VectorFourier.fourierSMulRight_apply]
  rw [show (-(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)) ξ m = -⟪ξ, m⟫ from rfl]
  simp only [smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- The complexification of a real `C¹` function has the complexified derivative. -/
theorem fderiv_cplx {a : Euc d → ℝ} (ha : Differentiable ℝ a) (x m : Euc d) :
    fderiv ℝ (cplx a) x m = (fderiv ℝ a x m : ℂ) := by
  have h : HasFDerivAt (cplx a) (Complex.ofRealCLM.comp (fderiv ℝ a x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (ha x).hasFDerivAt
  rw [h.fderiv]; rfl

/-- `|(∂_i∂_j α)^(ξ)| = 4π² |ξ_i| |ξ_j| |α̂(ξ)|` for real `C_c^∞` `α`. -/
theorem norm_fourier_second_deriv {α : Euc d → ℝ} (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    (i j : Fin d) (ξ : Euc d) :
    ‖𝓕 (cplx (fun y => fderiv ℝ (fun y' => fderiv ℝ α y' (ev j)) y (ev i))) ξ‖ =
      4 * π ^ 2 * |ξ.ofLp i| * |ξ.ofLp j| * ‖𝓕 (cplx α) ξ‖ := by
  set αj : Euc d → ℝ := fun y' => fderiv ℝ α y' (ev j)
  have hαj : ContDiff ℝ ∞ αj := (hα.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hαjc : HasCompactSupport αj := hαc.fderiv_apply ℝ (ev j)
  have e1 : cplx (fun y => fderiv ℝ αj y (ev i)) = fun y => fderiv ℝ (cplx αj) y (ev i) := by
    funext y; exact (fderiv_cplx (hαj.differentiable (by simp)) y (ev i)).symm
  have e2 : cplx αj = fun y => fderiv ℝ (cplx α) y (ev j) := by
    funext y; exact (fderiv_cplx (hα.differentiable (by simp)) y (ev j)).symm
  have hcα : ContDiff ℝ ∞ (cplx α) := Complex.ofRealCLM.contDiff.comp hα
  have hcαj : ContDiff ℝ ∞ (cplx αj) := Complex.ofRealCLM.contDiff.comp hαj
  have hcαc : HasCompactSupport (cplx α) := hαc.comp_left Complex.ofReal_zero
  have hcαjc : HasCompactSupport (cplx αj) := hαjc.comp_left Complex.ofReal_zero
  change ‖𝓕 (cplx (fun y => fderiv ℝ αj y (ev i))) ξ‖ = _
  rw [e1, fourier_dirDeriv (hcαj.of_le (by simp)) hcαjc, e2,
    fourier_dirDeriv (hcα.of_le (by simp)) hcαc]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
    Real.norm_eq_abs, EuclideanSpace.inner_single_right, abs_of_pos Real.pi_pos]
  simp only [mul_one, conj_trivial]
  ring

end Deriv

section Plancherel

/-- **Plancherel** for real `C_c^∞` functions on `ℝ^d`, in `ℝ≥0∞` form. -/
theorem lintegral_enorm_fourier_sq {α : Euc d → ℝ} (hα : ContDiff ℝ ∞ α)
    (hαc : HasCompactSupport α) :
    ∫⁻ ξ, ‖𝓕 (cplx α) ξ‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖α x‖ₑ ^ (2 : ℝ) := by
  have hcα : ContDiff ℝ ∞ (cplx α) := Complex.ofRealCLM.contDiff.comp hα
  have hcαc : HasCompactSupport (cplx α) := hαc.comp_left Complex.ofReal_zero
  set S := hcαc.toSchwartzMap hcα
  have hP := SchwartzMap.integral_norm_sq_fourier S
  rw [SchwartzMap.fourier_coe] at hP
  have hS : (S : Euc d → ℂ) = cplx α := rfl
  rw [hS] at hP
  have h1 : Integrable (fun ξ => ‖𝓕 (cplx α) ξ‖ ^ 2) volume := by
    have := (SchwartzMap.memLp (𝓕 S) 2 (μ := volume))
    rw [SchwartzMap.fourier_coe, hS] at this
    exact (memLp_two_iff_integrable_sq_norm this.1).1 this
  have h2 : Integrable (fun x => ‖cplx α x‖ ^ 2) volume := by
    have := (SchwartzMap.memLp S 2 (μ := volume))
    rw [hS] at this
    exact (memLp_two_iff_integrable_sq_norm this.1).1 this
  have e1 : ∀ ξ, ‖𝓕 (cplx α) ξ‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖𝓕 (cplx α) ξ‖ ^ 2) := by
    intro ξ; rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  have e2 : ∀ x, ‖α x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖cplx α x‖ ^ 2) := by
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Complex.norm_real]
    norm_num
  simp_rw [e1, e2]
  rw [← ofReal_integral_eq_lintegral_ofReal h1 (Filter.Eventually.of_forall fun _ => by positivity),
    ← ofReal_integral_eq_lintegral_ofReal h2 (Filter.Eventually.of_forall fun _ => by positivity),
    hP]

end Plancherel

section Slice

/-- The partial Fourier transform `(s, ξ) ↦ (f(s,·))^(ξ)` of a continuous compactly supported
function on `ℝ × ℝ^d` is continuous. -/
theorem continuous_fourier_slice {f : PS d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous fun p : ℝ × Euc d => 𝓕 (cplx fun x => f (p.1, x)) p.2 := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  set K : Set (Euc d) := Metric.closedBall 0 R
  have hK : IsCompact K := isCompact_closedBall 0 R
  have hzero : ∀ (s : ℝ) (x : Euc d), x ∉ K → f (s, x) = 0 := by
    intro s x hx
    by_contra h
    have hmem := hR (subset_tsupport f h)
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hx (by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_snd_le ((s, x) : PS d)).trans hmem)
  have heq : (fun p : ℝ × Euc d => 𝓕 (cplx fun x => f (p.1, x)) p.2) =
      fun p => ∫ x in K, ec (-2 * π * ⟪x, p.2⟫) * (f (p.1, x) : ℂ) := by
    funext p
    rw [fourier_eq_ec]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [hzero p.1 x hx]).symm
  rw [heq]
  refine continuous_parametric_integral_of_continuous ?_ hK
  refine (continuous_ec.comp ?_).mul (Complex.continuous_ofReal.comp (hf.comp ?_))
  · fun_prop
  · fun_prop

end Slice

end UnforcedLeray.Parabolic
