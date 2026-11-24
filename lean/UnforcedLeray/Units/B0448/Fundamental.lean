import UnforcedLeray.Units.B0448.Symbol
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# B0448, part 3: `K` is the fundamental solution of `∂_t − Δ_z + 1` (tex 7666–7677)

Manuscript `paper/main.tex` lines 7666–7677 (blueprint unit B0448): `K` is "the causal inverse
kernel" of `∂_t − Δ_z + 1`, and "the identity `H = K*F` is distributionally valid". Here:

* `integral_gaussKernel_mul_cexp`: `∫ H_t(z) e^{2πi⟨w,z⟩} dz = e^{-4π²t|w|²}` (`t > 0`);
* `integral_kerC_mul_cexp`: `∫ K(X) e^{2πi⟨X,ξ⟩} dX = 1/symbolT(ξ)` (the inverse Fourier
  transform of `K` is the reciprocal symbol);
* `integral_kerC_sub_mul_resolventOpT`: `∫ K(X − Y) (Lᵗψ)(X) dX = ψ(Y)` for every Schwartz
  `ψ` and every `Y`, i.e. `(∂_t − Δ_z + 1)K = δ` against Schwartz tests.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.B0448

open MeasureTheory SchwartzMap FourierTransform Complex
open scoped SchwartzMap Real ENNReal

/-- **Gaussian Fourier transform.** For `t > 0`, `∫ H_t(z) e^{2πi⟨w,z⟩} dz = e^{-4π²t|w|²}`. -/
theorem integral_gaussKernel_mul_cexp {t : ℝ} (ht : 0 < t) (w : Space) :
    ∫ z : Space, (Gaussian.gaussKernel 3 t z : ℂ) * cexp (2 * π * I * ((inner ℝ w z : ℝ) : ℂ)) =
      cexp (((-(4 * π ^ 2 * t * ‖w‖ ^ 2)) : ℝ)) := by
  set b : ℂ := (((4 * t)⁻¹ : ℝ) : ℂ) with hb
  have hbre : 0 < b.re := by rw [hb, ofReal_re]; positivity
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := Space) hbre (2 * π * I) w
  have hfun : ∀ z : Space, (Gaussian.gaussKernel 3 t z : ℂ) *
      cexp (2 * π * I * ((inner ℝ w z : ℝ) : ℂ)) =
      (((4 * π * t) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
        cexp (-b * ‖z‖ ^ 2 + 2 * π * I * ((inner ℝ w z : ℝ) : ℂ)) := by
    intro z
    rw [Gaussian.gaussKernel, ofReal_mul, ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 3
    rw [hb]; push_cast; field_simp
  simp_rw [hfun]
  rw [integral_const_mul, h, finrank_euclideanSpace_fin]
  have hπb : (π : ℂ) / b = ((4 * π * t : ℝ) : ℂ) := by
    rw [hb]; push_cast; field_simp
  rw [hπb, show ((3 : ℕ) : ℂ) / 2 = (((3 : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← mul_assoc, ← ofReal_mul, ← Real.rpow_add (by positivity)]
  norm_num
  congr 1
  rw [hb]; push_cast; field_simp; ring_nf; rw [I_sq]; ring

/-- The causal kernel on `ST`, complex valued: `kerC (t, z) = K(t, z)`. -/
def kerC (X : ST) : ℂ := (kernel (WithLp.ofLp X) : ℂ)

theorem measurePreserving_ofLp :
    MeasurePreserving (MeasurableEquiv.toLp 2 (ℝ × Space)).symm :=
  WithLp.volume_preserving_symm_measurableEquiv_toLp_prod ℝ Space

theorem integral_ST_eq (g : ℝ × Space → ℂ) : ∫ X : ST, g (WithLp.ofLp X) = ∫ p, g p :=
  measurePreserving_ofLp.integral_comp' g

theorem integrable_ST_iff (g : ℝ × Space → ℂ) :
    Integrable (fun X : ST => g (WithLp.ofLp X)) ↔ Integrable g :=
  measurePreserving_ofLp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)

theorem integrable_kerC : Integrable kerC :=
  (integrable_ST_iff fun p => (kernel p : ℂ)).2 integrable_kernel.ofReal

theorem measurable_kerC : Measurable kerC :=
  Complex.measurable_ofReal.comp (measurable_kernel.comp (WithLp.measurable_ofLp 2 _))

theorem norm_kerC (X : ST) : ‖kerC X‖ = kernel (WithLp.ofLp X) := by
  rw [kerC, Complex.norm_real, Real.norm_of_nonneg (kernel_nonneg _)]

theorem inner_timeDir (ξ : ST) : inner ℝ ξ timeDir = (WithLp.ofLp ξ).1 := by
  simp [timeDir, WithLp.prod_inner_apply]

theorem inner_spaceDir (ξ : ST) (i : Fin 3) : inner ℝ ξ (spaceDir i) = (WithLp.ofLp ξ).2 i := by
  simp [spaceDir, WithLp.prod_inner_apply, EuclideanSpace.inner_single_right]

/-- `symbolT ξ = 1 − 2πi ξ_t + 4π² |ξ_z|²`. -/
theorem symbolT_eq (ξ : ST) : symbolT ξ =
    1 - 2 * π * I * (((WithLp.ofLp ξ).1 : ℝ) : ℂ) + 4 * π ^ 2 * ((‖(WithLp.ofLp ξ).2‖ ^ 2 : ℝ) : ℂ) := by
  rw [symbolT, inner_timeDir, EuclideanSpace.norm_sq_eq]
  simp_rw [inner_spaceDir, Real.norm_eq_abs, sq_abs]
  push_cast
  ring

/-- **The inverse Fourier transform of `K`.** `∫ K(X) e^{2πi⟨X,ξ⟩} dX = 1/symbolT(ξ)`, i.e.
`1/(1 − 2πiξ_t + 4π²|ξ_z|²)`. -/
theorem integral_kerC_mul_cexp (ξ : ST) :
    ∫ X, kerC X * cexp (2 * π * I * ((inner ℝ X ξ : ℝ) : ℂ)) = (symbolT ξ)⁻¹ := by
  set ω := (WithLp.ofLp ξ).1
  set w := (WithLp.ofLp ξ).2
  set s := symbolT ξ with hs
  have hin : ∀ X : ST, inner ℝ X ξ = (WithLp.ofLp X).1 * ω + inner ℝ w (WithLp.ofLp X).2 := by
    intro X
    rw [WithLp.prod_inner_apply, real_inner_comm w]
    simp [ω, w, mul_comm]
  simp_rw [hin]
  refine (integral_ST_eq (fun p : ℝ × Space => (kernel p : ℂ) * cexp (2 * π * I * ((p.1 * ω +
        inner ℝ w p.2 : ℝ) : ℂ)))).trans ?_
  have hint : Integrable (fun p : ℝ × Space => (kernel p : ℂ) *
      cexp (2 * π * I * ((p.1 * ω + inner ℝ w p.2 : ℝ) : ℂ))) := by
    refine (integrable_kernel.ofReal (𝕜 := ℂ)).norm.mono' ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact ((Complex.measurable_ofReal.comp measurable_kernel).mul
        (Continuous.measurable (by fun_prop))).aestronglyMeasurable
    · rw [norm_mul, norm_exp]
      simp
  rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hint)]
  have hslice : ∀ t : ℝ, (∫ z : Space, (kernel (t, z) : ℂ) *
      cexp (2 * π * I * ((t * ω + inner ℝ w z : ℝ) : ℂ))) =
      (Set.Ioi (0 : ℝ)).indicator (fun t => cexp (-s * t)) t := by
    intro t
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from ht)]
      have hk : ∀ z : Space, (kernel (t, z) : ℂ) *
          cexp (2 * π * I * ((t * ω + inner ℝ w z : ℝ) : ℂ)) =
          cexp ((-t : ℝ) + 2 * π * I * ((t * ω : ℝ) : ℂ)) *
            ((Gaussian.gaussKernel 3 t z : ℂ) * cexp (2 * π * I * ((inner ℝ w z : ℝ) : ℂ))) := by
        intro z
        simp only [kernel, Gaussian.causalKernel, ht, ite_true]
        push_cast
        rw [Complex.exp_add, mul_add, Complex.exp_add]
        ring
      simp_rw [hk]
      rw [integral_const_mul, integral_gaussKernel_mul_cexp ht, ← Complex.exp_add]
      congr 1
      rw [hs, symbolT_eq]
      push_cast
      ring
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) from ht)]
      have : ∀ z : Space, (kernel (t, z) : ℂ) = 0 := fun z => by
        rw [kernel_of_nonpos (not_lt.1 ht)]; simp
      simp [this]
  simp_rw [hslice]
  rw [integral_indicator measurableSet_Ioi]
  have hre : (-s).re < 0 := by
    have := one_le_re_symbolT ξ
    rw [neg_re]; linarith
  have h := integral_exp_mul_complex_Ioi hre 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero] at h
  rw [h, neg_div, div_neg, neg_neg, one_div]

/-- Fourier inversion for Schwartz functions, written out:
`f(X) = ∫ e^{2πi⟨ξ,X⟩} 𝓕 f(ξ) dξ`. -/
theorem schwartz_eq_integral_fourier (f : 𝓢(ST, ℂ)) (X : ST) :
    f X = ∫ ξ, cexp (2 * π * I * ((inner ℝ ξ X : ℝ) : ℂ)) * 𝓕 f ξ := by
  have h := congrArg (fun g : 𝓢(ST, ℂ) => g X) (FourierPair.fourierInv_fourier_eq (F := 𝓢(ST, ℂ)) f)
  rw [← h, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1; funext ξ
  rw [smul_eq_mul, SchwartzMap.fourier_coe]
  congr 2
  push_cast; ring

/-- **`K` is the fundamental solution of `∂_t − Δ_z + 1`** (tex 7666–7677): for every Schwartz
`ψ` and every `Y`, `∫ K(X − Y) (Lᵗψ)(X) dX = ψ(Y)`, with `Lᵗ = −∂_t − Δ_z + 1`. -/
theorem integral_kerC_sub_mul_resolventOpT (ψ : 𝓢(ST, ℂ)) (Y : ST) :
    ∫ X, kerC (X - Y) * resolventOpT ψ X = ψ Y := by
  set g := resolventOpT ψ with hg
  have hstep1 : ∀ X, kerC (X - Y) * g X =
      ∫ ξ, kerC (X - Y) * (cexp (2 * π * I * ((inner ℝ ξ X : ℝ) : ℂ)) * 𝓕 g ξ) := by
    intro X
    rw [schwartz_eq_integral_fourier g X, integral_const_mul]
  simp_rw [hstep1]
  have hint : Integrable (fun p : ST × ST => kerC (p.1 - Y) *
      (cexp (2 * π * I * ((inner ℝ p.2 p.1 : ℝ) : ℂ)) * 𝓕 g p.2)) (volume.prod volume) := by
    have hprod : Integrable (fun p : ST × ST => kerC (p.1 - Y) * (𝓕 g) p.2)
        (volume.prod volume) :=
      Integrable.mul_prod (integrable_kerC.comp_sub_right Y) (𝓕 g).integrable
    refine hprod.norm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine ((measurable_kerC.comp (measurable_fst.sub_const Y)).mul ?_).aestronglyMeasurable
      exact (Continuous.measurable (by fun_prop)).mul
        ((𝓕 g).continuous.measurable.comp measurable_snd)
    · rw [norm_mul, norm_mul, norm_mul, norm_exp]
      simp
  rw [integral_integral_swap hint]
  have hstep3 : ∀ ξ : ST, (∫ X, kerC (X - Y) *
      (cexp (2 * π * I * ((inner ℝ ξ X : ℝ) : ℂ)) * 𝓕 g ξ)) =
      cexp (2 * π * I * ((inner ℝ ξ Y : ℝ) : ℂ)) * 𝓕 ψ ξ := by
    intro ξ
    have htr := integral_sub_right_eq_self (μ := (volume : Measure ST))
      (fun Z => kerC Z * (cexp (2 * π * I * ((inner ℝ ξ (Z + Y) : ℝ) : ℂ)) * 𝓕 g ξ)) Y
    simp only [sub_add_cancel] at htr
    rw [htr]
    have hfac : ∀ Z : ST, kerC Z * (cexp (2 * π * I * ((inner ℝ ξ (Z + Y) : ℝ) : ℂ)) * 𝓕 g ξ) =
        (kerC Z * cexp (2 * π * I * ((inner ℝ Z ξ : ℝ) : ℂ))) *
          (cexp (2 * π * I * ((inner ℝ ξ Y : ℝ) : ℂ)) * 𝓕 g ξ) := by
      intro Z
      rw [inner_add_right, real_inner_comm Z ξ]
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
    simp_rw [hfac]
    rw [integral_mul_const, integral_kerC_mul_cexp, hg, fourier_resolventOpT]
    field_simp [symbolT_ne_zero ξ]
  simp_rw [hstep3]
  rw [schwartz_eq_integral_fourier ψ Y]

end UnforcedLeray.B0448
