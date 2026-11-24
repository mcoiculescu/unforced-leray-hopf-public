import UnforcedLeray.Lib.Gaussian.LpNorm
import UnforcedLeray.Lib.ConvIneq.YoungGroup
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Order.CompletePartialOrder

/-!
# The heat flow on the line (INF05 T18, with INF04 T2's `lineGauss`)


and the 1D part of T2. Covers the heat steps of units B0158 (tex 2394–2404: the `L¹_η`
contraction), B0163 (tex 2440–2453: `‖∂^k G_T‖_∞ ≤ C_k T^{-(k+1)/2}`) and B0164
(tex 2454–2467: `‖∂^{j+1}G_T‖_{L^p} ≤ C T^{-1-j/2+1/(2p)}`).

`lineGauss θ η = (4πθ)^{-1/2} e^{-η²/(4θ)}` is the 1D heat kernel at heat time `θ` (the
manuscript's `G_T(Y) = (4πT)^{-1/2}e^{-Y²/4T}`), identified with the generic
`Gaussian.gaussKernel 1 θ` through the linear isometry `lineIso : ℝ ≃ₗᵢ Euc 1`. Every statement
assumes `θ > 0`.

Main results:
* `lineGauss_eq`, `integral_lineGauss`, `norm_iteratedDeriv_lineGauss`;
* `eLpNorm_iteratedDeriv_lineGauss` (exact scaling, INF04 T2):
  `‖∂^k G_θ‖_{L^p(ℝ)} = c_{k,p} θ^{-k/2 - (1 - 1/p)/2}`, every `p`;
* `lineHeat`, `eLpNorm_lineHeat_le` (contraction on `L^p`, `1 ≤ p ≤ ∞`, B0158);
* `eLpNorm_lineHeat_of_L1` (`L¹ → L^p` smoothing);
* `iteratedDeriv_lineHeat` (kernel-side derivatives of the heat flow of `L¹` data) and
  `eLpNorm_iteratedDeriv_lineHeat` (`‖∂^k e^{θ∂²}f‖_p ≤ c_{k,p} θ^{-k/2-(1-1/p)/2}‖f‖_1`,
  B0163, B0164).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology Real
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

/-- The linear isometry `ℝ ≃ Euc 1`, `η ↦ (η)`. -/
def lineIso : ℝ ≃ₗᵢ[ℝ] Euc 1 := (OrthonormalBasis.singleton (Fin 1) ℝ).repr

@[simp] theorem lineIso_apply (η : ℝ) (i : Fin 1) : lineIso η i = η :=
  OrthonormalBasis.singleton_repr η i

theorem norm_lineIso (η : ℝ) : ‖lineIso η‖ = |η| := by
  rw [LinearIsometryEquiv.norm_map, Real.norm_eq_abs]

/-- `η ↦ (η)` preserves Lebesgue measure. -/
theorem measurePreserving_lineIso : MeasurePreserving lineIso volume volume := by
  let φ : Euc 1 ≃ᵐ ℝ := (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans
    (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have hφ : MeasurePreserving φ volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).comp
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))
  have h : (lineIso : ℝ → Euc 1) = φ.symm := by
    funext η
    ext i
    fin_cases i
    simp [φ, MeasurableEquiv.funUnique]
  rw [h]
  exact hφ.symm

/-- **INF04 T2 `lineGauss`.** The heat kernel on the line at heat time `θ`. -/
def lineGauss (θ η : ℝ) : ℝ := (4 * π * θ) ^ (-(1 : ℝ) / 2) * Real.exp (-η ^ 2 / (4 * θ))

theorem lineGauss_eq (θ η : ℝ) : lineGauss θ η = gaussKernel 1 θ (lineIso η) := by
  rw [lineGauss, Gaussian.gaussKernel, norm_lineIso, sq_abs, Nat.cast_one]

theorem lineGauss_eq_comp (θ : ℝ) : lineGauss θ = gaussKernel 1 θ ∘ lineIso :=
  funext (lineGauss_eq θ)

theorem lineGauss_nonneg {θ : ℝ} (hθ : 0 < θ) (η : ℝ) : 0 ≤ lineGauss θ η := by
  rw [lineGauss_eq]; exact Gaussian.gaussKernel_nonneg hθ _

theorem contDiff_lineGauss {n : WithTop ℕ∞} (θ : ℝ) : ContDiff ℝ n (lineGauss θ) := by
  rw [lineGauss_eq_comp]
  exact (Gaussian.contDiff_gaussKernel θ).comp lineIso.toContinuousLinearEquiv.contDiff

theorem continuous_lineGauss (θ : ℝ) : Continuous (lineGauss θ) :=
  (contDiff_lineGauss (n := 0) θ).continuous

theorem integrable_lineGauss {θ : ℝ} (hθ : 0 < θ) : Integrable (lineGauss θ) := by
  rw [lineGauss_eq_comp]
  exact (measurePreserving_lineIso.integrable_comp_emb
    lineIso.toHomeomorph.measurableEmbedding).mpr (Gaussian.integrable_gaussKernel hθ)

/-- The 1D heat kernel has unit mass. -/
theorem integral_lineGauss {θ : ℝ} (hθ : 0 < θ) : ∫ η, lineGauss θ η = 1 := by
  rw [lineGauss_eq_comp]
  change ∫ η, gaussKernel 1 θ (lineIso η) = 1
  rw [measurePreserving_lineIso.integral_comp lineIso.toHomeomorph.measurableEmbedding,
    Gaussian.integral_gaussKernel hθ]

/-- `|∂^k G_θ(η)| = ‖D^k G^{(1)}_θ(η)‖` (transfer to the generic Gaussian). -/
theorem norm_iteratedDeriv_lineGauss (k : ℕ) (θ η : ℝ) :
    ‖iteratedDeriv k (lineGauss θ) η‖ = ‖iteratedFDeriv ℝ k (gaussKernel 1 θ) (lineIso η)‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, lineGauss_eq_comp,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]

/-- **INF04 T2 `eLpNorm_iteratedDeriv_lineGauss`** (B0163, B0164), exact form: for `θ > 0` and
every `p`, `‖∂^k G_θ‖_{L^p(ℝ)} = c_{k,p} θ^{-k/2 - (1/2)(1 - 1/p)}` with
`c_{k,p} = Gaussian.derivLpConst 1 k p` (for finite `p` the exponent is the scoping note's
`-(k+1)/2 + 1/(2p)`). -/
theorem eLpNorm_iteratedDeriv_lineGauss (k : ℕ) {θ : ℝ} (hθ : 0 < θ) (p : ℝ≥0∞) :
    (eLpNorm (iteratedDeriv k (lineGauss θ)) p volume).toReal =
      Gaussian.derivLpConst 1 k p * θ ^ (-(k : ℝ) / 2 - (1 : ℝ) / 2 * (1 - (1 / p).toReal)) := by
  have h1 : eLpNorm (iteratedDeriv k (lineGauss θ)) p volume =
      eLpNorm (iteratedFDeriv ℝ k (gaussKernel 1 θ)) p volume := by
    rw [← eLpNorm_norm (iteratedDeriv k (lineGauss θ)),
      ← eLpNorm_norm (iteratedFDeriv ℝ k (gaussKernel 1 θ))]
    have : (fun η => ‖iteratedDeriv k (lineGauss θ) η‖) =
        (fun y => ‖iteratedFDeriv ℝ k (gaussKernel 1 θ) y‖) ∘ lineIso :=
      funext fun η => norm_iteratedDeriv_lineGauss k θ η
    rw [this, eLpNorm_comp_measurePreserving
      (((Gaussian.contDiff_gaussKernel (n := k) θ).continuous_iteratedFDeriv
        le_rfl).norm.aestronglyMeasurable) measurePreserving_lineIso]
  rw [h1, Gaussian.eLpNorm_iteratedFDeriv_gaussKernel_toReal k hθ p]
  norm_num

theorem memLp_iteratedDeriv_lineGauss (k : ℕ) {θ : ℝ} (hθ : 0 < θ) (p : ℝ≥0∞) :
    MemLp (iteratedDeriv k (lineGauss θ)) p volume := by
  have hm : MemLp (iteratedFDeriv ℝ k (gaussKernel 1 θ)) p volume :=
    Gaussian.memLp_iteratedFDeriv_gaussKernel k hθ p
  have hc : Continuous (iteratedDeriv k (lineGauss θ)) :=
    (contDiff_lineGauss (n := k) θ).continuous_iteratedDeriv k le_rfl
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  have h1 : eLpNorm (iteratedDeriv k (lineGauss θ)) p volume =
      eLpNorm (iteratedFDeriv ℝ k (gaussKernel 1 θ)) p volume := by
    rw [← eLpNorm_norm (iteratedDeriv k (lineGauss θ)),
      ← eLpNorm_norm (iteratedFDeriv ℝ k (gaussKernel 1 θ))]
    have : (fun η => ‖iteratedDeriv k (lineGauss θ) η‖) =
        (fun y => ‖iteratedFDeriv ℝ k (gaussKernel 1 θ) y‖) ∘ lineIso :=
      funext fun η => norm_iteratedDeriv_lineGauss k θ η
    rw [this, eLpNorm_comp_measurePreserving
      (((Gaussian.contDiff_gaussKernel (n := k) θ).continuous_iteratedFDeriv
        le_rfl).norm.aestronglyMeasurable) measurePreserving_lineIso]
  rw [h1]; exact hm.2

/-- Every derivative of the 1D heat kernel is bounded. -/
theorem iteratedDeriv_lineGauss_bounded (k : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ M : ℝ, ∀ η, ‖iteratedDeriv k (lineGauss θ) η‖ ≤ M := by
  obtain ⟨C, _, hC⟩ := Gaussian.norm_iteratedFDeriv_gaussKernel_le 1 k
  refine ⟨C * θ ^ (-((((1 : ℕ) : ℝ) + k) / 2)), fun η => ?_⟩
  rw [norm_iteratedDeriv_lineGauss]
  refine (hC hθ (lineIso η)).trans ?_
  have he : Real.exp (-‖lineIso η‖ ^ 2 / (8 * θ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ‖lineIso η‖])
      (by positivity))
  have hpos : 0 ≤ C * θ ^ (-((((1 : ℕ) : ℝ) + k) / 2)) := by
    have := (norm_nonneg _).trans (hC hθ (lineIso η))
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  calc C * θ ^ (-((((1 : ℕ) : ℝ) + k) / 2)) * Real.exp (-‖lineIso η‖ ^ 2 / (8 * θ))
      ≤ C * θ ^ (-((((1 : ℕ) : ℝ) + k) / 2)) * 1 := by gcongr
    _ = C * θ ^ (-((((1 : ℕ) : ℝ) + k) / 2)) := mul_one _

/-! ### The heat flow on the line -/

/-- **INF05 T18 `lineHeat`.** `e^{θ∂²}f(η) = ∫ G_θ(ξ) f(η - ξ) dξ`. -/
def lineHeat (θ : ℝ) (f : ℝ → ℝ) (η : ℝ) : ℝ := ∫ ξ, lineGauss θ ξ * f (η - ξ)

/-- The kernel-side form `e^{θ∂²}f(η) = ∫ G_θ(η - ξ) f(ξ) dξ`. -/
theorem lineHeat_eq_conv (θ : ℝ) (f : ℝ → ℝ) (η : ℝ) :
    lineHeat θ f η = ∫ ξ, lineGauss θ (η - ξ) * f ξ := by
  rw [lineHeat, ← integral_sub_left_eq_self (fun ξ => lineGauss θ (η - ξ) * f ξ) volume η]
  simp only [sub_sub_cancel]

/-- **INF05 T18 `eLpNorm_lineHeat_le`.** Contraction on `L^p(ℝ)`, `1 ≤ p ≤ ∞` (B0158 at
`p = 1`). -/
theorem eLpNorm_lineHeat_le {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f volume) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (lineHeat θ f) p volume ≤ eLpNorm f p volume := by
  have hrep : lineHeat θ f = fun η => ∫ ξ, lineGauss θ (η - ξ) • f ξ :=
    funext fun η => by rw [lineHeat_eq_conv]; rfl
  rw [hrep]
  refine (Conv.eLpNorm_convolution_le_L1 (μ := volume) (K := lineGauss θ) (f := f)
    (continuous_lineGauss θ).aestronglyMeasurable hf hp).trans ?_
  rw [eLpNorm_one_eq_lintegral_enorm]
  have h1 : ∫⁻ η, ‖lineGauss θ η‖ₑ = 1 := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_lineGauss hθ)]
    simp_rw [Real.norm_of_nonneg (lineGauss_nonneg hθ _)]
    rw [integral_lineGauss hθ, ENNReal.ofReal_one]
  rw [h1, one_mul]

/-- The heat flow of `f` written as the convolution `f ⋆ K` with the kernel `K` on the right. -/
theorem integral_kernel_right_eq (K f : ℝ → ℝ) (η : ℝ) :
    ∫ ξ, K (η - ξ) * f ξ = ∫ ξ, f (η - ξ) • K ξ := by
  rw [← integral_sub_left_eq_self (fun ξ => K (η - ξ) * f ξ) volume η]
  simp only [sub_sub_cancel, smul_eq_mul, mul_comm]

/-- **INF05 T18 `eLpNorm_lineHeat_of_L1`.** `‖e^{θ∂²}f‖_{L^p} ≤ ‖G_θ‖_{L^p} ‖f‖_{L¹}`,
`1 ≤ p ≤ ∞`, with `‖G_θ‖_{L^p} = c_p θ^{-(1 - 1/p)/2}` (`eLpNorm_iteratedDeriv_lineGauss`,
`k = 0`). -/
theorem eLpNorm_lineHeat_of_L1 {θ : ℝ} {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (lineHeat θ f) p volume ≤ eLpNorm f 1 volume * eLpNorm (lineGauss θ) p volume := by
  have hrep : lineHeat θ f = fun η => ∫ ξ, f (η - ξ) • lineGauss θ ξ :=
    funext fun η => by rw [lineHeat_eq_conv, integral_kernel_right_eq]
  rw [hrep]
  exact Conv.eLpNorm_convolution_le_L1 (μ := volume) (K := f) (f := lineGauss θ)
    hf (continuous_lineGauss θ).aestronglyMeasurable hp

/-- **INF05 T18, kernel-side derivatives.** For `f ∈ L¹(ℝ)` and `θ > 0`,
`∂^k e^{θ∂²}f(η) = ∫ ∂^kG_θ(η - ξ) f(ξ) dξ` for every `k`. -/
theorem iteratedDeriv_lineHeat {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ} (hf : Integrable f) (k : ℕ) :
    iteratedDeriv k (lineHeat θ f) =
      fun η => ∫ ξ, iteratedDeriv k (lineGauss θ) (η - ξ) * f ξ := by
  induction k with
  | zero =>
    rw [iteratedDeriv_zero]
    funext η
    rw [lineHeat_eq_conv, iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext η
    obtain ⟨M, hM⟩ := iteratedDeriv_lineGauss_bounded (k + 1) hθ
    obtain ⟨M₀, hM₀⟩ := iteratedDeriv_lineGauss_bounded k hθ
    have hcont : ∀ j : ℕ, Continuous (iteratedDeriv j (lineGauss θ)) := fun j =>
      (contDiff_lineGauss (n := j) θ).continuous_iteratedDeriv j le_rfl
    have hdiff : ∀ j : ℕ, Differentiable ℝ (iteratedDeriv j (lineGauss θ)) := fun j =>
      (contDiff_lineGauss (n := (j + 1 : ℕ)) θ).differentiable_iteratedDeriv j
        (by exact_mod_cast Nat.lt_succ_self j)
    have hmeas : ∀ j : ℕ, ∀ η', AEStronglyMeasurable
        (fun ξ => iteratedDeriv j (lineGauss θ) (η' - ξ) * f ξ) volume := fun j η' =>
      ((hcont j).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.1
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun η' ξ => iteratedDeriv k (lineGauss θ) (η' - ξ) * f ξ)
      (F' := fun η' ξ => iteratedDeriv (k + 1) (lineGauss θ) (η' - ξ) * f ξ)
      (bound := fun ξ => M * ‖f ξ‖) (x₀ := η) (s := univ) univ_mem
      (Eventually.of_forall fun η' => hmeas k η')
      ((hf.norm.const_mul M₀).mono' (hmeas k η) (Eventually.of_forall fun ξ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM₀ _) (norm_nonneg _)))
      (hmeas (k + 1) η)
      (Eventually.of_forall fun ξ η' _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
      (hf.norm.const_mul M)
      (Eventually.of_forall fun ξ η' _ => by
        have h1 : HasDerivAt (fun z : ℝ => z - ξ) 1 η' := (hasDerivAt_id η').sub_const ξ
        have h2 := ((hdiff k) (η' - ξ)).hasDerivAt.comp η' h1
        rw [mul_one, ← iteratedDeriv_succ] at h2
        exact h2.mul_const (f ξ))
    exact key.2.deriv

/-- **INF05 T18 `eLpNorm_iteratedDeriv_lineHeat`** (B0163, B0164). For `f ∈ L¹(ℝ)`, `θ > 0`,
`1 ≤ p ≤ ∞`: `‖∂^k e^{θ∂²}f‖_{L^p} ≤ ‖∂^kG_θ‖_{L^p} ‖f‖_{L¹}
  = c_{k,p} θ^{-k/2 - (1-1/p)/2} ‖f‖_{L¹}`. -/
theorem eLpNorm_iteratedDeriv_lineHeat {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ} (hf : Integrable f)
    (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (iteratedDeriv k (lineHeat θ f)) p volume ≤
      eLpNorm f 1 volume * ENNReal.ofReal (Gaussian.derivLpConst 1 k p *
        θ ^ (-(k : ℝ) / 2 - (1 : ℝ) / 2 * (1 - (1 / p).toReal))) := by
  rw [iteratedDeriv_lineHeat hθ hf k]
  have hrep : (fun η => ∫ ξ, iteratedDeriv k (lineGauss θ) (η - ξ) * f ξ) =
      fun η => ∫ ξ, f (η - ξ) • iteratedDeriv k (lineGauss θ) ξ :=
    funext fun η => integral_kernel_right_eq _ f η
  rw [hrep]
  refine (Conv.eLpNorm_convolution_le_L1 (μ := volume) (K := f)
    (f := iteratedDeriv k (lineGauss θ)) hf.1
    (memLp_iteratedDeriv_lineGauss k hθ p).1 hp).trans (le_of_eq ?_)
  rw [← eLpNorm_iteratedDeriv_lineGauss k hθ p, ENNReal.ofReal_toReal
    (memLp_iteratedDeriv_lineGauss k hθ p).2.ne]

end UnforcedLeray.Heat
