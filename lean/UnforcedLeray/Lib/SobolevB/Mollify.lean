import UnforcedLeray.Lib.Sobolev
import NonUniqueEuler.P.Infra.ConvMinkowski.Minkowski
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# Mollification in `L^p` (INF11 targets S4 and S7, the analytic core)


§5.1 (S4 "mollification", S7 `eLpNorm_sub_mollify_le`). Manuscript uses: mollification in
`L^q` and translation continuity (tex 7550–7576, B0433), smooth approximation of Sobolev
fields (tex 13970–13985, B0892; tex 1238–1243, B0063).

On a finite-dimensional real inner product space `E` with an additive Haar measure `μ`:

* `cv φ f = f ⋆ φ`, `cv φ f x = ∫ φ (x - t) • f t dμ(t)` (a real kernel acting on an
  `F`-valued function), and `moll b μ f = cv (b.normed μ) f` for a bump `b`;
* `eLpNorm_cv_le` (Young's inequality with an `L¹` kernel, from Minkowski's integral
  inequality `NonUniqueEuler.Conv.eLpNorm_integral_le`, vendored at
  `lean/NonUniqueEuler/P/Infra/ConvMinkowski/Minkowski.lean`);
* `eLpNorm_sub_mollify_le` (S7): the mollifier error is at most the translation modulus on
  the support of the bump;
* `tendsto_eLpNorm_translate_sub`: translations are continuous in `L^p`, `p < ∞` (Mathlib's
  `Lp.instContinuousVAddDomAddAct`);
* `tendsto_eLpNorm_moll_sub`: `moll b f → f` in `L^p` as `rOut → 0`;
* `iterDD`, the classical iterated directional derivative of an `F`-valued function, and
  `iterDD_cv`: `∂_{vs}(f ⋆ φ) = f ⋆ ∂_{vs} φ`; `iterDD_cv_of_hasWeakDeriv`: if `g = ∂_{vs} f`
  weakly then `∂_{vs}(f ⋆ φ) = g ⋆ φ` classically.

The derivative computation follows the project's
`lean/UnforcedLeray/Analysis/SobolevEmbedding/Density.lean` (`mollification_derivative`),
here for every word and every carrier.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology ContDiff Convolution

namespace UnforcedLeray.Sob

section Moll

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Convolution of an `F`-valued function with a real kernel: `cv μ φ f = f ⋆ φ`. -/
def cv (μ : Measure E) (φ : E → ℝ) (f : E → F) : E → F :=
  f ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip, μ] φ

theorem cv_apply (φ : E → ℝ) (f : E → F) (x : E) :
    cv μ φ f x = ∫ t, φ (x - t) • f t ∂μ := by
  simp [cv, convolution_def]

theorem cv_apply_swap (φ : E → ℝ) (f : E → F) (x : E) :
    cv μ φ f x = ∫ t, φ t • f (x - t) ∂μ := by
  rw [cv, convolution_eq_swap]
  simp

/-- The mollification `f ⋆ b̃` by the normalized bump `b̃ = b.normed μ`. -/
def moll (b : ContDiffBump (0 : E)) (μ : Measure E) (f : E → F) : E → F :=
  cv μ (b.normed μ) f

theorem moll_apply_swap (b : ContDiffBump (0 : E)) (f : E → F) (x : E) :
    moll b μ f x = ∫ t, b.normed μ t • f (x - t) ∂μ :=
  cv_apply_swap _ _ _

/-! ### Measurability and Young's inequality -/

theorem aestronglyMeasurable_kernel_prod {φ : E → ℝ} (hφ : Continuous φ) {f : E → F}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (Function.uncurry fun x t => φ t • f (x - t)) (μ.prod μ) := by
  have h1 : AEStronglyMeasurable (fun z : E × E => f (z.1 - z.2)) (μ.prod μ) :=
    hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ)
  have h2 : AEStronglyMeasurable (fun z : E × E => φ z.2) (μ.prod μ) :=
    (hφ.comp continuous_snd).aestronglyMeasurable
  exact h2.smul h1

theorem eLpNorm_translate (f : E → F) (hf : AEStronglyMeasurable f μ) (t : E) (p : ℝ≥0∞) :
    eLpNorm (fun x => f (x - t)) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving (f := fun x => x - t) hf (measurePreserving_sub_right μ t)

theorem eLpNorm_translate_add (f : E → F) (hf : AEStronglyMeasurable f μ) (t : E)
    (p : ℝ≥0∞) : eLpNorm (fun x => f (x + t)) p μ = eLpNorm f p μ :=
  eLpNorm_comp_measurePreserving (f := fun x => x + t) hf (measurePreserving_add_right μ t)

/-- **Young's inequality with an `L¹` kernel** (via Minkowski's integral inequality). -/
theorem eLpNorm_cv_le {φ : E → ℝ} (hφ : Continuous φ) {f : E → F}
    (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (cv μ φ f) p μ ≤ (∫⁻ t, ‖φ t‖ₑ ∂μ) * eLpNorm f p μ := by
  have e : cv μ φ f = fun x => ∫ t, φ t • f (x - t) ∂μ := funext fun x => cv_apply_swap _ _ _
  rw [e]
  refine (NonUniqueEuler.Conv.eLpNorm_integral_le
    (aestronglyMeasurable_kernel_prod hφ hf) hp hp').trans ?_
  have e2 : ∀ t, eLpNorm (fun x => φ t • f (x - t)) p μ = ‖φ t‖ₑ * eLpNorm f p μ := by
    intro t
    rw [show (fun x => φ t • f (x - t)) = φ t • (fun x => f (x - t)) from rfl,
      eLpNorm_const_smul, eLpNorm_translate f hf]
  simp_rw [e2]
  rw [lintegral_mul_const _ hφ.measurable.enorm]


theorem lintegral_enorm_normed (b : ContDiffBump (0 : E)) :
    ∫⁻ t, ‖b.normed μ t‖ₑ ∂μ = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal (b.integrable_normed (μ := μ))
    (Eventually.of_forall fun t => b.nonneg_normed t)
  rw [b.integral_normed, ENNReal.ofReal_one] at h
  rw [h]
  refine lintegral_congr fun t => ?_
  rw [Real.enorm_eq_ofReal (b.nonneg_normed t)]

/-- Mollification does not increase `L^p` norms. -/
theorem eLpNorm_moll_le (b : ContDiffBump (0 : E)) {f : E → F}
    (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (moll b μ f) p μ ≤ eLpNorm f p μ := by
  have := eLpNorm_cv_le (μ := μ) (b.continuous_normed (μ := μ)) hf hp hp'
  rwa [lintegral_enorm_normed, one_mul] at this

theorem memLp_moll (b : ContDiffBump (0 : E)) {f : E → F} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ⊤) (hf : MemLp f p μ) (hm : AEStronglyMeasurable (moll b μ f) μ) :
    MemLp (moll b μ f) p μ :=
  ⟨hm, (eLpNorm_moll_le b hf.1 hp hp').trans_lt hf.2⟩

/-! ### Smoothness -/

theorem contDiff_cv {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {f : E → F}
    (hf : LocallyIntegrable f μ) : ContDiff ℝ ∞ (cv μ φ f) :=
  hc.contDiff_convolution_right (n := ⊤) _ hf hφ

theorem contDiff_moll (b : ContDiffBump (0 : E)) {f : E → F} (hf : LocallyIntegrable f μ) :
    ContDiff ℝ ∞ (moll b μ f) :=
  contDiff_cv (b.contDiff_normed (μ := μ)) (b.hasCompactSupport_normed (μ := μ)) hf

theorem integrable_kernel_swap {φ : E → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {f : E → F} (hf : LocallyIntegrable f μ) (x : E) :
    Integrable (fun t => φ t • f (x - t)) μ := by
  have := (hc.convolutionExists_right
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip hf hφ x).integrable_swap
  simpa using this

/-! ### The mollifier error (S7) -/

/-- **Mollifier error** (S7, `eLpNorm_sub_mollify_le`): if every translate `f(· + h) - f` with
`‖h‖ ≤ rOut` has `L^p` norm at most `η`, then `‖f - b̃ ⋆ f‖_p ≤ η`. -/
theorem eLpNorm_sub_mollify_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) {f : E → F}
    (hf : LocallyIntegrable f μ) (b : ContDiffBump (0 : E)) {η : ℝ≥0∞}
    (hη : ∀ h : E, ‖h‖ ≤ b.rOut → eLpNorm (fun y => f (y + h) - f y) p μ ≤ η) :
    eLpNorm (f - moll b μ f) p μ ≤ η := by
  have hrepr : ∀ x, moll b μ f x - f x = ∫ t, b.normed μ t • (f (x - t) - f x) ∂μ := by
    intro x
    rw [moll_apply_swap]
    have h1 := integrable_kernel_swap (b.continuous_normed (μ := μ))
      (b.hasCompactSupport_normed (μ := μ)) hf x
    have h2 : Integrable (fun t => b.normed μ t • f x) μ :=
      (b.integrable_normed (μ := μ)).smul_const _
    simp_rw [smul_sub]
    rw [integral_sub h1 h2, integral_smul_const, b.integral_normed (μ := μ), one_smul]
  have e : f - moll b μ f = -fun x => ∫ t, b.normed μ t • (f (x - t) - f x) ∂μ := by
    funext x
    rw [Pi.sub_apply, Pi.neg_apply, ← hrepr, neg_sub]
  rw [e, eLpNorm_neg]
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x t => b.normed μ t • (f (x - t) - f x)) (μ.prod μ) := by
    have h1 := aestronglyMeasurable_kernel_prod (μ := μ) (b.continuous_normed (μ := μ))
      hf.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z : E × E => b.normed μ z.2 • f z.1) (μ.prod μ) :=
      (b.continuous_normed.comp continuous_snd).aestronglyMeasurable.smul
        hf.aestronglyMeasurable.comp_fst
    refine (h1.sub h2).congr (Eventually.of_forall fun z => ?_)
    simp [Function.uncurry, smul_sub]
  refine (NonUniqueEuler.Conv.eLpNorm_integral_le hmeas hp hp').trans ?_
  calc ∫⁻ t, eLpNorm (fun x => b.normed μ t • (f (x - t) - f x)) p μ ∂μ
      ≤ ∫⁻ t, ‖b.normed μ t‖ₑ * η ∂μ := by
        refine lintegral_mono fun t => ?_
        rw [show (fun x => b.normed μ t • (f (x - t) - f x)) =
            b.normed μ t • (fun x => f (x - t) - f x) from rfl, eLpNorm_const_smul]
        by_cases ht : t ∈ ball (0 : E) b.rOut
        · refine mul_le_mul_right ?_ _
          have := hη (-t) (by rw [norm_neg]; exact (mem_ball_zero_iff.mp ht).le)
          simpa only [sub_eq_add_neg] using this
        · have h0 : b.normed μ t = 0 := by
            rw [← Function.notMem_support, b.support_normed_eq (μ := μ)]; exact ht
          simp [h0]
    _ = η := by rw [lintegral_mul_const _ (b.continuous_normed (μ := μ)).measurable.enorm,
          lintegral_enorm_normed, one_mul]

/-! ### Continuity of translations in `L^p` -/

/-- **Translations are continuous in `L^p`**, `1 ≤ p < ∞`. -/
theorem tendsto_eLpNorm_translate_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {f : E → F}
    (hf : MemLp f p μ) :
    Tendsto (fun h : E => eLpNorm (fun y => f (y + h) - f y) p μ) (𝓝 0) (𝓝 0) := by
  haveI : Fact (p ≠ ⊤) := ⟨hp⟩
  set v : Lp F p μ := hf.toLp f
  have hc : Continuous fun h : E => (DomAddAct.mk h +ᵥ v : Lp F p μ) - v :=
    (continuous_vadd.comp (DomAddAct.continuous_mk.prodMk continuous_const)).sub
      continuous_const
  have h0 : (DomAddAct.mk (0 : E) +ᵥ v : Lp F p μ) - v = 0 := by
    rw [DomAddAct.mk_zero, zero_vadd, sub_self]
  have hlim := hc.tendsto 0
  rw [h0] at hlim
  have hlim' := (ENNReal.continuous_coe.tendsto _).comp
    ((continuous_nnnorm.tendsto (0 : Lp F p μ)).comp hlim)
  simp only [nnnorm_zero, ENNReal.coe_zero] at hlim'
  refine hlim'.congr fun h => ?_
  simp only [Function.comp_apply]
  rw [← enorm_eq_nnnorm, Lp.enorm_def]
  refine eLpNorm_congr_ae ?_
  have hq : ∀ᵐ y ∂μ, v (h + y) = f (h + y) :=
    (measurePreserving_add_left μ h).quasiMeasurePreserving.ae hf.coeFn_toLp
  filter_upwards [Lp.coeFn_sub (DomAddAct.mk h +ᵥ v) v, DomAddAct.vadd_Lp_ae_eq
    (DomAddAct.mk h) v, hf.coeFn_toLp, hq] with y h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3]
  simp only [Equiv.symm_apply_apply, vadd_eq_add]
  rw [h4, add_comm]

/-- **Mollifiers converge in `L^p`**, `1 ≤ p < ∞`, as the bump radius tends to `0`. -/
theorem tendsto_eLpNorm_moll_sub {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {f : E → F}
    (hf : MemLp f p μ) {ι : Type*} {l : Filter ι} {b : ι → ContDiffBump (0 : E)}
    (hb : Tendsto (fun i => (b i).rOut) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f - moll (b i) μ f) p μ) l (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hloc : LocallyIntegrable f μ := hf.locallyIntegrable hp1
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have ht := tendsto_eLpNorm_translate_sub hp hf
  rw [ENNReal.tendsto_nhds_zero] at ht
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (ht ε hε)
  have hev : ∀ᶠ i in l, (b i).rOut < δ := hb.eventually (gt_mem_nhds hδ)
  filter_upwards [hev] with i hi
  refine eLpNorm_sub_mollify_le hp1 hp hloc (b i) fun h hh => ?_
  exact hball (mem_ball_zero_iff.mpr (hh.trans_lt hi))

/-! ### Supports -/

theorem cv_congr_ae (φ : E → ℝ) {f f' : E → F} (h : f =ᵐ[μ] f') : cv μ φ f = cv μ φ f' := by
  rw [cv, cv, convolution_congr _ h (EventuallyEq.refl _ φ)]

/-- If `f` vanishes a.e. outside a compact set, `f ⋆ φ` has compact support. -/
theorem hasCompactSupport_cv {φ : E → ℝ} (hc : HasCompactSupport φ) {f : E → F} {K : Set E}
    (hK : IsCompact K) (hfK : ∀ᵐ x ∂μ, x ∉ K → f x = 0) : HasCompactSupport (cv μ φ f) := by
  have he : f =ᵐ[μ] K.indicator f := by
    filter_upwards [hfK] with x hx
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK]
    · rw [Set.indicator_of_notMem hxK, hx hxK]
  rw [cv_congr_ae φ he]
  refine HasCompactSupport.intro (hK.add hc) fun x hx => ?_
  by_contra hne
  have hs := support_convolution_subset
    (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip) (μ := μ)
    (f := K.indicator f) (g := φ) (Function.mem_support.mpr hne)
  exact hx (Set.add_subset_add (Set.support_indicator_subset) (subset_tsupport φ) hs)

/-! ### Derivatives -/

section Deriv

/-- The classical iterated directional derivative `∂_{v₁} ⋯ ∂_{vₘ} u` of an `F`-valued
function (the `F`-valued analogue of `iterDirDeriv`). -/
def iterDD (vs : List E) (u : E → F) : E → F :=
  vs.foldr (fun v ψ x => fderiv ℝ ψ x v) u

@[simp] theorem iterDD_nil (u : E → F) : iterDD [] u = u := rfl

@[simp] theorem iterDD_cons (v : E) (vs : List E) (u : E → F) :
    iterDD (v :: vs) u = fun x => fderiv ℝ (iterDD vs u) x v := rfl

theorem hasCompactSupport_iterDirDeriv {φ : E → ℝ} (hc : HasCompactSupport φ) (vs : List E) :
    HasCompactSupport (iterDirDeriv vs φ) := by
  induction vs with
  | nil => simpa using hc
  | cons v vs ih => exact ih.fderiv_apply ℝ v

theorem fderiv_cv_apply {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {f : E → F} (hf : LocallyIntegrable f μ) (x v : E) :
    fderiv ℝ (cv μ φ f) x v = cv μ (fun y => fderiv ℝ φ y v) f x := by
  have hd := hc.hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip hf (hφ.of_le (by simp)) x
  rw [cv, hd.fderiv, convolution_precompR_apply _ hf (hc.fderiv ℝ)
    (hφ.continuous_fderiv (by simp)) x v]
  rfl

/-- `∂_{vs}(f ⋆ φ) = f ⋆ ∂_{vs} φ` for a smooth compactly supported kernel. -/
theorem iterDD_cv {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {f : E → F}
    (hf : LocallyIntegrable f μ) (vs : List E) :
    iterDD vs (cv μ φ f) = cv μ (iterDirDeriv vs φ) f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    simp only [iterDD_cons, ih, iterDirDeriv_cons]
    exact fderiv_cv_apply (contDiff_iterDirDeriv hφ vs) (hasCompactSupport_iterDirDeriv hc vs)
      hf x v

theorem iterDirDeriv_reflect {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E) (vs : List E) :
    iterDirDeriv vs (fun t => φ (x - t)) =
      fun t => (-1 : ℝ) ^ vs.length * iterDirDeriv vs φ (x - t) := by
  induction vs with
  | nil => funext t; simp
  | cons v vs ih =>
    funext t
    simp only [iterDirDeriv_cons, ih, List.length_cons]
    have hψ : Differentiable ℝ (iterDirDeriv vs φ) :=
      (contDiff_iterDirDeriv hφ vs).differentiable (by simp)
    have hd : HasFDerivAt (fun t => (-1 : ℝ) ^ vs.length * iterDirDeriv vs φ (x - t))
        ((-1 : ℝ) ^ vs.length • (fderiv ℝ (iterDirDeriv vs φ) (x - t)).comp
          (-ContinuousLinearMap.id ℝ E)) t := by
      have h1 : HasFDerivAt (fun t : E => x - t) (-ContinuousLinearMap.id ℝ E) t := by
        exact (hasFDerivAt_id (𝕜 := ℝ) t).const_sub x
      exact ((hψ (x - t)).hasFDerivAt.comp t h1).const_mul _
    rw [hd.fderiv]
    simp [pow_succ]

/-- **Mollification turns weak derivatives into classical ones**: if `g = ∂_{vs} f` weakly
(locally integrable `f, g`), then `∂_{vs}(f ⋆ φ) = g ⋆ φ` classically. -/
theorem iterDD_cv_of_hasWeakDeriv {n : ℕ} {dir : Fin n → E} {vs : List E} {f g : E → F}
    (hw : HasWeakDeriv (wholeSpaceOf E μ dir) vs f g) {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hf : LocallyIntegrable f μ) :
    iterDD vs (cv μ φ f) = cv μ φ g := by
  rw [iterDD_cv hφ hc hf]
  funext x
  rw [cv_apply, cv_apply]
  have hψ : (wholeSpaceOf E μ dir).Adm (fun t => φ (x - t)) :=
    ⟨hφ.comp (contDiff_const.sub contDiff_id), hc.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hid := hw.identity _ hψ
  rw [iterDirDeriv_reflect hφ x vs] at hid
  simp only [wholeSpaceOf_μ, mul_smul] at hid
  rw [integral_smul] at hid
  exact smul_right_injective F (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)) hid

end Deriv

end Moll

end UnforcedLeray.Sob
