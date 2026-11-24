import UnforcedLeray.Lib.Sobolev
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The weight package (INF11 target S13)


target S13 ("weights and negative dual spaces"), block 2E of `scoping/README.md` §5.

The periodic cylinder weight `ρ_ℓ` and its derivative bounds are in `Lib/Cylinder` (CY02,
`norm_iteratedFDeriv_rpow_ρw_le`) and are not repeated here.  This file supplies the
whole-space part, for an arbitrary test domain `D` whenever possible:

* `wCS`: the weighted Cauchy–Schwarz inequality
  `∫ |f||g| dμ ≤ ‖f‖_{L²(ρ dμ)} ‖g‖_{L²(ρ⁻¹ dμ)}` (the unweighted pairing of `X_m` and `X_{-m}`,
  B0579 tex 9370–9387, B0656 tex 13869–13890);
* `jw M`: the weight `⟨y⟩^{2M} = (1 + ‖y‖²)^M` (B0008, tex 653–660);
  `eLpNorm_one_le_jw`: `‖f‖_{L¹} ≤ C_M ‖f‖_{L²(⟨y⟩^{2M})}` for `2M > dim` (B0008, B0059 tex
  1206–1213, B0658 tex 13917–13925); `toL1`, `meanL`, `meanZero`, `isClosed_meanZero`,
  `W.meanZero`: the mean-zero subspace `X_{j,M} = {∫ f = 0}` is closed (B0008, B0085);
* `one_add_rpow_le_exp`, `jw_le_gaussInv`: the Gaussian weight dominates every polynomial
  weight, so `X_G ↪ L²(⟨y⟩^{2m})` (B0354, tex 6661–6668; B0082, tex 1388);
* `wμ_le_smul`, `eLpNorm_wμ_le`, `lpWeightLE`, `W.weightLE`: comparable weights give
  continuous inclusions, at the level of `L^p` and of `W` (B0082, B0354, B0989);
* `Hneg`, `pairL`: the negative space `H^{-k}_ρ := (H^k_{ρ⁻¹})^*` with the unweighted pairing,
  and the bounded conjugate-linear map `L²(ρ) → H^{-k}_ρ` (B0579, B0656, B0908, B0946).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Module
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.Sob

/-! ### Weighted Cauchy–Schwarz -/

section CS

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

/-- The weight `ρ⁻¹`. -/
abbrev Weight.inv (ρ : Weight E) : Weight E := ρ ^ (-1 : ℝ)

theorem Weight.inv_apply (ρ : Weight E) (x : E) : ρ.inv x = (ρ x)⁻¹ := by
  simp [Weight.inv, Real.rpow_neg_one]

/-- `‖f‖_{L²(ρ dμ)} = (∫ ρ |f|²)^{1/2}` in `lintegral` form. -/
theorem eLpNorm_two_wμ {F : Type*} [NormedAddCommGroup F] (μ : Measure E) (ρ : Weight E)
    (f : E → F) :
    eLpNorm f 2 (wμ μ ρ) = (∫⁻ x, ENNReal.ofReal (ρ x) * ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  rw [wμ, lintegral_withDensity_eq_lintegral_mul_non_measurable₀]
  · rfl
  · exact (measurable_ofReal_weight ρ).aemeasurable
  · exact Eventually.of_forall fun x => ENNReal.ofReal_lt_top

/-- **Weighted Cauchy–Schwarz** (B0579 tex 9370–9387, B0656 tex 13869–13890):
`∫ |f| |g| dμ ≤ ‖f‖_{L²(ρ dμ)} ‖g‖_{L²(ρ⁻¹ dμ)}`. -/
theorem wCS {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G] (μ : Measure E)
    (ρ : Weight E) {f : E → F} {g : E → G} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ ≤ eLpNorm f 2 (wμ μ ρ) * eLpNorm g 2 (wμ μ ρ.inv) := by
  set a : E → ℝ≥0∞ := fun x => ‖f x‖ₑ * ENNReal.ofReal (ρ x ^ (1 / 2 : ℝ))
  set b : E → ℝ≥0∞ := fun x => ‖g x‖ₑ * ENNReal.ofReal (ρ x ^ (-(1 / 2) : ℝ))
  have hab : ∀ x, ‖f x‖ₑ * ‖g x‖ₑ = a x * b x := by
    intro x
    have h1 : ENNReal.ofReal (ρ x ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ρ x ^ (-(1 / 2) : ℝ)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (ρ.pos x).le _), ← Real.rpow_add (ρ.pos x)]
      simp
    calc ‖f x‖ₑ * ‖g x‖ₑ = ‖f x‖ₑ * ‖g x‖ₑ *
          (ENNReal.ofReal (ρ x ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ρ x ^ (-(1 / 2) : ℝ))) := by
          rw [h1, mul_one]
      _ = a x * b x := by simp only [a, b]; ring
  have hρm : Measurable fun x => ρ x := ρ.measurable
  have ha : AEMeasurable a μ := hf.enorm.mul (hρm.pow_const _).ennreal_ofReal.aemeasurable
  have hb : AEMeasurable b μ := hg.enorm.mul (hρm.pow_const _).ennreal_ofReal.aemeasurable
  have hpq : Real.HolderConjugate 2 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq ha hb
  simp_rw [hab]
  refine hH.trans (le_of_eq ?_)
  rw [eLpNorm_two_wμ, eLpNorm_two_wμ]
  congr 2
  · refine lintegral_congr fun x => ?_
    simp only [a]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (ρ.pos x).le _) (by norm_num),
      ← Real.rpow_mul (ρ.pos x).le]
    norm_num
    ring
  · refine lintegral_congr fun x => ?_
    simp only [b, Weight.inv_apply]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (ρ.pos x).le _) (by norm_num),
      ← Real.rpow_mul (ρ.pos x).le]
    norm_num
    rw [Real.rpow_neg_one]
    ring

end CS

/-! ### The weight `⟨y⟩^{2M}` and the `L¹` embedding -/

section Bracket

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

theorem continuous_one_add_sq_rpow (M : ℝ) :
    Continuous fun y : E => (1 + ‖y‖ ^ 2) ^ M :=
  (continuous_const.add (continuous_norm.pow 2)).rpow_const fun y =>
    Or.inl (by positivity : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0)

/-- **The weight** `⟨y⟩^{2M} = (1 + ‖y‖²)^M` (B0008, tex 653–660). -/
def jw (M : ℝ) : Weight E :=
  Weight.ofContinuous (fun y => (1 + ‖y‖ ^ 2) ^ M) (continuous_one_add_sq_rpow M)
    (fun _ => by positivity)

@[simp] theorem jw_apply (M : ℝ) (y : E) : jw M y = (1 + ‖y‖ ^ 2) ^ M := rfl

theorem jw_inv_apply (M : ℝ) (y : E) : (jw M).inv y = (1 + ‖y‖ ^ 2) ^ (-M) := by
  rw [Weight.inv_apply, jw_apply, Real.rpow_neg (by positivity)]

/-- The constant `C_M = (∫ ⟨y⟩^{-2M} dμ)^{1/2}` of the `L¹` embedding. -/
def bracketConst (μ : Measure E) (M : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun _ : E => (1 : ℝ)) 2 (wμ μ (jw M).inv)

theorem bracketConst_ne_top [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {M : ℝ} (hM : (finrank ℝ E : ℝ) < 2 * M) : bracketConst μ M ≠ ⊤ := by
  rw [bracketConst, eLpNorm_two_wμ]
  refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
  have hint : Integrable (fun y : E => (1 + ‖y‖ ^ 2) ^ (-(2 * M) / 2)) μ :=
    integrable_rpow_neg_one_add_norm_sq hM
  have h2 : (-(2 * M) / 2) = -M := by ring
  rw [h2] at hint
  have := hint.hasFiniteIntegral
  rw [HasFiniteIntegral] at this
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) this)
  refine lintegral_congr fun y => ?_
  simp only [jw_inv_apply, enorm_one, ENNReal.one_rpow, mul_one]
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (by positivity) _)]

/-- **`L¹` embedding** (B0008, tex 653–660; B0059, tex 1206–1213; B0658, tex 13917–13925):
`‖f‖_{L¹(μ)} ≤ C_M ‖f‖_{L²(⟨y⟩^{2M} dμ)}`; `C_M < ∞` when `2M > dim E`
(`bracketConst_ne_top`). -/
theorem eLpNorm_one_le_jw {F : Type*} [NormedAddCommGroup F] (μ : Measure E) (M : ℝ)
    {f : E → F} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 1 μ ≤ eLpNorm f 2 (wμ μ (jw M)) * bracketConst μ M := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have := wCS μ (jw M) hf (aestronglyMeasurable_const (b := (1 : ℝ)))
  simpa [bracketConst] using this

theorem memLp_one_of_jw {F : Type*} [NormedAddCommGroup F] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {M : ℝ} (hM : (finrank ℝ E : ℝ) < 2 * M) {f : E → F}
    (hf : MemLp f 2 (wμ μ (jw M))) : MemLp f 1 μ := by
  have hm : AEStronglyMeasurable f μ := hf.1.mono_ac (ac_wμ μ (jw M))
  refine ⟨hm, lt_of_le_of_lt (eLpNorm_one_le_jw μ M hm) ?_⟩
  exact ENNReal.mul_lt_top hf.2 (bracketConst_ne_top μ hM).lt_top

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] {M : ℝ}

/-- The inclusion `L²(⟨y⟩^{2M} dμ) → L¹(μ)` for `2M > dim E`, a bounded `𝕜`-linear map. -/
def toL1 (hM : (finrank ℝ E : ℝ) < 2 * M) : Lp F 2 (wμ μ (jw M)) →L[𝕜] Lp F 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_one_of_jw μ hM (Lp.memLp f)).toLp f
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_one_of_jw μ hM (Lp.memLp (f + g))).coeFn_toLp,
          (memLp_one_of_jw μ hM (Lp.memLp f)).coeFn_toLp,
          (memLp_one_of_jw μ hM (Lp.memLp g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_one_of_jw μ hM (Lp.memLp f)).toLp f)
            ((memLp_one_of_jw μ hM (Lp.memLp g)).toLp g),
          (ae_eq_wμ_iff μ (jw M)).mp (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
        rw [h1, h4, h5, Pi.add_apply, Pi.add_apply, h2, h3]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(memLp_one_of_jw μ hM (Lp.memLp (c • f))).coeFn_toLp,
          (memLp_one_of_jw μ hM (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_one_of_jw μ hM (Lp.memLp f)).toLp f),
          (ae_eq_wμ_iff μ (jw M)).mp (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h2] }
    (bracketConst μ M).toReal fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (memLp_one_of_jw μ hM (Lp.memLp f)).coeFn_toLp,
        mul_comm, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
        (bracketConst_ne_top μ hM))
        (eLpNorm_one_le_jw μ M ((Lp.aestronglyMeasurable f).mono_ac (ac_wμ μ (jw M))))

theorem coeFn_toL1 (hM : (finrank ℝ E : ℝ) < 2 * M) (f : Lp F 2 (wμ μ (jw M))) :
    (toL1 (𝕜 := 𝕜) μ hM f : E → F) =ᵐ[μ] f :=
  (memLp_one_of_jw μ hM (Lp.memLp f)).coeFn_toLp

variable [NormedSpace ℝ F] [CompleteSpace F] [SMulCommClass ℝ 𝕜 F]

/-- **The mean** `f ↦ ∫ f dμ` on `L²(⟨y⟩^{2M} dμ)`, `2M > dim E` (B0008, tex 653–660). -/
def meanL (hM : (finrank ℝ E : ℝ) < 2 * M) : Lp F 2 (wμ μ (jw M)) →L[𝕜] F :=
  (L1.integralCLM' (μ := μ) 𝕜).comp (toL1 μ hM)

theorem meanL_apply (hM : (finrank ℝ E : ℝ) < 2 * M) (f : Lp F 2 (wμ μ (jw M))) :
    meanL (𝕜 := 𝕜) μ hM f = ∫ x, f x ∂μ := by
  rw [meanL, ContinuousLinearMap.comp_apply, ← L1.integral_eq' 𝕜, L1.integral_eq_integral]
  exact integral_congr_ae (coeFn_toL1 μ hM f)

/-- **The mean-zero subspace** `{f ∈ L²(⟨y⟩^{2M}) | ∫ f = 0}` (B0008, tex 653–660). -/
def meanZero (hM : (finrank ℝ E : ℝ) < 2 * M) : Submodule 𝕜 (Lp F 2 (wμ μ (jw M))) :=
  LinearMap.ker (meanL (𝕜 := 𝕜) (F := F) μ hM : Lp F 2 (wμ μ (jw M)) →ₗ[𝕜] F)

theorem mem_meanZero (hM : (finrank ℝ E : ℝ) < 2 * M) (f : Lp F 2 (wμ μ (jw M))) :
    f ∈ meanZero (𝕜 := 𝕜) μ hM ↔ ∫ x, f x ∂μ = 0 := by
  rw [meanZero, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, meanL_apply]

/-- `X_{0,M}` is closed (B0008: "closed because `‖f‖₁ ≤ C_M ‖⟨y⟩^M f‖₂` for `M > 1`"). -/
theorem isClosed_meanZero (hM : (finrank ℝ E : ℝ) < 2 * M) :
    IsClosed (meanZero (𝕜 := 𝕜) (F := F) μ hM : Set (Lp F 2 (wμ μ (jw M)))) :=
  (meanL (𝕜 := 𝕜) (F := F) μ hM).isClosed_ker

end Bracket


/-! ### Polynomial weights against the Gaussian weight -/

section Gauss

/-- `(1 + s)^m ≤ (max 1 (4m))^m e^{s/4}` for `s ≥ 0` (B0354, tex 6661–6668: "the Gaussian
weight dominates every polynomial"). -/
theorem one_add_rpow_le_exp (m : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (1 + s) ^ m ≤ max 1 (4 * m) ^ m * Real.exp (s / 4) := by
  rcases le_or_gt m 0 with hm | hm
  · have h1 : max 1 (4 * m) = 1 := max_eq_left (by linarith)
    rw [h1, Real.one_rpow, one_mul]
    exact (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hm).trans
      (Real.one_le_exp (by positivity))
  · have hm4 : 0 < 4 * m := by linarith
    have h1 : 1 + s ≤ max 1 (4 * m) * (1 + s / (4 * m)) := by
      rcases le_total 1 (4 * m) with h | h
      · rw [max_eq_right h, mul_add, mul_one, mul_div_cancel₀ _ hm4.ne']
        linarith
      · rw [max_eq_left h, one_mul]
        have : s ≤ s / (4 * m) := by
          rw [le_div_iff₀ hm4]
          nlinarith
        linarith
    have h2 : 1 + s / (4 * m) ≤ Real.exp (s / (4 * m)) := by
      have := Real.add_one_le_exp (s / (4 * m))
      linarith
    have hmax : 0 ≤ max 1 (4 * m) := le_trans zero_le_one (le_max_left _ _)
    calc (1 + s) ^ m ≤ (max 1 (4 * m) * (1 + s / (4 * m))) ^ m :=
          Real.rpow_le_rpow (by positivity) h1 hm.le
      _ = max 1 (4 * m) ^ m * (1 + s / (4 * m)) ^ m :=
          Real.mul_rpow hmax (by positivity)
      _ ≤ max 1 (4 * m) ^ m * Real.exp (s / (4 * m)) ^ m := by
          gcongr
      _ = max 1 (4 * m) ^ m * Real.exp (s / 4) := by
          rw [← Real.exp_mul, div_mul_eq_mul_div, mul_div_mul_right _ _ hm.ne']

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- The inverse Gaussian weight `G⁻¹ = 4π e^{‖y‖²/4}` of `X_G` (planar normalization
`G = (4π)⁻¹ e^{-|y|²/4}`, tex 1388, B0082). -/
def gaussInv : Weight E :=
  Weight.ofContinuous (fun y => 4 * Real.pi * Real.exp (‖y‖ ^ 2 / 4))
    (continuous_const.mul (Real.continuous_exp.comp ((continuous_norm.pow 2).div_const 4)))
    (fun _ => by positivity)

@[simp] theorem gaussInv_apply (y : E) : (gaussInv : Weight E) y =
    4 * Real.pi * Real.exp (‖y‖ ^ 2 / 4) := rfl

/-- **`⟨y⟩^{2m} ≤ C_m G⁻¹`** (B0354, tex 6661–6668). -/
theorem jw_le_gaussInv (m : ℝ) (y : E) :
    jw m y ≤ (max 1 (4 * m) ^ m / (4 * Real.pi)) * (gaussInv : Weight E) y := by
  rw [jw_apply, gaussInv_apply]
  have h := one_add_rpow_le_exp m (sq_nonneg ‖y‖)
  have hπ : 0 < 4 * Real.pi := by positivity
  calc (1 + ‖y‖ ^ 2) ^ m ≤ max 1 (4 * m) ^ m * Real.exp (‖y‖ ^ 2 / 4) := h
    _ = max 1 (4 * m) ^ m / (4 * Real.pi) * (4 * Real.pi * Real.exp (‖y‖ ^ 2 / 4)) := by
      field_simp

end Gauss

/-! ### Comparable weights -/

section Compare

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

theorem nonneg_of_weight_le {ρ σ : Weight E} {c : ℝ} (h : ∀ x, ρ x ≤ c * σ x) (x : E) :
    0 ≤ c := by
  have h1 := h x
  have h2 := ρ.pos x
  have h3 := σ.pos x
  by_contra hc
  have hc' : c < 0 := lt_of_not_ge hc
  nlinarith

/-- `ρ ≤ c σ` pointwise gives `ρ dμ ≤ c σ dμ`. -/
theorem wμ_le_smul (μ : Measure E) {ρ σ : Weight E} {c : ℝ} (h : ∀ x, ρ x ≤ c * σ x) :
    wμ μ ρ ≤ ENNReal.ofReal c • wμ μ σ := by
  rw [wμ, wμ, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  refine withDensity_mono (Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (nonneg_of_weight_le h x)]
  exact ENNReal.ofReal_le_ofReal (h x)

/-- **Weight comparison** (B0082 tex 1388, B0354 tex 6661–6668):
`‖f‖_{L^p(ρ dμ)} ≤ c^{1/p} ‖f‖_{L^p(σ dμ)}` when `ρ ≤ c σ`. -/
theorem eLpNorm_wμ_le {F : Type*} [NormedAddCommGroup F] (μ : Measure E) {ρ σ : Weight E}
    {c : ℝ} (h : ∀ x, ρ x ≤ c * σ x) (f : E → F) (p : ℝ≥0∞) :
    eLpNorm f p (wμ μ ρ) ≤ ENNReal.ofReal c ^ (1 / p).toReal * eLpNorm f p (wμ μ σ) :=
  eLpNorm_le_of_measure_le_smul (wμ_le_smul μ h)

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (μ : Measure E) {ρ σ : Weight E} {c : ℝ}

theorem memLp_wμ_of_le (h : ∀ x, ρ x ≤ c * σ x) {f : E → F} (hf : MemLp f p (wμ μ σ)) :
    MemLp f p (wμ μ ρ) :=
  hf.of_measure_le_smul ENNReal.ofReal_ne_top (wμ_le_smul μ h)

/-- **The inclusion** `L^p(σ dμ) → L^p(ρ dμ)` for `ρ ≤ c σ`, `𝕜`-linear and bounded
(adapted from Mathlib `Lp.LpToLpOfMeasureLeSMul`, which is only `ℝ`-linear). -/
def lpWeightLE (h : ∀ x, ρ x ≤ c * σ x) : Lp F p (wμ μ σ) →L[𝕜] Lp F p (wμ μ ρ) :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_wμ_of_le μ h (Lp.memLp f)).toLp f
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_wμ_of_le μ h (Lp.memLp (f + g))).coeFn_toLp,
          (memLp_wμ_of_le μ h (Lp.memLp f)).coeFn_toLp,
          (memLp_wμ_of_le μ h (Lp.memLp g)).coeFn_toLp,
          Lp.coeFn_add ((memLp_wμ_of_le μ h (Lp.memLp f)).toLp f)
            ((memLp_wμ_of_le μ h (Lp.memLp g)).toLp g),
          (ae_eq_wμ_iff μ ρ).mpr ((ae_eq_wμ_iff μ σ).mp (Lp.coeFn_add f g))]
          with x h1 h2 h3 h4 h5
        rw [h1, h4, h5, Pi.add_apply, Pi.add_apply, h2, h3]
      map_smul' := fun a f => by
        apply Lp.ext
        filter_upwards [(memLp_wμ_of_le μ h (Lp.memLp (a • f))).coeFn_toLp,
          (memLp_wμ_of_le μ h (Lp.memLp f)).coeFn_toLp,
          Lp.coeFn_smul a ((memLp_wμ_of_le μ h (Lp.memLp f)).toLp f),
          (ae_eq_wμ_iff μ ρ).mpr ((ae_eq_wμ_iff μ σ).mp (Lp.coeFn_smul a f))]
          with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h2] }
    ((ENNReal.ofReal c).toReal ^ (1 / p).toReal) fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (memLp_wμ_of_le μ h (Lp.memLp f)).coeFn_toLp,
        ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
        (Lp.eLpNorm_ne_top f)) (eLpNorm_wμ_le μ h f p)

theorem coeFn_lpWeightLE (h : ∀ x, ρ x ≤ c * σ x) (f : Lp F p (wμ μ σ)) :
    (lpWeightLE (𝕜 := 𝕜) μ h f : E → F) =ᵐ[μ] f :=
  (ae_eq_wμ_iff μ ρ).mp (memLp_wμ_of_le μ h (Lp.memLp f)).coeFn_toLp

end Compare

section WCompare

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {n : ℕ} {D : TestDomain E n} {ρ σ : Weight E} {c : ℝ}
  {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F] {k : ℕ} {p : ℝ≥0∞}
  [Fact (1 ≤ p)]

variable (D 𝕜 F k p) in
/-- The componentwise inclusion of tuples. -/
def tupleWeightLE (h : ∀ x, ρ x ≤ c * σ x) : SobTuple D σ F k p →L[𝕜] SobTuple D ρ F k p :=
  (PiLp.continuousLinearEquiv p 𝕜
      (fun _ : Idx n k => Lp F p (wμ D.μ ρ))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun α => (lpWeightLE (𝕜 := 𝕜) D.μ h).comp
      (PiLp.proj p (fun _ : Idx n k => Lp F p (wμ D.μ σ)) α))

theorem tupleWeightLE_apply (h : ∀ x, ρ x ≤ c * σ x) (x : SobTuple D σ F k p) (α : Idx n k) :
    (tupleWeightLE D 𝕜 F k p h x).ofLp α = lpWeightLE (𝕜 := 𝕜) D.μ h (x.ofLp α) := rfl

theorem mem_SobSub_tupleWeightLE (h : ∀ x, ρ x ≤ c * σ x) (x : W D σ 𝕜 F k p) :
    tupleWeightLE D 𝕜 F k p h (x : SobTuple D σ F k p) ∈ SobSub D ρ 𝕜 F k p := by
  rw [mem_SobSub_iff]
  intro α
  rw [tupleWeightLE_apply, tupleWeightLE_apply]
  exact (W.hasWeakDeriv x α).congr_ae (coeFn_lpWeightLE (𝕜 := 𝕜) D.μ h _).symm
    (coeFn_lpWeightLE (𝕜 := 𝕜) D.μ h _).symm

/-- **Comparable weights embed the Sobolev spaces** (B0082 tex 1388, B0354 tex 6661–6668,
B0989): `W^{k,p}(σ dμ) → W^{k,p}(ρ dμ)` for `ρ ≤ c σ`; the weak derivatives are those of the
unweighted pairing, so they are unchanged. -/
def W.weightLE (h : ∀ x, ρ x ≤ c * σ x) : W D σ 𝕜 F k p →L[𝕜] W D ρ 𝕜 F k p :=
  ((tupleWeightLE D 𝕜 F k p h).comp (SobSub D σ 𝕜 F k p).subtypeL).codRestrict _
    (mem_SobSub_tupleWeightLE h)

theorem W.deriv_weightLE (h : ∀ x, ρ x ≤ c * σ x) (x : W D σ 𝕜 F k p) (α : Idx n k) :
    W.deriv D ρ 𝕜 F k p α (W.weightLE h x) =
      lpWeightLE (𝕜 := 𝕜) D.μ h (W.deriv D σ 𝕜 F k p α x) := rfl

theorem W.coeFn_deriv_weightLE (h : ∀ x, ρ x ≤ c * σ x) (x : W D σ 𝕜 F k p) (α : Idx n k) :
    (W.deriv D ρ 𝕜 F k p α (W.weightLE h x) : E → F) =ᵐ[D.μ] W.deriv D σ 𝕜 F k p α x :=
  coeFn_lpWeightLE (𝕜 := 𝕜) D.μ h _

end WCompare


/-! ### Negative spaces and the unweighted pairing -/

section Neg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {n : ℕ} (D : TestDomain E n) (ρ : Weight E)
  (𝕜 : Type*) [RCLike 𝕜] (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F] (k : ℕ)

/-- **The negative space** `H^{-k}_ρ := (H^k_{ρ⁻¹})^*` (B0579 tex 9370–9387, B0656
tex 13869–13890: `H^{-k}_m := (H^k_{-m})^*` under the unweighted pairing). -/
abbrev Hneg : Type _ := StrongDual 𝕜 (W D ρ.inv 𝕜 F k 2)

variable {D ρ 𝕜 F k}

theorem enorm_inner_le' (x y : F) : ‖inner 𝕜 x y‖ₑ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm x y)

/-- The pairing integrand of `L²(ρ dμ)` and `L²(ρ⁻¹ dμ)` is integrable. -/
theorem integrable_inner_wμ {f g : E → F} (hf : MemLp f 2 (wμ D.μ ρ))
    (hg : MemLp g 2 (wμ D.μ ρ.inv)) : Integrable (fun x => inner 𝕜 (f x) (g x)) D.μ := by
  have hf' : AEStronglyMeasurable f D.μ := hf.1.mono_ac (ac_wμ D.μ ρ)
  have hg' : AEStronglyMeasurable g D.μ := hg.1.mono_ac (ac_wμ D.μ ρ.inv)
  refine ⟨hf'.inner hg', ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ x, ‖inner 𝕜 (f x) (g x)‖ₑ ∂D.μ ≤ ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂D.μ :=
        lintegral_mono fun x => enorm_inner_le' (f x) (g x)
    _ ≤ eLpNorm f 2 (wμ D.μ ρ) * eLpNorm g 2 (wμ D.μ ρ.inv) := wCS D.μ ρ hf' hg'
    _ < ⊤ := ENNReal.mul_lt_top hf.2 hg.2

theorem norm_integral_inner_le {f g : E → F} (hf : MemLp f 2 (wμ D.μ ρ))
    (hg : MemLp g 2 (wμ D.μ ρ.inv)) :
    ‖∫ x, inner 𝕜 (f x) (g x) ∂D.μ‖ ≤
      (eLpNorm f 2 (wμ D.μ ρ)).toReal * (eLpNorm g 2 (wμ D.μ ρ.inv)).toReal := by
  have hf' : AEStronglyMeasurable f D.μ := hf.1.mono_ac (ac_wμ D.μ ρ)
  have hg' : AEStronglyMeasurable g D.μ := hg.1.mono_ac (ac_wμ D.μ ρ.inv)
  refine (norm_integral_le_lintegral_norm _).trans ?_
  rw [← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top hf.2.ne hg.2.ne) ?_
  calc ∫⁻ x, ENNReal.ofReal ‖inner 𝕜 (f x) (g x)‖ ∂D.μ ≤ ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂D.μ :=
        lintegral_mono fun x => by
          rw [ofReal_norm_eq_enorm]; exact enorm_inner_le' (f x) (g x)
    _ ≤ eLpNorm f 2 (wμ D.μ ρ) * eLpNorm g 2 (wμ D.μ ρ.inv) := wCS D.μ ρ hf' hg'

theorem norm_value_le {σ : Weight E} {p : ℝ≥0∞} [Fact (1 ≤ p)] (φ : W D σ 𝕜 F k p) :
    ‖W.value D σ 𝕜 F k p φ‖ ≤ ‖φ‖ := by
  rw [W.value_apply]
  exact PiLp.norm_apply_le (φ : SobTuple D σ F k p) Idx.zero

/-- The functional `φ ↦ ∫ ⟪f, φ⟫ dμ` of `f ∈ L²(ρ dμ)` on `H^k_{ρ⁻¹}`. -/
def pairFun (f : Lp F 2 (wμ D.μ ρ)) : Hneg D ρ 𝕜 F k :=
  LinearMap.mkContinuous
    { toFun := fun φ => ∫ x, inner 𝕜 (f x) ((W.value D ρ.inv 𝕜 F k 2 φ) x) ∂D.μ
      map_add' := fun φ ψ => by
        simp only [map_add]
        rw [← integral_add (integrable_inner_wμ (Lp.memLp f) (Lp.memLp _))
          (integrable_inner_wμ (Lp.memLp f) (Lp.memLp _))]
        refine integral_congr_ae ?_
        filter_upwards [(ae_eq_wμ_iff D.μ ρ.inv).mp
          (Lp.coeFn_add (W.value D ρ.inv 𝕜 F k 2 φ) (W.value D ρ.inv 𝕜 F k 2 ψ))] with x hx
        rw [hx, Pi.add_apply, inner_add_right]
      map_smul' := fun a φ => by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [(ae_eq_wμ_iff D.μ ρ.inv).mp
          (Lp.coeFn_smul a (W.value D ρ.inv 𝕜 F k 2 φ))] with x hx
        rw [hx, Pi.smul_apply, inner_smul_right] }
    ‖f‖ fun φ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine (norm_integral_inner_le (Lp.memLp f) (Lp.memLp _)).trans ?_
      rw [← Lp.norm_def, ← Lp.norm_def]
      exact mul_le_mul_of_nonneg_left (norm_value_le φ) (norm_nonneg _)

theorem pairFun_apply (f : Lp F 2 (wμ D.μ ρ)) (φ : W D ρ.inv 𝕜 F k 2) :
    pairFun f φ = ∫ x, inner 𝕜 (f x) ((W.value D ρ.inv 𝕜 F k 2 φ) x) ∂D.μ := rfl

theorem norm_pairFun_le (f : Lp F 2 (wμ D.μ ρ)) : ‖(pairFun f : Hneg D ρ 𝕜 F k)‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

variable (D ρ 𝕜 F k) in
/-- The pairing map, conjugate-linear in `f`. -/
def pairLₗ : Lp F 2 (wμ D.μ ρ) →ₗ⋆[𝕜] Hneg D ρ 𝕜 F k where
  toFun f := pairFun f
  map_add' f g := by
    refine ContinuousLinearMap.ext fun φ => ?_
    simp only [pairFun_apply, ContinuousLinearMap.add_apply]
    rw [← integral_add (integrable_inner_wμ (Lp.memLp f) (Lp.memLp _))
      (integrable_inner_wμ (Lp.memLp g) (Lp.memLp _))]
    refine integral_congr_ae ?_
    filter_upwards [(ae_eq_wμ_iff D.μ ρ).mp (Lp.coeFn_add f g)] with x hx
    rw [hx, Pi.add_apply, inner_add_left]
  map_smul' a f := by
    refine ContinuousLinearMap.ext fun φ => ?_
    simp only [pairFun_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [(ae_eq_wμ_iff D.μ ρ).mp (Lp.coeFn_smul a f)] with x hx
    rw [hx, Pi.smul_apply, inner_smul_left]

variable (D ρ 𝕜 F k) in
/-- **`X_ρ ↪ H^{-k}_ρ`** through the unweighted pairing `f ↦ ∫ ⟪f, ·⟫ dμ` (B0579 tex 9370–9387,
B0908 tex 14082–14092, B0946): a bounded conjugate-linear map of norm `≤ 1`. -/
def pairL : Lp F 2 (wμ D.μ ρ) →L⋆[𝕜] Hneg D ρ 𝕜 F k where
  toLinearMap := pairLₗ D ρ 𝕜 F k
  cont := AddMonoidHomClass.continuous_of_bound (pairLₗ D ρ 𝕜 F k) 1 fun f => by
    rw [one_mul]
    exact norm_pairFun_le f

theorem pairL_apply (f : Lp F 2 (wμ D.μ ρ)) (φ : W D ρ.inv 𝕜 F k 2) :
    pairL D ρ 𝕜 F k f φ = ∫ x, inner 𝕜 (f x) ((W.value D ρ.inv 𝕜 F k 2 φ) x) ∂D.μ := rfl

theorem norm_pairL_apply_le (f : Lp F 2 (wμ D.μ ρ)) : ‖pairL D ρ 𝕜 F k f‖ ≤ ‖f‖ :=
  norm_pairFun_le f

end Neg

/-! ### The mean-zero subspace of `W` -/

section WMean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {n : ℕ} (D : TestDomain E n) [D.μ.IsAddHaarMeasure]
  {𝕜 : Type*} [RCLike 𝕜] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] [FiniteDimensional 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  (k : ℕ) {M : ℝ}

/-- **The spaces `X_{j,M}`** (B0008, tex 653–660; B0085, tex 691–705): the mean-zero elements of
`H^k(⟨y⟩^{2M})`, `2M > dim E`. -/
def W.meanZero (hM : (finrank ℝ E : ℝ) < 2 * M) : Submodule 𝕜 (W D (jw M) 𝕜 F k 2) :=
  haveI := completeSpace_of_finiteDimensional 𝕜 F
  LinearMap.ker ((meanL (𝕜 := 𝕜) (F := F) D.μ hM).comp (W.value D (jw M) 𝕜 F k 2) :
    W D (jw M) 𝕜 F k 2 →ₗ[𝕜] F)

theorem W.mem_meanZero (hM : (finrank ℝ E : ℝ) < 2 * M) (x : W D (jw M) 𝕜 F k 2) :
    x ∈ W.meanZero D k hM ↔ ∫ y, (W.value D (jw M) 𝕜 F k 2 x) y ∂D.μ = 0 := by
  have := completeSpace_of_finiteDimensional 𝕜 F
  rw [W.meanZero, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, meanL_apply]

theorem W.isClosed_meanZero (hM : (finrank ℝ E : ℝ) < 2 * M) :
    IsClosed (W.meanZero (𝕜 := 𝕜) (F := F) D k hM : Set (W D (jw M) 𝕜 F k 2)) := by
  have := completeSpace_of_finiteDimensional 𝕜 F
  exact ((meanL (𝕜 := 𝕜) (F := F) D.μ hM).comp (W.value D (jw M) 𝕜 F k 2)).isClosed_ker

end WMean

end UnforcedLeray.Sob
