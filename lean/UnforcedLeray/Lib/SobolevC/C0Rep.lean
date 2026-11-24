import UnforcedLeray.Lib.SobolevC.FourierBridge
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# `H^k(ℝⁿ) ⊂ C₀ ∩ L^∞` for `2k > n` (INF11 target S9a, second half)


S9a `W.exists_C0_rep`.  Manuscript uses: B0711 (tex 279–290, `H²(ℝ³)` facts), B0091
(tex 1463–1477, "`H^{m+2}(ℝ²) ⊂ C^m_b`"), B0059 (tex 1206–1213).

## Proof
`𝓕x = ⟨ξ⟩^{-k} · (⟨ξ⟩^k 𝓕x)` is in `L¹` with
`‖𝓕x‖₁ ≤ ‖⟨ξ⟩^{-k}‖₂ ‖⟨ξ⟩^k 𝓕x‖₂ ≤ ‖⟨ξ⟩^{-k}‖₂ 2^{k/2} ‖x‖` (Cauchy–Schwarz and
`W.bessel_sq_le`); `‖⟨ξ⟩^{-k}‖₂ < ∞` iff `n < 2k`.  Then `g = 𝓕⁻¹(𝓕x)` (the inverse Fourier
integral of an `L¹` function) is continuous, tends to `0` at infinity (Riemann–Lebesgue),
is bounded by `‖𝓕x‖₁`, and represents `x`: both define the same tempered distribution
(the Fourier multiplication formula `VectorFourier.integral_fourierIntegral_smul_eq_flip`).

## Main declaration
* `W.exists_C0_rep` (complex scalars).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric SchwartzMap TemperedDistribution
open scoped ENNReal NNReal Topology ContDiff FourierTransform SchwartzMap Real

namespace UnforcedLeray.Sob

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [FiniteDimensional ℂ F] {k : ℕ}

/-- The weight `⟨ξ⟩^{-k} = (1 + |ξ|²)^{-k/2}` as a complex function. -/
def bracketNeg (k : ℕ) (ξ : Eucl n) : ℂ := (((1 + ‖ξ‖ ^ 2) ^ (-(k : ℝ) / 2) : ℝ) : ℂ)

theorem continuous_bracketNeg (k : ℕ) : Continuous (bracketNeg (n := n) k) :=
  Complex.continuous_ofReal.comp ((continuous_const.add (continuous_norm.pow 2)).rpow_const
    fun y => Or.inl (by positivity : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0))

theorem memLp_bracketNeg (hn : n < 2 * k) : MemLp (bracketNeg (n := n) k) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (continuous_bracketNeg k).aestronglyMeasurable).mpr ?_
  have hr : ((Module.finrank ℝ (Eucl n) : ℕ) : ℝ) < ((2 * k : ℕ) : ℝ) := by
    rw [finrank_euclideanSpace_fin]; exact_mod_cast hn
  have hint := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (Eucl n))) hr
  refine hint.congr (Eventually.of_forall fun ξ => ?_)
  simp only [bracketNeg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← Real.rpow_mul_natCast (by positivity)]
  congr 1
  push_cast
  ring

theorem fourierValue_eq_bracketNeg_smul (x : W (wholeSpace n) 1 ℂ F k 2) (ξ : Eucl n) :
    (W.fourierValue x : Eucl n → F) ξ = bracketNeg k ξ • W.besselFn x ξ := by
  rw [W.besselFn, bracketNeg, smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
  rw [show -(k : ℝ) / 2 + (k : ℝ) / 2 = 0 by ring, Real.rpow_zero, Complex.ofReal_one, one_smul]

theorem integrable_fourierValue (hn : n < 2 * k) (x : W (wholeSpace n) 1 ℂ F k 2) :
    Integrable (W.fourierValue x : Eucl n → F) volume := by
  have h := (W.memLp_besselFn x).smul (r := 1) (memLp_bracketNeg (n := n) hn)
  refine (memLp_one_iff_integrable.mp h).congr (Eventually.of_forall fun ξ => ?_)
  rw [Pi.smul_apply', fourierValue_eq_bracketNeg_smul]

/-- `‖𝓕x‖₁ ≤ ‖⟨ξ⟩^{-k}‖₂ ‖⟨ξ⟩^k 𝓕x‖₂`. -/
theorem eLpNorm_one_fourierValue_le (x : W (wholeSpace n) 1 ℂ F k 2) :
    eLpNorm (W.fourierValue x : Eucl n → F) 1 volume ≤
      eLpNorm (bracketNeg (n := n) k) 2 volume * eLpNorm (W.besselFn x) 2 volume := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) (μ := volume)
    (W.memLp_besselFn x).1 (continuous_bracketNeg (n := n) k).aestronglyMeasurable
  refine le_trans (le_of_eq ?_) h
  congr 1
  funext ξ
  rw [Pi.smul_apply', fourierValue_eq_bracketNeg_smul]

theorem toReal_eLpNorm_besselFn_le (x : W (wholeSpace n) 1 ℂ F k 2) :
    (eLpNorm (W.besselFn x) 2 volume).toReal ≤ Real.sqrt (2 ^ k) * ‖x‖ := by
  have h := W.bessel_sq_le x
  have hne : eLpNorm (W.besselFn x) 2 volume ≠ ⊤ := (W.memLp_besselFn x).2.ne
  set b := (eLpNorm (W.besselFn x) 2 volume).toReal with hb
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hsq : b ^ 2 ≤ 2 ^ k * ‖x‖ ^ 2 := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) h
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at this
    simpa [hb] using this
  calc b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb0).symm
    _ ≤ Real.sqrt (2 ^ k * ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (2 ^ k) * ‖x‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The flip identity for the inverse Fourier integral. -/
theorem integral_fourierInv_smul_flip {ψ : Eucl n → ℂ} {G : Eucl n → F} (hψ : Integrable ψ)
    (hG : Integrable G) :
    ∫ ξ, (𝓕⁻ ψ) ξ • G ξ = ∫ y, ψ y • (𝓕⁻ G) y := by
  have hL : Continuous fun p : Eucl n × Eucl n => (-innerₗ (Eucl n)) p.1 p.2 :=
    Continuous.congr (continuous_inner.neg) (fun p => by simp)
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume)
    (ν := volume) (L := -innerₗ (Eucl n)) Real.continuous_fourierChar hL hψ hG
  have hflip : (-innerₗ (Eucl n)).flip = -innerₗ (Eucl n) := by
    ext a b
    simp [real_inner_comm]
  rw [hflip] at h
  exact h

/-- **The inverse Fourier integral represents `x`** when `𝓕x ∈ L¹`. -/
theorem W.toVol_ae_eq_fourierInv (x : W (wholeSpace n) 1 ℂ F k 2)
    (hint : Integrable (W.fourierValue x : Eucl n → F) volume) :
    (toVol (W.value (wholeSpace n) 1 ℂ F k 2 x) : Eucl n → F) =ᵐ[volume]
      𝓕⁻ (W.fourierValue x : Eucl n → F) := by
  set g : Eucl n → F := 𝓕⁻ (W.fourierValue x : Eucl n → F) with hg
  set F₁ : Lp F 1 (volume : Measure (Eucl n)) := (memLp_one_iff_integrable.mpr hint).toLp _
  have hgF₁ : (Real.Lp.fourierTransformInv F₁ : Eucl n → F) = g := by
    rw [Real.Lp.fourierTransformInv_toLp]
  have hcont : Continuous g := hgF₁ ▸ (Real.Lp.fourierTransformInv F₁).continuous
  set V : Lp F 2 (volume : Measure (Eucl n)) := toVol (W.value (wholeSpace n) 1 ℂ F k 2 x)
    with hV
  have hVl : LocallyIntegrable (V : Eucl n → F) volume :=
    (Lp.memLp V).locallyIntegrable (by norm_num)
  have hgl : LocallyIntegrable g volume := hcont.locallyIntegrable
  have hD := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hVl.sub hgl) (fun φ hφ hφc => by
    have hc1 : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
    have hc2 : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
    set ψ : 𝓢(Eucl n, ℂ) := hc1.toSchwartzMap hc2
    have hψ : ∀ ξ, ψ ξ = (φ ξ : ℂ) := fun ξ => rfl
    have e1 : (V : 𝓢'(Eucl n, F)) ψ = ∫ y, ψ y • g y := by
      have hT : (V : 𝓢'(Eucl n, F)) = 𝓕⁻ ((W.fourierValue x : Lp F 2 volume) : 𝓢'(Eucl n, F)) := by
        rw [W.fourierValue, ← Lp.fourier_toTemperedDistribution_eq,
          FourierTransform.fourierInv_fourier_eq]
      rw [hT, TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply,
        SchwartzMap.fourierInv_coe]
      exact integral_fourierInv_smul_flip (ψ.integrable) hint
    rw [Lp.toTemperedDistribution_apply] at e1
    simp_rw [hψ, Complex.coe_smul] at e1
    have i1 : Integrable (fun y => φ y • (V : Eucl n → F) y) volume :=
      hVl.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have i2 : Integrable (fun y => φ y • g y) volume :=
      hgl.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub i1 i2, e1, sub_self])
  filter_upwards [hD] with y hy
  simpa [sub_eq_zero] using hy

/-- **`H^k(ℝⁿ) ⊂ C₀ ∩ L^∞` for `2k > n`** (S9a; B0711 tex 279–290, B0091 tex 1463–1477):
every `x ∈ W^{k,2}(ℝⁿ; F)` has a continuous representative vanishing at infinity, with
`sup |g| ≤ C ‖x‖_{H^k}` and `C` depending only on `n, k`. -/
theorem W.exists_C0_rep (hn : n < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : W (wholeSpace n) 1 ℂ F k 2,
      ∃ g : Eucl n → F, Continuous g ∧ Tendsto g (cocompact _) (𝓝 0) ∧
        (W.value (wholeSpace n) 1 ℂ F k 2 x : Eucl n → F) =ᵐ[volume] g ∧
        ∀ y, ‖g y‖ ≤ C * ‖x‖ := by
  refine ⟨(eLpNorm (bracketNeg (n := n) k) 2 volume).toReal * Real.sqrt (2 ^ k),
    by positivity, fun x => ?_⟩
  set F₀ : Eucl n → F := (W.fourierValue x : Eucl n → F) with hF₀
  have hint : Integrable F₀ volume := integrable_fourierValue hn x
  set g : Eucl n → F := 𝓕⁻ F₀ with hg
  -- continuity and decay, through the `L¹` inverse transform
  set F₁ : Lp F 1 (volume : Measure (Eucl n)) := (memLp_one_iff_integrable.mpr hint).toLp F₀
  have hgF₁ : (Real.Lp.fourierTransformInv F₁ : Eucl n → F) = g := by
    rw [Real.Lp.fourierTransformInv_toLp]
  have hcont : Continuous g := hgF₁ ▸ (Real.Lp.fourierTransformInv F₁).continuous
  have hdecay : Tendsto g (cocompact _) (𝓝 0) := by
    have h1 := tendsto_integral_exp_inner_smul_cocompact F₀
    have h2 : Tendsto (fun w : Eucl n => -w) (cocompact _) (cocompact _) :=
      (Homeomorph.neg (Eucl n)).isClosedEmbedding.tendsto_cocompact
    refine (h1.comp h2).congr fun w => ?_
    simp only [Function.comp, hg, Real.fourierInv_eq, inner_neg_right, neg_neg]
  -- the bound
  have hbound : ∀ y, ‖g y‖ ≤ (eLpNorm F₀ 1 volume).toReal := by
    intro y
    rw [hg, Real.fourierInv_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    simp_rw [Circle.norm_smul]
    rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hint.1]
  have hwne : eLpNorm (bracketNeg (n := n) k) 2 volume ≠ ⊤ := (memLp_bracketNeg hn).2.ne
  have hBne : eLpNorm (W.besselFn x) 2 volume ≠ ⊤ := (W.memLp_besselFn x).2.ne
  have hL1 : (eLpNorm F₀ 1 volume).toReal ≤
      (eLpNorm (bracketNeg (n := n) k) 2 volume).toReal * Real.sqrt (2 ^ k) * ‖x‖ := by
    calc (eLpNorm F₀ 1 volume).toReal
        ≤ (eLpNorm (bracketNeg (n := n) k) 2 volume * eLpNorm (W.besselFn x) 2 volume).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top hwne hBne) (eLpNorm_one_fourierValue_le x)
      _ = (eLpNorm (bracketNeg (n := n) k) 2 volume).toReal *
            (eLpNorm (W.besselFn x) 2 volume).toReal := ENNReal.toReal_mul
      _ ≤ (eLpNorm (bracketNeg (n := n) k) 2 volume).toReal * (Real.sqrt (2 ^ k) * ‖x‖) :=
          mul_le_mul_of_nonneg_left (toReal_eLpNorm_besselFn_le x) ENNReal.toReal_nonneg
      _ = _ := by ring
  refine ⟨g, hcont, hdecay, ?_, fun y => (hbound y).trans hL1⟩
  exact (coeFn_toVol _).symm.trans (W.toVol_ae_eq_fourierInv x hint)

end UnforcedLeray.Sob
