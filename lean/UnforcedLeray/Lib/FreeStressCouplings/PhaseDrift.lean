import UnforcedLeray.Lib.FreeStressCouplings.DilationGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# `B = T₀ - 3/4` diagonalised on `Y₂` (INF10 F1, part B)


§4 bypass **B9** and §5 Level F, target **F1**; blueprint units **B0459** (tex 7698-7722: "`B` is
skew-adjoint: it is the generator of the unitary group consisting of phase translation and the
`L²`-normalized spatial dilation") and **B0474** (tex 7789: `C₀ = 1 + |B|`).

In the flow chart (`DilationChart.lean`, `DilationGroup.lean`) the group `e^{tB}` is the
translation `θ ↦ θ + t`; the `L²` Fourier transform in `θ` turns it into multiplication by
`e^{2πiσt}`.  So `B` is diagonalised by

  `dilFourier P = 𝓕_θ ∘ prodLpEquiv ∘ chartY P : Y₂ ≃ L²(ℝ_σ; L²(K; ℂ³))`

with the real symbol `b(σ) = 2πσ`: `B = U⁻¹ (i b ·) U` (`driftRep P`, a `SkewRep`).  The spatial
variables of the shell `K` are carried as the parameter Hilbert space `L²(K; ℂ³)`.

* `fourier_translR`: `𝓕(g(· + t)) = e^{2πiσt} 𝓕 g` on `L²(ℝ; E)` (density of Schwartz functions);
* `dilFourier_phaseDilation`: `U e^{tB} = e^{itb} U`;
* `hasGen_iff_tendsto`: for a multiplication group, `i b g = h` iff `t⁻¹(e^{itb} g - g) → h`;
* `driftRep_hasGen_iff`: **`B` is the generator of the group** `phaseDilation P`
  (`phaseDilation_ae`: phase translation composed with the `L²`-normalised dilation), i.e.
  `B x = y` iff `t⁻¹ (e^{tB} x - x) → y` in `Y₂`.  Being a multiplication operator by `i b`
  with `b` real on its maximal domain, `B` is skew-adjoint (`SkewRep.inner_hasGen` gives
  `⟪u, B x⟫ = -⟪B u, x⟫`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real Topology SchwartzMap FourierTransform
open scoped ENNReal

namespace UnforcedLeray.FreeStress

open UnforcedLeray.PhaseSpace UnforcedLeray.Infra

section Translation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Translation `g ↦ g(· + t)` on `L²(ℝ; E)`. -/
def translR (t : ℝ) : Lp E 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp E 2 (volume : Measure ℝ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (· + t) (measurePreserving_add_right volume t)

theorem translR_ae (t : ℝ) (g : Lp E 2 (volume : Measure ℝ)) :
    (translR t g : ℝ → E) =ᵐ[volume] fun θ => g (θ + t) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_add_right volume t)

/-- The phase `e^{2πiσt}`. -/
def phaseMul (t σ : ℝ) : ℂ := Complex.exp ((2 * π * σ * t : ℝ) * Complex.I)

theorem norm_phaseMul (t σ : ℝ) : ‖phaseMul t σ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem measurable_phaseMul (t : ℝ) : Measurable (phaseMul t) := by
  unfold phaseMul
  fun_prop

/-- Multiplication by `e^{2πiσt}` on `L²(ℝ_σ; E)`. -/
def phaseMulOp (t : ℝ) : Lp E 2 (volume : Measure ℝ) →L[ℂ] Lp E 2 (volume : Measure ℝ) :=
  Mult.mulOp (phaseMul t) (measurable_phaseMul t).aestronglyMeasurable (C := 1)
    (Eventually.of_forall fun σ => (norm_phaseMul t σ).le)

theorem phaseMulOp_ae (t : ℝ) (g : Lp E 2 (volume : Measure ℝ)) :
    (phaseMulOp t g : ℝ → E) =ᵐ[volume] fun σ => phaseMul t σ • g σ :=
  Mult.coeFn_mulOp _ _ g

theorem translR_toLp (t : ℝ) (φ : 𝓢(ℝ, E)) :
    translR t (φ.toLp 2) = (SchwartzMap.compSubConstCLM ℂ (-t) φ).toLp 2 := by
  apply Lp.ext
  filter_upwards [translR_ae t (φ.toLp 2),
    (measurePreserving_add_right volume t).quasiMeasurePreserving.ae
      (SchwartzMap.coeFn_toLp φ 2 volume),
    SchwartzMap.coeFn_toLp (SchwartzMap.compSubConstCLM ℂ (-t) φ) 2 volume] with θ h1 h2 h3
  rw [h1, h3, h2, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]

theorem fourier_compSubConst (t : ℝ) (φ : 𝓢(ℝ, E)) (σ : ℝ) :
    𝓕 (SchwartzMap.compSubConstCLM ℂ (-t) φ) σ = phaseMul t σ • 𝓕 φ σ := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have hfun : (⇑(SchwartzMap.compSubConstCLM ℂ (-t) φ) : ℝ → E) = (⇑φ) ∘ fun v => v + t := by
    funext v
    rw [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, Function.comp_apply]
  rw [hfun]
  change VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) ((⇑φ) ∘ fun v => v + t) σ = _
  rw [VectorFourier.fourierIntegral_comp_add_right]
  change (𝐞 ((innerₗ ℝ) t σ)) • 𝓕 (⇑φ) σ = _
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 2
  have hin : (innerₗ ℝ) t σ = t * σ := by simp [innerₗ_apply_apply, mul_comm]
  rw [hin]
  push_cast
  ring

/-- **Fourier transform of a translate** on `L²(ℝ; E)`: `𝓕(g(· + t)) = e^{2πiσt} 𝓕 g`. -/
theorem fourier_translR (t : ℝ) (g : Lp E 2 (volume : Measure ℝ)) :
    Lp.fourierTransformₗᵢ ℝ E (translR t g) = phaseMulOp t (Lp.fourierTransformₗᵢ ℝ E g) := by
  refine DenseRange.induction_on (p := fun g : Lp E 2 (volume : Measure ℝ) =>
      Lp.fourierTransformₗᵢ ℝ E (translR t g) = phaseMulOp t (Lp.fourierTransformₗᵢ ℝ E g))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) g ?_ ?_
  · exact isClosed_eq ((Lp.fourierTransformₗᵢ ℝ E).continuous.comp (translR t).continuous)
      ((phaseMulOp t).continuous.comp (Lp.fourierTransformₗᵢ ℝ E).continuous)
  · intro φ
    simp only [SchwartzMap.toLpCLM_apply]
    change 𝓕 (translR t (φ.toLp 2)) = phaseMulOp t (𝓕 (φ.toLp 2))
    rw [translR_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
    apply Lp.ext
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (SchwartzMap.compSubConstCLM ℂ (-t) φ)) 2 volume,
      phaseMulOp_ae t ((𝓕 φ).toLp 2), SchwartzMap.coeFn_toLp (𝓕 φ) 2 volume] with σ h1 h2 h3
    rw [h1, h2, h3, fourier_compSubConst]

end Translation

section Generator

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tendsto_slope_exp (c : ℝ) :
    Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ * (Complex.exp ((t * c : ℝ) * Complex.I) - 1)) (𝓝[≠] 0)
      (𝓝 (Complex.I * (c : ℂ))) := by
  have h1 : HasDerivAt (fun t : ℝ => ((t * c : ℝ) : ℂ) * Complex.I) ((c : ℂ) * Complex.I) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const c).ofReal_comp).mul_const Complex.I
    simpa using this
  have h3 := hasDerivAt_iff_tendsto_slope_zero.1 h1.cexp
  have hlim : Complex.exp (((0 * c : ℝ) : ℂ) * Complex.I) * ((c : ℂ) * Complex.I) =
      Complex.I * (c : ℂ) := by simp [mul_comm]
  rw [hlim] at h3
  refine h3.congr fun t => ?_
  simp only [zero_add, zero_mul, Complex.ofReal_zero, Complex.exp_zero, Complex.real_smul,
    Complex.ofReal_inv]

theorem norm_slope_exp_le (c t : ℝ) :
    ‖((t : ℂ))⁻¹ * (Complex.exp ((t * c : ℝ) * Complex.I) - 1)‖ ≤ |c| := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_comm ((t * c : ℝ) : ℂ)]
  calc |t|⁻¹ * ‖Complex.exp (Complex.I * ((t * c : ℝ) : ℂ)) - 1‖ ≤ |t|⁻¹ * ‖t * c‖ :=
        mul_le_mul_of_nonneg_left Real.norm_exp_I_mul_ofReal_sub_one_le (by positivity)
    _ = |c| := by
        rw [Real.norm_eq_abs, abs_mul, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.2 ht), one_mul]

/-- **Generator of a multiplication group**: if `G t = e^{itb} g` then `h = i b g` iff
`t⁻¹ (G t - g) → h` in `L²` as `t → 0`. -/
theorem hasGen_iff_tendsto (b : α → ℝ) (hb : Measurable b) (G : ℝ → Lp E 2 μ) (g h : Lp E 2 μ)
    (hG : ∀ t, (G t : α → E) =ᵐ[μ] fun a => Complex.exp ((t * b a : ℝ) * Complex.I) • g a) :
    (∀ᵐ a ∂μ, h a = (Complex.I * (b a : ℂ)) • g a) ↔
      Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ • (G t - g)) (𝓝[≠] 0) (𝓝 h) := by
  set D : ℝ → Lp E 2 μ := fun t => ((t : ℂ))⁻¹ • (G t - g) with hD
  have hDae : ∀ t, (D t : α → E) =ᵐ[μ]
      fun a => (((t : ℂ))⁻¹ * (Complex.exp ((t * b a : ℝ) * Complex.I) - 1)) • g a := by
    intro t
    filter_upwards [Lp.coeFn_smul ((t : ℂ))⁻¹ (G t - g), Lp.coeFn_sub (G t) g, hG t]
      with a h1 h2 h3
    rw [hD]
    simp only
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, mul_smul, sub_smul, one_smul]
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  constructor
  · intro hh
    set F : ℝ → α → ℝ≥0∞ := fun t a => ‖(((t : ℂ))⁻¹ * (Complex.exp ((t * b a : ℝ) * Complex.I)
      - 1) - Complex.I * (b a : ℂ)) • g a‖ₑ ^ (2 : ℝ) with hF
    have hEq : ∀ t, eLpNorm (⇑(D t) - ⇑h) 2 μ = (∫⁻ a, F t a ∂μ) ^ (1 / (2 : ℝ)) := by
      intro t
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat]
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [hDae t, hh] with a h1 h2
      rw [Pi.sub_apply, h1, h2, ← sub_smul]
    have hmeas : ∀ t, AEMeasurable (F t) μ := by
      intro t
      have hc : Measurable fun a => (((t : ℂ))⁻¹ * (Complex.exp ((t * b a : ℝ) * Complex.I) - 1) -
          Complex.I * (b a : ℂ)) := by fun_prop
      exact ((hc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable g)).enorm.pow_const _)
    have hbound : ∀ t, ∀ᵐ a ∂μ, F t a ≤ (2 * ‖h a‖ₑ) ^ (2 : ℝ) := by
      intro t
      filter_upwards [hh] with a ha
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      have e1 : ‖Complex.I * (b a : ℂ)‖ = |b a| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hn : ‖(((t : ℂ))⁻¹ * (Complex.exp ((t * b a : ℝ) * Complex.I) - 1) -
          Complex.I * (b a : ℂ)) • g a‖ ≤ 2 * ‖h a‖ := by
        rw [ha, norm_smul, norm_smul, ← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine (norm_sub_le _ _).trans ?_
        rw [e1]
        linarith [norm_slope_exp_le (b a) t]
      rw [← ofReal_norm, ← ofReal_norm]
      refine le_trans (ENNReal.ofReal_le_ofReal hn) (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    have hfin : ∫⁻ a, (2 * ‖h a‖ₑ) ^ (2 : ℝ) ∂μ ≠ ∞ := by
      have h2 := (Lp.memLp h).eLpNorm_lt_top
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat] at h2
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      rw [lintegral_const_mul' _ _ (by simp)]
      exact ENNReal.mul_ne_top (by simp) h2.ne
    have hlim : ∀ᵐ a ∂μ, Tendsto (fun t => F t a) (𝓝[≠] 0) (𝓝 0) := by
      refine Eventually.of_forall fun a => ?_
      have h0 : Tendsto (fun t : ℝ => (((t : ℂ))⁻¹ * (Complex.exp ((t * b a : ℝ) * Complex.I)
          - 1) - Complex.I * (b a : ℂ)) • g a) (𝓝[≠] 0) (𝓝 0) := by
        have := ((tendsto_slope_exp (b a)).sub_const (Complex.I * (b a : ℂ))).smul_const (g a)
        simpa using this
      have h1 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp
        ((continuous_enorm.tendsto (0 : E)).comp h0)
      rw [enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at h1
      exact h1
    have hint := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ)
      (l := 𝓝[≠] (0 : ℝ)) (F := F) (f := fun _ => 0) (fun a => (2 * ‖h a‖ₑ) ^ (2 : ℝ))
      (Eventually.of_forall hmeas) (Eventually.of_forall hbound) hfin hlim
    rw [lintegral_zero] at hint
    have hfin2 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto _).comp hint
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hfin2
    refine hfin2.congr fun t => ?_
    rw [hEq t]
    rfl
  · intro hlim
    set u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hu
    have hu0 : Tendsto u atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Eventually.of_forall fun n => by
        simp only [hu, mem_compl_iff, mem_singleton_iff]
        positivity
    have hseq := hlim.comp hu0
    obtain ⟨ns, hns_mono, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ℝ≥0∞))
      two_ne_zero (fun n => Lp.aestronglyMeasurable (D (u n))) (Lp.aestronglyMeasurable h)
      hseq).exists_seq_tendsto_ae
    have hall : ∀ᵐ a ∂μ, ∀ n, (D (u n) : α → E) a =
        (((u n : ℂ))⁻¹ * (Complex.exp ((u n * b a : ℝ) * Complex.I) - 1)) • g a := by
      rw [ae_all_iff]
      exact fun n => hDae (u n)
    filter_upwards [hns, hall] with a h1 h2
    have h3 : Tendsto (fun i => (D (u (ns i)) : α → E) a) atTop
        (𝓝 ((Complex.I * (b a : ℂ)) • g a)) := by
      simp_rw [h2]
      have hsub : Tendsto (fun i => u (ns i)) atTop (𝓝[≠] 0) :=
        hu0.comp hns_mono.tendsto_atTop
      exact ((tendsto_slope_exp (b a)).comp hsub).smul_const (g a)
    exact tendsto_nhds_unique h1 h3

end Generator

variable (P : ℝ) [hP : Fact (0 < P)]

/-- The parameter Hilbert space `L²(K; ℂ³)` of the shell. -/
abbrev ShellL2 : Type := Lp CVec3 2 ((volume : Measure Space).restrict (shell P))

theorem prodLpEquiv_chartShift (t : ℝ) (h : Lp CVec3 2 (chartBase P)) :
    prodLpEquiv (chartShift P t h) = translR t (prodLpEquiv h) := by
  apply Lp.ext
  have h1 := prodLpEquiv_ae (chartShift P t h)
  have h2 := Measure.ae_ae_of_ae_prod (chartShift_ae P t h)
  have h3 := translR_ae t (prodLpEquiv h)
  have h4 := (measurePreserving_add_right (volume : Measure ℝ) t).quasiMeasurePreserving.ae
    (prodLpEquiv_ae (ν := (volume : Measure ℝ)) (μ := (volume : Measure Space).restrict (shell P)) h)
  filter_upwards [h1, h2, h3, h4] with θ e1 e2 e3 e4
  rw [e3]
  apply Lp.ext
  have e2' : (fun z => (chartShift P t h : ℝ × Space → CVec3) (θ, z)) =ᵐ[_]
      fun z => (h : ℝ × Space → CVec3) (θ + t, z) := e2
  exact e1.trans (e2'.trans e4.symm)

/-- **The diagonalising unitary of `B`**: chart, Fubini, Fourier transform in `θ`. -/
def dilFourier : Yq P 2 ≃ₗᵢ[ℂ] Lp (ShellL2 P) 2 (volume : Measure ℝ) :=
  (chartY P).trans (prodLpEquiv.trans (Lp.fourierTransformₗᵢ ℝ (ShellL2 P)))

/-- `U e^{tB} = e^{2πiσt} U`. -/
theorem dilFourier_phaseDilation (t : ℝ) (x : Yq P 2) :
    dilFourier P (phaseDilation P t x) = phaseMulOp t (dilFourier P x) := by
  change Lp.fourierTransformₗᵢ ℝ (ShellL2 P) (prodLpEquiv (chartY P (phaseDilation P t x))) =
    phaseMulOp t (Lp.fourierTransformₗᵢ ℝ (ShellL2 P) (prodLpEquiv (chartY P x)))
  rw [chartY_phaseDilation, prodLpEquiv_chartShift, fourier_translR]

/-- **`B = T₀ - 3/4` on `Y₂`, diagonalised** (bypass B9, B0459): unitary `dilFourier P` and
real symbol `b(σ) = 2πσ`; `B = U⁻¹ (i b ·) U`. -/
def driftRep : SkewRep (Yq P 2) (volume : Measure ℝ) (ShellL2 P) where
  U := dilFourier P
  sym σ := 2 * π * σ
  measurable_sym := by fun_prop

/-- **`B` is the generator of `e^{tB}`** (B0459(i), tex 7713-7715): `B x = y` iff
`t⁻¹ (e^{tB} x - x) → y` in `Y₂` as `t → 0`, where `e^{tB} = phaseDilation P t` is phase
translation composed with the `L²`-normalised dilation (`phaseDilation_ae`). -/
theorem driftRep_hasGen_iff (x y : Yq P 2) :
    (driftRep P).HasGen x y ↔
      Tendsto (fun t : ℝ => ((t : ℂ))⁻¹ • (phaseDilation P t x - x)) (𝓝[≠] 0) (𝓝 y) := by
  have hind : IsInducing (dilFourier P) := (dilFourier P).toHomeomorph.isInducing
  rw [hind.tendsto_nhds_iff]
  have hcomp : (dilFourier P ∘ fun t : ℝ => ((t : ℂ))⁻¹ • (phaseDilation P t x - x)) =
      fun t : ℝ => ((t : ℂ))⁻¹ • (dilFourier P (phaseDilation P t x) - dilFourier P x) := by
    funext t
    rw [Function.comp_apply, map_smul, map_sub]
  rw [hcomp]
  refine hasGen_iff_tendsto (fun σ => 2 * π * σ) (by fun_prop)
    (fun t => dilFourier P (phaseDilation P t x)) (dilFourier P x) (dilFourier P y) fun t => ?_
  rw [dilFourier_phaseDilation]
  filter_upwards [phaseMulOp_ae t (dilFourier P x)] with σ h
  rw [h, phaseMul]
  congr 3
  ring

/-- `C₀ = 1 + |B|` on `Y₂` (tex 7789), in the representation of `B`. -/
abbrev phaseC0 : MulRep (Yq P 2) (volume : Measure ℝ) (ShellL2 P) := (driftRep P).onePlusAbs

end UnforcedLeray.FreeStress
