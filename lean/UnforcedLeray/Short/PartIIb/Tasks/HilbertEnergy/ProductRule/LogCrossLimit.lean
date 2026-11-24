import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTranslateContinuous

/-!
# Part II-b, task `PartII-b:T15/2/11`: limit of the cross term

Source of record: `the November 2 reference manuscript`, lines 1974-1979 (the weak
product rule in the `H_2` measure; log chart `s = e^t`). The statement is `LogCrossLimit`
(`Sub/T15_2.lean`), proved here with no extra hypotheses. Accepted dependencies:
`logTranslateContinuous`, `logTC_sq` and `logTC_measurePreserving`
(`ProductRule/LogTranslateContinuous.lean`).

Strategy. Write `u_h = u(· + h)`, `D_h = h⁻¹ (u_h - u)`, `U_h = u_h + u`, `V_h = u_h - u`.
Pointwise, `D_h \bar U_h ψ - 2 G \bar u ψ = (D_h - G) \bar U_h ψ + G \bar V_h ψ`.
A Hölder bound `|∫ F \bar K ψ| ≤ C ‖F‖₂ ‖K‖₂` for `|ψ| ≤ C` controls both terms.
Then `‖D_h - G‖₂ → 0`, `‖V_h‖₂ → 0` (`logTranslateContinuous`), and `‖U_h‖₂ ≤ 2 ‖u‖₂`
(translation invariance and Minkowski). `squeeze_zero` finishes.

Every auxiliary declaration is prefixed `logCL_`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIb

/-! ## Convergence of `L²` norms from convergence of their squares -/

/-- If `∫⁻ ‖F_h‖ₑ²` tends to `0` on `logMeas c`, then `‖F_h‖₂ → 0`. -/
theorem logCL_tendsto_eLpNorm (c : ℝ) (F : ℝ → Coord → ℂ) (l : Filter ℝ)
    (hT : Tendsto (fun h => ∫⁻ x, ‖F h x‖ₑ ^ 2 ∂(logMeas c)) l (𝓝 0)) :
    Tendsto (fun h => (eLpNorm (F h) 2 (logMeas c)).toReal) l (𝓝 0) := by
  have hS : Tendsto (fun h => (∫⁻ x, ‖F h x‖ₑ ^ 2 ∂(logMeas c)).toReal) l (𝓝 0) := by
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
    rw [ENNReal.toReal_zero] at h0
    exact h0
  have h3 := (Real.continuous_sqrt.tendsto 0).comp hS
  rw [Real.sqrt_zero] at h3
  refine h3.congr fun h => ?_
  show Real.sqrt ((∫⁻ x, ‖F h x‖ₑ ^ 2 ∂(logMeas c)).toReal) = (eLpNorm (F h) 2 (logMeas c)).toReal
  rw [logTC_sq, ENNReal.toReal_pow, Real.sqrt_sq ENNReal.toReal_nonneg]

/-! ## Hölder bound for `∫ F G ψ` -/

/-- Integrability and a Hölder bound for `∫ F(x) G(x) ψ(x)`, with `F, G ∈ L²` and `|ψ| ≤ C`. -/
theorem logCL_holder (μ : Measure Coord) (F G : Coord → ℂ) (ψ : Coord → ℝ) (C : ℝ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (hψc : Continuous ψ) (hC : ∀ x, |ψ x| ≤ C) :
    Integrable (fun x => F x * G x * (ψ x : ℂ)) μ ∧
      ‖∫ x, F x * G x * (ψ x : ℂ) ∂μ‖ ≤
        C * (eLpNorm F 2 μ).toReal * (eLpNorm G 2 μ).toReal := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  have hFG : Integrable (fun x => F x * G x) μ := hF.integrable_mul hG
  have hmeas : AEStronglyMeasurable (fun x => F x * G x) μ := hFG.aestronglyMeasurable
  have hψm : AEStronglyMeasurable (fun x => (ψ x : ℂ)) μ :=
    (Complex.continuous_ofReal.comp hψc).aestronglyMeasurable
  have hψb : ∀ᵐ x ∂μ, ‖(ψ x : ℂ)‖ ≤ C :=
    ae_of_all μ fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hC x
  have hintF : Integrable (fun x => F x * G x * (ψ x : ℂ)) μ := hFG.mul_bdd hψm hψb
  have hae : ∀ᵐ x ∂μ, ‖(fun a b : ℂ => a * b) (F x) (G x)‖₊ ≤ (1 : ℝ≥0) * ‖F x‖₊ * ‖G x‖₊ :=
    ae_of_all μ fun x => by simp [nnnorm_mul]
  have hbd : eLpNorm (fun x => F x * G x) 1 μ ≤ eLpNorm F 2 μ * eLpNorm G 2 μ := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1)
      hF.1 hG.1 (fun a b : ℂ => a * b) 1 hae
    simpa using h
  have hnorm : ∫ x, ‖F x * G x‖ ∂μ = (eLpNorm (fun x => F x * G x) 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, integral_norm_eq_lintegral_enorm hmeas]
  have hpt : ∀ x, ‖F x * G x * (ψ x : ℂ)‖ ≤ C * ‖F x * G x‖ := fun x => by
    rw [norm_mul (F x * G x) (ψ x : ℂ), mul_comm C, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
  have hbound : ‖∫ x, F x * G x * (ψ x : ℂ) ∂μ‖ ≤ ∫ x, C * ‖F x * G x‖ ∂μ :=
    norm_integral_le_of_norm_le (hFG.norm.const_mul C) (ae_of_all μ hpt)
  rw [integral_const_mul, hnorm] at hbound
  have hmono : (eLpNorm (fun x => F x * G x) 1 μ).toReal ≤
      (eLpNorm F 2 μ * eLpNorm G 2 μ).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top hF.eLpNorm_ne_top hG.eLpNorm_ne_top) hbd
  rw [ENNReal.toReal_mul] at hmono
  refine ⟨hintF, hbound.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hmono hC0

/-! ## Algebra -/

/-- The pointwise identity behind the splitting `D \bar U - 2 G \bar u = (D - G) \bar U + G \bar V`
with `U = uh + u` and `V = uh - u`. -/
theorem logCL_pointwise (D G uh u p : ℂ) :
    D * starRingEnd ℂ (uh + u) * p - 2 * (G * starRingEnd ℂ u * p) =
      (D - G) * starRingEnd ℂ (uh + u) * p + G * starRingEnd ℂ (uh - u) * p := by
  simp only [map_add, map_sub]
  ring

/-- Integral form of a pointwise splitting `P - 2 Q = F₁ + F₂`. -/
theorem logCL_split (μ : Measure Coord) (P Q F1 F2 : Coord → ℂ)
    (hP : Integrable P μ) (hQ : Integrable Q μ) (hF1 : Integrable F1 μ) (hF2 : Integrable F2 μ)
    (hpt : ∀ x, P x - 2 * Q x = F1 x + F2 x) :
    ∫ x, P x ∂μ - 2 * ∫ x, Q x ∂μ = ∫ x, F1 x ∂μ + ∫ x, F2 x ∂μ := by
  have h1 : ∫ x, (P x - 2 * Q x) ∂μ = ∫ x, P x ∂μ - 2 * ∫ x, Q x ∂μ := by
    rw [integral_sub hP (hQ.const_mul 2), integral_const_mul]
  have h2 : ∫ x, (P x - 2 * Q x) ∂μ = ∫ x, (F1 x + F2 x) ∂μ :=
    integral_congr_ae (ae_of_all μ hpt)
  rw [← h1, h2, integral_add hF1 hF2]

/-! ## The splitting bound -/

/-- The cross term splits as `∫ (D - G) \bar U ψ + ∫ G \bar V ψ`, each Hölder-bounded. -/
theorem logCL_core (μ : Measure Coord) (ψ : Coord → ℝ) (C : ℝ) (hψc : Continuous ψ)
    (hC : ∀ x, |ψ x| ≤ C) (D U V G u : Coord → ℂ)
    (hD : MemLp D 2 μ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) (hG : MemLp G 2 μ)
    (hu : MemLp u 2 μ)
    (hrel : ∀ x, D x * starRingEnd ℂ (U x) * (ψ x : ℂ)
        - 2 * (G x * starRingEnd ℂ (u x) * (ψ x : ℂ))
        = (D x - G x) * starRingEnd ℂ (U x) * (ψ x : ℂ)
          + G x * starRingEnd ℂ (V x) * (ψ x : ℂ)) :
    ‖(∫ x, D x * starRingEnd ℂ (U x) * (ψ x : ℂ) ∂μ) -
        2 * ∫ x, G x * starRingEnd ℂ (u x) * (ψ x : ℂ) ∂μ‖ ≤
      C * (eLpNorm (fun x => D x - G x) 2 μ).toReal * (eLpNorm U 2 μ).toReal +
        C * (eLpNorm G 2 μ).toReal * (eLpNorm V 2 μ).toReal := by
  have hconj : ∀ f : Coord → ℂ, eLpNorm (fun x => starRingEnd ℂ (f x)) 2 μ = eLpNorm f 2 μ :=
    fun f => eLpNorm_congr_norm_ae (ae_of_all μ fun x => by simp)
  have hcU : MemLp (fun x => starRingEnd ℂ (U x)) 2 μ := hU.star
  have hcu : MemLp (fun x => starRingEnd ℂ (u x)) 2 μ := hu.star
  have hcV : MemLp (fun x => starRingEnd ℂ (V x)) 2 μ := hV.star
  have hDG : MemLp (fun x => D x - G x) 2 μ := hD.sub hG
  have hP : Integrable (fun x => D x * starRingEnd ℂ (U x) * (ψ x : ℂ)) μ :=
    (logCL_holder μ D (fun x => starRingEnd ℂ (U x)) ψ C hD hcU hψc hC).1
  have hQ : Integrable (fun x => G x * starRingEnd ℂ (u x) * (ψ x : ℂ)) μ :=
    (logCL_holder μ G (fun x => starRingEnd ℂ (u x)) ψ C hG hcu hψc hC).1
  have hF1 : Integrable (fun x => (D x - G x) * starRingEnd ℂ (U x) * (ψ x : ℂ)) μ :=
    (logCL_holder μ (fun x => D x - G x) (fun x => starRingEnd ℂ (U x)) ψ C hDG hcU hψc hC).1
  have hF2 : Integrable (fun x => G x * starRingEnd ℂ (V x) * (ψ x : ℂ)) μ :=
    (logCL_holder μ G (fun x => starRingEnd ℂ (V x)) ψ C hG hcV hψc hC).1
  have hF1b : ‖∫ x, (D x - G x) * starRingEnd ℂ (U x) * (ψ x : ℂ) ∂μ‖ ≤
      C * (eLpNorm (fun x => D x - G x) 2 μ).toReal * (eLpNorm U 2 μ).toReal := by
    have h := (logCL_holder μ (fun x => D x - G x) (fun x => starRingEnd ℂ (U x)) ψ C hDG
      hcU hψc hC).2
    rw [hconj U] at h
    exact h
  have hF2b : ‖∫ x, G x * starRingEnd ℂ (V x) * (ψ x : ℂ) ∂μ‖ ≤
      C * (eLpNorm G 2 μ).toReal * (eLpNorm V 2 μ).toReal := by
    have h := (logCL_holder μ G (fun x => starRingEnd ℂ (V x)) ψ C hG hcV hψc hC).2
    rw [hconj V] at h
    exact h
  have hsplit : (∫ x, D x * starRingEnd ℂ (U x) * (ψ x : ℂ) ∂μ) -
        2 * ∫ x, G x * starRingEnd ℂ (u x) * (ψ x : ℂ) ∂μ =
      (∫ x, (D x - G x) * starRingEnd ℂ (U x) * (ψ x : ℂ) ∂μ) +
        ∫ x, G x * starRingEnd ℂ (V x) * (ψ x : ℂ) ∂μ :=
    logCL_split μ _ _ _ _ hP hQ hF1 hF2 hrel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hF1b hF2b)

/-! ## The main theorem -/

/-- **Leaf `PartII-b:T15/2/11`** (limit of the cross term). If `D_h → G` in `L²(logMeas c)` and
`ψ` is bounded and continuous, then `∫ D_h \bar{(u_h + u)} ψ → 2 ∫ G \bar u ψ`. -/
theorem logCrossLimit : LogCrossLimit := by
  unfold LogCrossLimit
  intro c u G hc hu hG hD ψ hψc hψb
  obtain ⟨C, hC⟩ := hψb
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  -- `L²` facts for the translates `u_h = u(· + h)` on `logMeas c`
  have hTr : ∀ h : ℝ, MemLp (fun x : Coord => u (x.1 + h, x.2)) 2 (logMeas c) :=
    fun h => hu.comp_measurePreserving (logTC_measurePreserving c h)
  have hDm : ∀ h : ℝ,
      MemLp (fun x : Coord => (h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) 2 (logMeas c) :=
    fun h => ((hTr h).sub hu).const_smul (h⁻¹ : ℝ)
  have hUm : ∀ h : ℝ, MemLp (fun x : Coord => u (x.1 + h, x.2) + u x) 2 (logMeas c) :=
    fun h => (hTr h).add hu
  have hVm : ∀ h : ℝ, MemLp (fun x : Coord => u (x.1 + h, x.2) - u x) 2 (logMeas c) :=
    fun h => (hTr h).sub hu
  -- the splitting bound, for each `h`
  have hcore : ∀ h : ℝ,
      ‖(∫ x, ((h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) * starRingEnd ℂ (u (x.1 + h, x.2) + u x)
            * (ψ x : ℂ) ∂(logMeas c))
          - 2 * ∫ x, G x * starRingEnd ℂ (u x) * (ψ x : ℂ) ∂(logMeas c)‖ ≤
        C * (eLpNorm (fun x : Coord => (h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x) - G x) 2
            (logMeas c)).toReal *
          (eLpNorm (fun x : Coord => u (x.1 + h, x.2) + u x) 2 (logMeas c)).toReal +
        C * (eLpNorm G 2 (logMeas c)).toReal *
          (eLpNorm (fun x : Coord => u (x.1 + h, x.2) - u x) 2 (logMeas c)).toReal := by
    intro h
    exact logCL_core (logMeas c) ψ C hψc hC _ _ _ G u (hDm h) (hUm h) (hVm h) hG hu
      (fun x => logCL_pointwise ((h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) (G x)
        (u (x.1 + h, x.2)) (u x) (ψ x : ℂ))
  -- the two `L²` distances tend to `0`
  have hA : Tendsto (fun h : ℝ =>
      (eLpNorm (fun x : Coord => (h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x) - G x) 2
        (logMeas c)).toReal) (𝓝[≠] 0) (𝓝 0) :=
    logCL_tendsto_eLpNorm c (fun h x => (h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x) - G x)
      (𝓝[≠] 0) hD
  have hVt : Tendsto (fun h : ℝ =>
      (eLpNorm (fun x : Coord => u (x.1 + h, x.2) - u x) 2 (logMeas c)).toReal)
      (𝓝[≠] 0) (𝓝 0) :=
    (logCL_tendsto_eLpNorm c (fun h x => u (x.1 + h, x.2) - u x) (𝓝 0)
      (logTranslateContinuous c u hc hu)).mono_left nhdsWithin_le_nhds
  -- `‖u_h + u‖₂ ≤ 2 ‖u‖₂`
  have hshift : ∀ h : ℝ,
      eLpNorm (fun x : Coord => u (x.1 + h, x.2)) 2 (logMeas c) = eLpNorm u 2 (logMeas c) :=
    fun h => eLpNorm_comp_measurePreserving hu.1 (logTC_measurePreserving c h)
  have hUb : ∀ h : ℝ, (eLpNorm (fun x : Coord => u (x.1 + h, x.2) + u x) 2 (logMeas c)).toReal ≤
      2 * (eLpNorm u 2 (logMeas c)).toReal := by
    intro h
    have h1 : eLpNorm (fun x : Coord => u (x.1 + h, x.2) + u x) 2 (logMeas c) ≤
        eLpNorm (fun x : Coord => u (x.1 + h, x.2)) 2 (logMeas c) + eLpNorm u 2 (logMeas c) :=
      eLpNorm_add_le (hTr h).1 hu.1 (by norm_num)
    rw [hshift h] at h1
    have h2 : eLpNorm (fun x : Coord => u (x.1 + h, x.2) + u x) 2 (logMeas c) ≤
        2 * eLpNorm u 2 (logMeas c) := by
      rw [two_mul]
      exact h1
    have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hu.eLpNorm_ne_top) h2
    rw [ENNReal.toReal_mul] at h3
    simpa using h3
  -- squeeze
  have hlim : Tendsto (fun h : ℝ =>
      C * (eLpNorm (fun x : Coord => (h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x) - G x) 2
        (logMeas c)).toReal * (2 * (eLpNorm u 2 (logMeas c)).toReal) +
      C * (eLpNorm G 2 (logMeas c)).toReal *
        (eLpNorm (fun x : Coord => u (x.1 + h, x.2) - u x) 2 (logMeas c)).toReal)
      (𝓝[≠] 0) (𝓝 0) := by
    have h1 := ((hA.const_mul C).mul_const (2 * (eLpNorm u 2 (logMeas c)).toReal)).add
      (hVt.const_mul (C * (eLpNorm G 2 (logMeas c)).toReal))
    have h0 : C * 0 * (2 * (eLpNorm u 2 (logMeas c)).toReal) +
        C * (eLpNorm G 2 (logMeas c)).toReal * 0 = 0 := by
      ring
    rw [h0] at h1
    exact h1
  have hnorm : Tendsto (fun h : ℝ =>
      ‖(∫ x, ((h⁻¹ : ℝ) • (u (x.1 + h, x.2) - u x)) * starRingEnd ℂ (u (x.1 + h, x.2) + u x)
            * (ψ x : ℂ) ∂(logMeas c))
          - 2 * ∫ x, G x * starRingEnd ℂ (u x) * (ψ x : ℂ) ∂(logMeas c)‖)
      (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero (fun h => norm_nonneg _) (fun h => ?_) hlim
    refine (hcore h).trans (add_le_add ?_ le_rfl)
    exact mul_le_mul_of_nonneg_left (hUb h) (mul_nonneg hC0 ENNReal.toReal_nonneg)
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm

end UnforcedLeray.Short.IIb
