import UnforcedLeray.Units.B0121.WeakDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# B0121 helper: the Gaussian `L²` space `L²(ℝ², G⁻¹ dy)` and test functions of temperate growth

Blueprint unit B0121 (`eq:st18-t00100`, `paper/main.tex` lines 1856--1865).

* `MemGaussL2 F`: `F ∈ L²(ℝ², G⁻¹ dy)`, i.e. `U_G F = F/√G ∈ L²(ℝ², dy)` (B0093's `conjG`);
  `gaussNormSq F = ∫ |F|² G⁻¹ dy`, and `norm_toLp_sq` identifies it with the `L²` norm of `U_G F`.
* `gS ζ = √G ζ = U_G⁻¹ ζ` on Schwartz functions and the conjugation identity
  `∂ᵢ (√G ζ) = √G (∂ᵢ - yᵢ/4) ζ` (`dop_gS`, tex line 1863).
* `integral_dirDeriv_temperate`: a first-order weak derivative relation between two functions
  of `L²(ℝ², G⁻¹ dy)`, tested against smooth compactly supported functions, extends to test
  functions of temperate growth (cutoff `φ(y) b(y/(n+1))` and dominated convergence). This is
  how the polynomial test functions `U_G` of the Hermite levels enter.
* `IsGP ζ`: `ζ = √G P` with `P` of temperate growth; stable under `Aᵢ` and `Bᵢ`, and
  `integral_peel` moves one derivative from the weak-derivative side to the test side.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped SchwartzMap InnerProductSpace ComplexConjugate ContDiff

namespace UnforcedLeray.B0121

open UnforcedLeray.B0094 UnforcedLeray.PlanarBS.Sob

/-! ## The square root of the Gaussian weight -/

/-- `√G` with `G = (4π)⁻¹ e^{-|y|²/4}` (B0093's `gaussianWeight`, tex line 649). -/
def sqG (z : ℝ × ℝ) : ℝ := Real.sqrt (B0093.gaussianWeight z)

theorem sqG_eq_halfGaussian : sqG = B0093.halfGaussian B0093.sqrtConst := by
  funext z
  exact B0093.sqrt_gaussianWeight z

theorem sqG_pos (z : ℝ × ℝ) : 0 < sqG z := Real.sqrt_pos.2 (B0093.gaussianWeight_pos z)

theorem sqG_sq (z : ℝ × ℝ) : sqG z ^ 2 = B0093.gaussianWeight z :=
  Real.sq_sqrt (B0093.gaussianWeight_pos z).le

theorem sqG_eq (z : ℝ × ℝ) : sqG z = B0093.sqrtConst * gaussS z := by
  rw [sqG_eq_halfGaussian, B0093.halfGaussian, gaussS_apply]
  rfl

/-- `√G` as a complex function. -/
def sqGc (z : ℝ × ℝ) : ℂ := ((sqG z : ℝ) : ℂ)

theorem sqGc_ne_zero (z : ℝ × ℝ) : sqGc z ≠ 0 := Complex.ofReal_ne_zero.2 (sqG_pos z).ne'

theorem hasTemperateGrowth_sqGc : sqGc.HasTemperateGrowth := by
  have h : sqGc = (fun _ : ℝ × ℝ => ((B0093.sqrtConst : ℝ) : ℂ)) *
      fun z => ((gaussS z : ℝ) : ℂ) := by
    funext z
    simp [sqGc, sqG_eq]
  rw [h]
  exact (Function.HasTemperateGrowth.const _).mul
    (hasTemperateGrowth_ofReal_comp gaussS.hasTemperateGrowth)

theorem contDiff_sqG : ContDiff ℝ ∞ sqG := by
  rw [sqG_eq_halfGaussian]
  exact B0093.contDiff_halfGaussian _

theorem fderiv_sqG_ev (i : Fin 2) (z : ℝ × ℝ) :
    fderiv ℝ sqG z (ev i) = -(crdL i z / 4) * sqG z := by
  have hd : DifferentiableAt ℝ sqG z := (contDiff_sqG.differentiable (by simp)) z
  rw [sqG_eq_halfGaussian] at hd ⊢
  fin_cases i
  · show fderiv ℝ _ z (1, 0) = _
    rw [← B0093.dx_eq_fderiv hd, B0093.dx_halfGaussian]
    rfl
  · show fderiv ℝ _ z (0, 1) = _
    rw [← B0093.dy_eq_fderiv hd, B0093.dy_halfGaussian]
    rfl

theorem hasFDerivAt_sqGc (z : ℝ × ℝ) :
    HasFDerivAt sqGc (Complex.ofRealCLM.comp (fderiv ℝ sqG z)) z := by
  have hd : DifferentiableAt ℝ sqG z := (contDiff_sqG.differentiable (by simp)) z
  exact Complex.ofRealCLM.hasFDerivAt.comp z hd.hasFDerivAt

/-- `∂ᵢ √G = -(yᵢ/4) √G`. -/
theorem fderiv_sqGc_ev (i : Fin 2) (z : ℝ × ℝ) :
    fderiv ℝ sqGc z (ev i) = -(crdC i z / 4) * sqGc z := by
  rw [(hasFDerivAt_sqGc z).fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    fderiv_sqG_ev]
  simp [crdC, sqGc]

/-! ## `U_G⁻¹ = √G ·` on Schwartz functions -/

/-- `U_G⁻¹ ζ = √G ζ` on `𝓢(ℝ², ℂ)`. -/
def gS : S2 →L[ℂ] S2 := SchwartzMap.smulLeftCLM ℂ sqGc

theorem gS_apply (ζ : S2) (z : ℝ × ℝ) : gS ζ z = sqGc z * ζ z := by
  simp [gS, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_sqGc]

/-- **The conjugation identity** (tex line 1863): `∂ᵢ (√G ζ) = √G (∂ᵢ - yᵢ/4) ζ`, i.e.
`U_G ∂ᵢ U_G⁻¹ = Aᵢ`. -/
theorem dop_gS (i : Fin 2) (ζ : S2) : dop i (gS ζ) = gS (Aop i ζ) := by
  ext z
  have hX : ⇑(gS ζ) = sqGc * ⇑ζ := by
    funext y
    rw [gS_apply, Pi.mul_apply]
  have hm := (hasFDerivAt_sqGc z).mul (ζ.hasFDerivAt z)
  rw [dop_apply, hX, hm.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, gS_apply, Aop_apply, sub_apply, X_apply,
    dop_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, fderiv_sqG_ev]
  simp only [crdC, sqGc]
  push_cast
  ring

theorem coe_dop_eq_dirDeriv (i : Fin 2) (ζ : S2) : ⇑(dop i ζ) = dirDeriv (ev i) ⇑ζ := rfl

/-! ## `L²(ℝ², G⁻¹ dy)` -/

/-- `F ∈ L²(ℝ², G⁻¹ dy)` (the space of `eq:st18-t00100`): `U_G F = F/√G ∈ L²(ℝ², dy)`. This
includes the a.e. strong measurability of `F`. -/
def MemGaussL2 (F : ℝ × ℝ → ℂ) : Prop := MemLp (B0093.conjG F) 2 volume

/-- `‖F‖²_{L²(ℝ², G⁻¹ dy)} = ∫ |F|² G⁻¹ dy`. -/
def gaussNormSq (F : ℝ × ℝ → ℂ) : ℝ := ∫ z, ‖F z‖ ^ 2 * (B0093.gaussianWeight z)⁻¹

theorem conjG_apply (F : ℝ × ℝ → ℂ) (z : ℝ × ℝ) :
    B0093.conjG F z = (((sqG z)⁻¹ : ℝ) : ℂ) * F z := by
  rw [B0093.conjG, Complex.real_smul]
  rfl

theorem norm_conjG_sq (F : ℝ × ℝ → ℂ) (z : ℝ × ℝ) :
    ‖B0093.conjG F z‖ ^ 2 = ‖F z‖ ^ 2 * (B0093.gaussianWeight z)⁻¹ := by
  rw [conjG_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (sqG_pos z)), mul_pow, inv_pow, sqG_sq]
  ring

/-- The `L²(ℝ², dy)` norm of `U_G F` is the Gaussian norm of `F`. -/
theorem norm_toLp_sq {F : ℝ × ℝ → ℂ} (hF : MemGaussL2 F) :
    ‖hF.toLp (B0093.conjG F)‖ ^ 2 = gaussNormSq F := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  have h : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      ⟪(hF.toLp (B0093.conjG F) : ℝ × ℝ → ℂ) z, (hF.toLp (B0093.conjG F) : ℝ × ℝ → ℂ) z⟫_ℂ =
        (((‖F z‖ ^ 2 * (B0093.gaussianWeight z)⁻¹ : ℝ)) : ℂ) := by
    filter_upwards [hF.coeFn_toLp] with z hz
    rw [hz, RCLike.inner_apply, Complex.mul_conj', ← Complex.ofReal_pow, norm_conjG_sq]
  rw [integral_congr_ae h, integral_complex_ofReal]
  rfl

theorem conjG_gS (ζ : S2) : B0093.conjG ⇑(gS ζ) = ⇑ζ := by
  funext z
  rw [conjG_apply, gS_apply, sqGc, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (sqG_pos z).ne', Complex.ofReal_one, one_mul]

theorem memGaussL2_gS (ζ : S2) : MemGaussL2 ⇑(gS ζ) := by
  rw [MemGaussL2, conjG_gS]
  exact ζ.memLp 2 volume

/-- `√G (U_G F) = F`. -/
theorem sqGc_mul_conjG (F : ℝ × ℝ → ℂ) (z : ℝ × ℝ) : sqGc z * B0093.conjG F z = F z := by
  rw [conjG_apply, sqGc, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (sqG_pos z).ne',
    Complex.ofReal_one, one_mul]

theorem sqG_le (z : ℝ × ℝ) : sqG z ≤ B0093.sqrtConst := by
  rw [sqG_eq, gaussS_apply]
  have h1 : Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 8)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg z.1, sq_nonneg z.2])
  have h2 := B0093.sqrtConst_pos
  nlinarith

/-- `L²(ℝ², G⁻¹ dy) ⊂ L²(ℝ², dy)`. -/
theorem MemGaussL2.memLp {F : ℝ × ℝ → ℂ} (hF : MemGaussL2 F) : MemLp F 2 volume := by
  have h : F = fun z => sqGc z * B0093.conjG F z := by
    funext z
    rw [sqGc_mul_conjG]
  rw [h]
  refine hF.of_le_mul (c := B0093.sqrtConst) ?_ (Eventually.of_forall fun z => ?_)
  · exact ((Complex.continuous_ofReal.comp contDiff_sqG.continuous).aestronglyMeasurable).mul
      hF.aestronglyMeasurable
  · rw [norm_mul, sqGc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sqG_pos z)]
    exact mul_le_mul_of_nonneg_right (sqG_le z) (norm_nonneg _)

theorem MemGaussL2.locallyIntegrable {F : ℝ × ℝ → ℂ} (hF : MemGaussL2 F) :
    LocallyIntegrable F volume :=
  hF.memLp.locallyIntegrable (by norm_num)

theorem MemGaussL2.aestronglyMeasurable {F : ℝ × ℝ → ℂ} (hF : MemGaussL2 F) :
    AEStronglyMeasurable F volume :=
  hF.memLp.aestronglyMeasurable

/-! ## Products of `L²` functions -/

theorem integrable_mul_of_memLp {a b : ℝ × ℝ → ℂ} (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) : Integrable (fun z => a z * b z) volume := by
  have h := hb.mul' (r := 1) ha
  exact memLp_one_iff_integrable.1 h

/-- `∫ a b = ⟪conj a, b⟫_{L²}`. -/
theorem integral_mul_eq_inner {a b : ℝ × ℝ → ℂ} (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) :
    ∫ z, a z * b z = ⟪ha.star.toLp (star a), hb.toLp b⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.star.coeFn_toLp, hb.coeFn_toLp] with z h1 h2
  rw [h1, h2, RCLike.inner_apply, Pi.star_apply]
  simp only [RCLike.star_def, Complex.conj_conj]
  ring

theorem norm_toLp_star {a : ℝ × ℝ → ℂ} (ha : MemLp a 2 volume) :
    ‖ha.star.toLp (star a)‖ = ‖ha.toLp a‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  refine eLpNorm_congr_norm_ae (Eventually.of_forall fun z => ?_)
  simp [Pi.star_apply]

/-- Cauchy–Schwarz: `|∫ a b| ≤ ‖a‖_{L²} ‖b‖_{L²}`. -/
theorem norm_integral_mul_le {a b : ℝ × ℝ → ℂ} (ha : MemLp a 2 volume)
    (hb : MemLp b 2 volume) : ‖∫ z, a z * b z‖ ≤ ‖ha.toLp a‖ * ‖hb.toLp b‖ := by
  rw [integral_mul_eq_inner ha hb, ← norm_toLp_star ha]
  exact norm_inner_le_norm _ _

/-! ## Test functions of temperate growth -/

/-- `√G Ψ` for `Ψ` of temperate growth, as a Schwartz function. -/
def wS (Ψ : ℝ × ℝ → ℂ) (hΨ : Ψ.HasTemperateGrowth) : S2 :=
  ((B0093.sqrtConst : ℝ) : ℂ) •
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) hΨ gaussS

theorem wS_apply (Ψ : ℝ × ℝ → ℂ) (hΨ : Ψ.HasTemperateGrowth) (z : ℝ × ℝ) :
    wS Ψ hΨ z = sqGc z * Ψ z := by
  rw [wS, smul_apply, SchwartzMap.bilinLeftCLM_apply]
  simp only [ContinuousLinearMap.lsmul_apply, sqGc, sqG_eq, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- `F Ψ = (U_G F) (√G Ψ)`. -/
theorem mul_eq_conjG_mul (F Ψ : ℝ × ℝ → ℂ) (hΨ : Ψ.HasTemperateGrowth) (z : ℝ × ℝ) :
    F z * Ψ z = B0093.conjG F z * wS Ψ hΨ z := by
  rw [wS_apply]
  conv_lhs => rw [← sqGc_mul_conjG F z]
  ring

/-- A function of `L²(ℝ², G⁻¹ dy)` times a function of temperate growth is integrable. -/
theorem integrable_mul_temperate {F : ℝ × ℝ → ℂ} (hF : MemGaussL2 F) {Ψ : ℝ × ℝ → ℂ}
    (hΨ : Ψ.HasTemperateGrowth) : Integrable (fun z => F z * Ψ z) volume := by
  have h := integrable_mul_of_memLp hF ((wS Ψ hΨ).memLp 2 volume)
  refine h.congr (Eventually.of_forall fun z => ?_)
  exact (mul_eq_conjG_mul F Ψ hΨ z).symm

/-- Bound for the pairing of a Gaussian-`L²` function with a temperate test function. -/
theorem norm_integral_mul_temperate_le {F : ℝ × ℝ → ℂ} (hF : MemGaussL2 F) {Ψ : ℝ × ℝ → ℂ}
    (hΨ : Ψ.HasTemperateGrowth) :
    ‖∫ z, F z * Ψ z‖ ≤ ‖hF.toLp (B0093.conjG F)‖ * ‖J (wS Ψ hΨ)‖ := by
  have e : ∫ z, F z * Ψ z = ∫ z, B0093.conjG F z * wS Ψ hΨ z :=
    integral_congr_ae (Eventually.of_forall fun z => mul_eq_conjG_mul F Ψ hΨ z)
  rw [e]
  refine (norm_integral_mul_le hF ((wS Ψ hΨ).memLp 2 volume)).trans (le_of_eq ?_)
  rfl

theorem hasTemperateGrowth_fderiv {Φ : ℝ × ℝ → ℂ} (hΦ : Φ.HasTemperateGrowth) :
    (fderiv ℝ Φ).HasTemperateGrowth := by
  refine ⟨ContDiff.fderiv_right (m := ∞) hΦ.1 (by simp), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hΦ.2 (n + 1)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact h x⟩

theorem hasTemperateGrowth_dirDeriv {Φ : ℝ × ℝ → ℂ} (hΦ : Φ.HasTemperateGrowth) (v : ℝ × ℝ) :
    (dirDeriv v Φ).HasTemperateGrowth := by
  have h := (ContinuousLinearMap.apply ℝ ℂ v).hasTemperateGrowth.comp
    (hasTemperateGrowth_fderiv hΦ)
  exact h

theorem hasTemperateGrowth_conj {P : ℝ × ℝ → ℂ} (hP : P.HasTemperateGrowth) :
    (fun z => conj (P z)).HasTemperateGrowth :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasTemperateGrowth.comp hP

theorem dirDeriv_conj {P : ℝ × ℝ → ℂ} (hP : P.HasTemperateGrowth) (v z : ℝ × ℝ) :
    dirDeriv v (fun z => conj (P z)) z = conj (dirDeriv v P z) := by
  have hd : DifferentiableAt ℝ P z := (hP.1.differentiable (by simp)) z
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hd.hasFDerivAt
  show fderiv ℝ (⇑(Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ P) z v = _
  rw [h.fderiv]
  rfl

/-! ## Extension of a first-order weak derivative to test functions of temperate growth -/

/-- The cutoff `b(y/(n+1))` with a fixed bump `b = 1` on the unit ball. -/
def bump : ContDiffBump (0 : ℝ × ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- `cutoff n y = b(y/(n+1))`. -/
def cutoff (n : ℕ) (z : ℝ × ℝ) : ℂ := ((bump (((n : ℝ) + 1)⁻¹ • z) : ℝ) : ℂ)

theorem cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  Complex.ofRealCLM.contDiff.comp (bump.contDiff.comp (contDiff_id.const_smul _))

theorem cutoff_hasCompactSupport (n : ℕ) : HasCompactSupport (cutoff n) := by
  have hc : ((n : ℝ) + 1)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  exact (bump.hasCompactSupport.comp_smul hc).comp_left Complex.ofReal_zero

theorem norm_cutoff_le (n : ℕ) (z : ℝ × ℝ) : ‖cutoff n z‖ ≤ 1 := by
  rw [cutoff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg bump.nonneg]
  exact bump.le_one

theorem dirDeriv_cutoff (n : ℕ) (v z : ℝ × ℝ) :
    dirDeriv v (cutoff n) z =
      ((fderiv ℝ bump (((n : ℝ) + 1)⁻¹ • z) (((n : ℝ) + 1)⁻¹ • v) : ℝ) : ℂ) := by
  have hb : DifferentiableAt ℝ bump (((n : ℝ) + 1)⁻¹ • z) :=
    (bump.contDiff (n := 1)).differentiable (by simp) _
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => ((n : ℝ) + 1)⁻¹ • y)
      (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)) z :=
    (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)).hasFDerivAt
  have h2 := Complex.ofRealCLM.hasFDerivAt.comp z (hb.hasFDerivAt.comp z h1)
  show fderiv ℝ (cutoff n) z v = _
  have e : cutoff n = Complex.ofRealCLM ∘ (bump ∘ fun y : ℝ × ℝ => ((n : ℝ) + 1)⁻¹ • y) := rfl
  rw [e, h2.fderiv]
  simp

theorem exists_bound_fderiv_bump : ∃ K : ℝ, ∀ y : ℝ × ℝ, ‖fderiv ℝ bump y‖ ≤ K :=
  ((bump.contDiff (n := 1)).continuous_fderiv (by simp)).bounded_above_of_compact_support
    (bump.hasCompactSupport.fderiv ℝ)

theorem tendsto_inv_succ : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by rw [one_div]

theorem eventually_cutoff_eq_one (z : ℝ × ℝ) : ∀ᶠ n : ℕ in atTop, cutoff n z = 1 := by
  have h : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1)⁻¹ * ‖z‖ ≤ 1 := by
    have := (tendsto_inv_succ.mul_const ‖z‖)
    rw [zero_mul] at this
    exact this.eventually (ge_mem_nhds one_pos)
  filter_upwards [h] with n hn
  rw [cutoff, bump.one_of_mem_closedBall, Complex.ofReal_one]
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (n : ℝ) + 1))]
  exact hn

theorem tendsto_dirDeriv_cutoff (v z : ℝ × ℝ) :
    Tendsto (fun n => dirDeriv v (cutoff n) z) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_bound_fderiv_bump
  have hb : ∀ n : ℕ, ‖dirDeriv v (cutoff n) z‖ ≤ K * ‖v‖ * ((n : ℝ) + 1)⁻¹ := by
    intro n
    rw [dirDeriv_cutoff, Complex.norm_real]
    calc ‖fderiv ℝ bump (((n : ℝ) + 1)⁻¹ • z) (((n : ℝ) + 1)⁻¹ • v)‖
        ≤ ‖fderiv ℝ bump (((n : ℝ) + 1)⁻¹ • z)‖ * ‖((n : ℝ) + 1)⁻¹ • v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * (((n : ℝ) + 1)⁻¹ * ‖v‖) := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (n : ℝ) + 1))]
          exact mul_le_mul_of_nonneg_right (hK _) (by positivity)
      _ = K * ‖v‖ * ((n : ℝ) + 1)⁻¹ := by ring
  refine squeeze_zero_norm hb ?_
  have := tendsto_inv_succ.const_mul (K * ‖v‖)
  rwa [mul_zero] at this

theorem norm_dirDeriv_cutoff_le (v z : ℝ × ℝ) {K : ℝ} (hK : ∀ y : ℝ × ℝ, ‖fderiv ℝ bump y‖ ≤ K)
    (n : ℕ) : ‖dirDeriv v (cutoff n) z‖ ≤ K * ‖v‖ := by
  rw [dirDeriv_cutoff, Complex.norm_real]
  have hc : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
  have hc0 : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  calc ‖fderiv ℝ bump (((n : ℝ) + 1)⁻¹ • z) (((n : ℝ) + 1)⁻¹ • v)‖
      ≤ ‖fderiv ℝ bump (((n : ℝ) + 1)⁻¹ • z)‖ * ‖((n : ℝ) + 1)⁻¹ • v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
        refine mul_le_mul (hK _) ?_ (by positivity) hK0
        calc ((n : ℝ) + 1)⁻¹ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
          _ = ‖v‖ := one_mul _

/-- **Temperate test functions.** If `u, u' ∈ L²(ℝ², G⁻¹ dy)` and `u' = ∂_v u` weakly
(`∫ u ∂_v φ = -∫ u' φ` for all smooth compactly supported `φ`), the same identity holds for
every test function `Φ` of temperate growth. -/
theorem integral_dirDeriv_temperate {u u' : ℝ × ℝ → ℂ} (hu : MemGaussL2 u)
    (hu' : MemGaussL2 u') (v : ℝ × ℝ)
    (h : ∀ φ : ℝ × ℝ → ℂ, IsTestFn univ φ →
      ∫ z, u z * dirDeriv v φ z = -∫ z, u' z * φ z)
    {Φ : ℝ × ℝ → ℂ} (hΦ : Φ.HasTemperateGrowth) :
    ∫ z, u z * dirDeriv v Φ z = -∫ z, u' z * Φ z := by
  obtain ⟨K, hK⟩ := exists_bound_fderiv_bump
  set φn : ℕ → ℝ × ℝ → ℂ := fun n z => Φ z * cutoff n z with hφn
  have htest : ∀ n, IsTestFn univ (φn n) := fun n =>
    ⟨hΦ.1.mul (cutoff_contDiff n), (cutoff_hasCompactSupport n).mul_left, subset_univ _⟩
  have hd : ∀ n z, dirDeriv v (φn n) z =
      dirDeriv v Φ z * cutoff n z + Φ z * dirDeriv v (cutoff n) z := by
    intro n z
    have h1 : DifferentiableAt ℝ Φ z := (hΦ.1.differentiable (by simp)) z
    have h2 : DifferentiableAt ℝ (cutoff n) z := ((cutoff_contDiff n).differentiable (by simp)) z
    have hm : HasFDerivAt (fun y => Φ y * cutoff n y)
        (Φ z • fderiv ℝ (cutoff n) z + cutoff n z • fderiv ℝ Φ z) z :=
      h1.hasFDerivAt.mul h2.hasFDerivAt
    show fderiv ℝ (fun y => Φ y * cutoff n y) z v = _
    rw [hm.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp only [dirDeriv]
    ring
  have hΦ' := hasTemperateGrowth_dirDeriv hΦ v
  have i1 := integrable_mul_temperate hu hΦ'
  have i2 := integrable_mul_temperate hu hΦ
  have i3 := integrable_mul_temperate hu' hΦ
  -- first integral
  have lim1 : Tendsto (fun n => ∫ z, u z * dirDeriv v (φn n) z) atTop
      (𝓝 (∫ z, u z * dirDeriv v Φ z)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun z => ‖u z * dirDeriv v Φ z‖ + K * ‖v‖ * ‖u z * Φ z‖) (fun n => ?_)
      (i1.norm.add (i2.norm.const_mul _)) (fun n => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => ?_)
    · refine hu.aestronglyMeasurable.mul ?_
      exact (contDiff_dirDeriv (htest n).smooth v).continuous.aestronglyMeasurable
    · rw [hd, mul_add]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [← mul_assoc, norm_mul _ (cutoff n z)]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_cutoff_le n z)
      · rw [← mul_assoc, norm_mul _ (dirDeriv v (cutoff n) z)]
        calc ‖u z * Φ z‖ * ‖dirDeriv v (cutoff n) z‖ ≤ ‖u z * Φ z‖ * (K * ‖v‖) :=
              mul_le_mul_of_nonneg_left (norm_dirDeriv_cutoff_le v z hK n) (norm_nonneg _)
          _ = K * ‖v‖ * ‖u z * Φ z‖ := by ring
    · have hc : Tendsto (fun n => cutoff n z) atTop (𝓝 1) :=
        tendsto_const_nhds.congr' ((eventually_cutoff_eq_one z).mono fun n hn => hn.symm)
      have := ((hc.const_mul (dirDeriv v Φ z)).add
        ((tendsto_dirDeriv_cutoff v z).const_mul (Φ z))).const_mul (u z)
      simp only [mul_one, mul_zero, add_zero] at this
      refine this.congr fun n => ?_
      rw [hd]
  -- second integral
  have lim2 : Tendsto (fun n => ∫ z, u' z * φn n z) atTop (𝓝 (∫ z, u' z * Φ z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖u' z * Φ z‖) (fun n => ?_)
      i3.norm (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
    · exact hu'.aestronglyMeasurable.mul (htest n).continuous.aestronglyMeasurable
    · simp only [hφn, norm_mul]
      calc ‖u' z‖ * (‖Φ z‖ * ‖cutoff n z‖) ≤ ‖u' z‖ * (‖Φ z‖ * 1) := by
            gcongr
            exact norm_cutoff_le n z
        _ = ‖u' z‖ * ‖Φ z‖ := by ring
    · have hc : Tendsto (fun n => cutoff n z) atTop (𝓝 1) :=
        tendsto_const_nhds.congr' ((eventually_cutoff_eq_one z).mono fun n hn => hn.symm)
      have := (hc.const_mul (Φ z)).const_mul (u' z)
      simp only [mul_one] at this
      exact this
  have e : ∀ n, ∫ z, u z * dirDeriv v (φn n) z = -∫ z, u' z * φn n z :=
    fun n => h _ (htest n)
  have lim1' : Tendsto (fun n => ∫ z, u z * dirDeriv v (φn n) z) atTop
      (𝓝 (-∫ z, u' z * Φ z)) := by
    have := lim2.neg
    exact this.congr fun n => (e n).symm
  exact tendsto_nhds_unique lim1 lim1'

/-! ## Schwartz functions of the form `√G × (temperate)` -/

/-- `ζ = √G P` with `P` of temperate growth (the conjugated Hermite functions and their
images under the ladder operators: polynomials times `e^{-|y|²/8}`). -/
def IsGP (ζ : S2) : Prop := ∃ P : ℝ × ℝ → ℂ, P.HasTemperateGrowth ∧ ∀ z, ζ z = sqGc z * P z

theorem IsGP.conjG_eq {ζ : S2} {P : ℝ × ℝ → ℂ} (h : ∀ z, ζ z = sqGc z * P z) (z : ℝ × ℝ) :
    B0093.conjG ⇑ζ z = P z := by
  rw [conjG_apply, h, sqGc, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (sqG_pos z).ne',
    Complex.ofReal_one, one_mul]

theorem dop_of_eq {ζ : S2} {P : ℝ × ℝ → ℂ} (hP : P.HasTemperateGrowth)
    (h : ∀ z, ζ z = sqGc z * P z) (i : Fin 2) (z : ℝ × ℝ) :
    dop i ζ z = sqGc z * (dirDeriv (ev i) P z - crdC i z / 4 * P z) := by
  have hf : ⇑ζ = sqGc * P := by
    funext y
    rw [h, Pi.mul_apply]
  have hd : DifferentiableAt ℝ P z := (hP.1.differentiable (by simp)) z
  have hm := (hasFDerivAt_sqGc z).mul hd.hasFDerivAt
  rw [dop_apply, hf, hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← (hasFDerivAt_sqGc z).fderiv, fderiv_sqGc_ev]
  simp only [dirDeriv]
  ring

theorem Bop_of_eq {ζ : S2} {P : ℝ × ℝ → ℂ} (hP : P.HasTemperateGrowth)
    (h : ∀ z, ζ z = sqGc z * P z) (i : Fin 2) (z : ℝ × ℝ) :
    Bop i ζ z = sqGc z * (-dirDeriv (ev i) P z) := by
  rw [Bop_apply, sub_apply, neg_apply, smul_apply, X_apply, dop_of_eq hP h, h, smul_eq_mul]
  ring

theorem Aop_of_eq {ζ : S2} {P : ℝ × ℝ → ℂ} (hP : P.HasTemperateGrowth)
    (h : ∀ z, ζ z = sqGc z * P z) (i : Fin 2) (z : ℝ × ℝ) :
    Aop i ζ z = sqGc z * (dirDeriv (ev i) P z - crdC i z / 2 * P z) := by
  rw [Aop_apply, sub_apply, smul_apply, X_apply, dop_of_eq hP h, h, smul_eq_mul]
  ring

theorem IsGP.Bop {ζ : S2} (hζ : IsGP ζ) (i : Fin 2) : IsGP (Bop i ζ) := by
  obtain ⟨P, hP, h⟩ := hζ
  exact ⟨fun z => -dirDeriv (ev i) P z, (hasTemperateGrowth_dirDeriv hP (ev i)).neg,
    Bop_of_eq hP h i⟩

theorem IsGP.Aop {ζ : S2} (hζ : IsGP ζ) (i : Fin 2) : IsGP (Aop i ζ) := by
  obtain ⟨P, hP, h⟩ := hζ
  refine ⟨fun z => dirDeriv (ev i) P z - crdC i z / 2 * P z, ?_, Aop_of_eq hP h i⟩
  refine (hasTemperateGrowth_dirDeriv hP (ev i)).sub ?_
  have h2 : (fun z => crdC i z / 2 * P z) = (fun z => crdC i z * (2⁻¹ : ℂ)) * P := by
    funext z
    simp only [Pi.mul_apply]
    ring
  rw [h2]
  exact ((hasTemperateGrowth_crdC i).mul (Function.HasTemperateGrowth.const _)).mul hP

theorem IsGP.add {ζ η : S2} (hζ : IsGP ζ) (hη : IsGP η) : IsGP (ζ + η) := by
  obtain ⟨P, hP, h⟩ := hζ
  obtain ⟨Q, hQ, h'⟩ := hη
  exact ⟨P + Q, hP.add hQ, fun z => by rw [add_apply, h, h', Pi.add_apply]; ring⟩

theorem IsGP.smul {ζ : S2} (hζ : IsGP ζ) (c : ℂ) : IsGP (c • ζ) := by
  obtain ⟨P, hP, h⟩ := hζ
  exact ⟨(fun _ => c) * P, (Function.HasTemperateGrowth.const _).mul hP,
    fun z => by rw [smul_apply, h, Pi.mul_apply, smul_eq_mul]; ring⟩

theorem IsGP.zero : IsGP (0 : S2) :=
  ⟨0, Function.HasTemperateGrowth.zero, fun z => by simp⟩

theorem IsGP.sum {ι : Type*} (s : Finset ι) (ζ : ι → S2) (h : ∀ i ∈ s, IsGP (ζ i)) :
    IsGP (∑ i ∈ s, ζ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsGP.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IsGP.Aw {ζ : S2} (hζ : IsGP ζ) (k : ℕ) (w : Fin k → Fin 2) : IsGP (Aw k w ζ) := by
  induction k with
  | zero => exact hζ
  | succ k ih => rw [Aw_succ]; exact (ih _).Aop _

theorem IsGP.Bw {k : ℕ} (w : Fin k → Fin 2) {ζ : S2} (hζ : IsGP ζ) : IsGP (Bw k w ζ) := by
  induction k generalizing ζ with
  | zero => exact hζ
  | succ k ih => rw [Bw_succ]; exact ih _ (hζ.Bop _)

/-- The core functions `coreS p = U_G (r² p(r²) e^{-r²/4} e^{2iϑ})` of B0094. -/
theorem isGP_coreS (p : Polynomial ℂ) : IsGP (coreS p) := by
  refine ⟨fun z => corePoly p z * ((B0093.sqrtConst⁻¹ : ℝ) : ℂ),
    (hasTemperateGrowth_corePoly p).mul (Function.HasTemperateGrowth.const _), fun z => ?_⟩
  simp only [coreS_apply, sqGc, sqG_eq, gaussS_apply, corePoly]
  have hc : (B0093.sqrtConst : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 B0093.sqrtConst_pos.ne'
  push_cast
  field_simp

/-- **One step of moving derivatives to the test side.** If `g' = ∂ᵢ g` weakly and `η = √G P`,
then `∫ g' conj(U_G η) = ∫ g conj(U_G (Bᵢ η))`. -/
theorem integral_peel {g g' : ℝ × ℝ → ℂ} (hg : MemGaussL2 g) (hg' : MemGaussL2 g') (i : Fin 2)
    (h : ∀ φ : ℝ × ℝ → ℂ, IsTestFn univ φ →
      ∫ z, g z * dirDeriv (ev i) φ z = -∫ z, g' z * φ z)
    {η : S2} (hη : IsGP η) :
    ∫ z, g' z * conj (B0093.conjG ⇑η z) = ∫ z, g z * conj (B0093.conjG ⇑(Bop i η) z) := by
  obtain ⟨P, hP, hηP⟩ := hη
  have hB : ∀ z, Bop i η z = sqGc z * (-dirDeriv (ev i) P z) := Bop_of_eq hP hηP i
  have e1 : ∀ z, conj (B0093.conjG ⇑η z) = conj (P z) := fun z => by
    rw [IsGP.conjG_eq hηP]
  have e2 : ∀ z, conj (B0093.conjG ⇑(Bop i η) z) = -dirDeriv (ev i) (fun z => conj (P z)) z :=
    fun z => by rw [IsGP.conjG_eq hB, dirDeriv_conj hP, map_neg]
  simp_rw [e1, e2, mul_neg]
  rw [integral_neg, integral_dirDeriv_temperate hg hg' (ev i) h (hasTemperateGrowth_conj hP),
    neg_neg]

end UnforcedLeray.B0121
