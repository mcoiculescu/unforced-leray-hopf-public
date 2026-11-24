import UnforcedLeray.Units.B0581.Modes
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# B0581 helper: explicit horizontal Fourier coefficients

Blueprint unit **B0581** (`paper/main.tex` lines 9407–9412). The abstract coefficient map
`modes c` (the adjoint of the mode synthesis, `B0581/Modes.lean`) is identified with the
slice-wise Fourier coefficients of a field on the cell `[-c/2, c/2) × ℝ`:
`modes_apply_ae`:
`(modes ω)_k(η) = √c · ω_k(η)` for a.e. `η`, with
`ω_k(η) = modeCoeff c k ω η = c⁻¹ ∫_{-c/2}^{c/2} e^{-2πikq/c} ω(q, η) dq`.
In particular `ω_0(η) = ω̄(η) = c⁻¹ ∫ ω(q, η) dq` is the horizontal mean of line 9409
(`modeCoeff_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal NNReal InnerProductSpace Real ComplexConjugate

namespace UnforcedLeray.B0581

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The `k`-th horizontal Fourier coefficient
`ω_k(η) = c⁻¹ ∫_{-c/2}^{c/2} e^{-2πikq/c} ω(q, η) dq`. -/
def modeCoeff (c : ℝ) (k : ℤ) (f : B0579.Plane → F) (η : ℝ) : F :=
  ((c⁻¹ : ℝ) : ℂ) • ∫ q in qInt c, conj (eMode c k q) • f (q, η)

/-- The horizontal mean `ω̄(η) = ω_0(η) = c⁻¹ ∫_{-c/2}^{c/2} ω(q, η) dq`. -/
theorem modeCoeff_zero (c : ℝ) (f : B0579.Plane → F) (η : ℝ) :
    modeCoeff c 0 f η = ((c⁻¹ : ℝ) : ℂ) • ∫ q in qInt c, f (q, η) := by
  simp [modeCoeff, eMode_zero]

/-- The integrand `(√c)⁻¹ e^{-2πikq/c} ω(q, η)`. -/
def coeffIntegrand (c : ℝ) (k : ℤ) (f : B0579.Plane → F) (x : B0579.Plane) : F :=
  (((Real.sqrt c)⁻¹ : ℝ) : ℂ) • (conj (eMode c k x.1) • f x)

theorem integral_coeffIntegrand [CompleteSpace F] {c : ℝ} (hc : 0 < c) (k : ℤ)
    (f : B0579.Plane → F) (η : ℝ) :
    ∫ q in qInt c, coeffIntegrand c k f (q, η) =
      ((Real.sqrt c : ℝ) : ℂ) • modeCoeff c k f η := by
  rw [modeCoeff, smul_smul]
  simp only [coeffIntegrand]
  rw [integral_smul]
  congr 1
  rw [← Real.sqrt_div_self, div_eq_mul_inv]
  push_cast
  ring

theorem memLp_coeffIntegrand (c : ℝ) (k : ℤ) {f : B0579.Plane → F}
    (hf : MemLp f 2 ((μq c).prod volume)) :
    MemLp (coeffIntegrand c k f) 2 ((μq c).prod volume) := by
  refine (hf.const_smul (((Real.sqrt c)⁻¹ : ℝ) : ℂ)).of_le ?_
    (Eventually.of_forall fun x => ?_)
  · exact aestronglyMeasurable_const.smul ((((Complex.continuous_conj.comp
      (continuous_eMode c k)).comp continuous_fst).aestronglyMeasurable).smul hf.1)
  · simp only [coeffIntegrand, Pi.smul_apply, norm_smul, Function.comp_apply, Complex.norm_conj,
      norm_eMode, one_mul, le_refl]

theorem ae_cellVol (c : ℝ) : ae (cellVol c) = ae ((μq c).prod (volume : Measure ℝ)) := by
  rw [cellVol_eq]

theorem integral_cellVol (c : ℝ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : B0579.Plane → E) :
    ∫ x, G x ∂cellVol c = ∫ x, G x ∂((μq c).prod (volume : Measure ℝ)) := by
  rw [cellVol_eq]

theorem prod_restrict_snd (c : ℝ) (s : Set ℝ) :
    (μq c).prod (volume.restrict s) = ((μq c).prod volume).restrict (univ ×ˢ s) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

theorem integrable_coeffIntegrand (c : ℝ) (k : ℤ) {f : B0579.Plane → F}
    (hf : MemLp f 2 ((μq c).prod volume)) {s : Set ℝ} (hμs : volume s ≠ ∞) :
    Integrable (coeffIntegrand c k f) ((μq c).prod (volume.restrict s)) := by
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hμs
  have hle : (μq c).prod (volume.restrict s) ≤ (μq c).prod volume := by
    rw [prod_restrict_snd]
    exact Measure.restrict_le_self
  exact ((memLp_coeffIntegrand c k hf).mono_measure hle).integrable one_le_two

variable [CompleteSpace F]

theorem inner_tensorFun_indicator (c : ℝ) (k : ℤ) (s : Set ℝ) (v : F) (f : B0579.Plane → F)
    (x : B0579.Plane) :
    ⟪tensorFun c k (s.indicator fun _ => v) x, f x⟫_ℂ =
      (univ ×ˢ s).indicator (fun z => ⟪v, coeffIntegrand c k f z⟫_ℂ) x := by
  by_cases hx : x.2 ∈ s
  · have hx' : x ∈ (univ ×ˢ s : Set B0579.Plane) := ⟨mem_univ _, hx⟩
    rw [indicator_of_mem hx', tensorFun, indicator_of_mem hx, coeffIntegrand, inner_smul_left,
      inner_smul_right, inner_smul_right]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  · have hx' : x ∉ (univ ×ˢ s : Set B0579.Plane) := fun h => hx h.2
    rw [indicator_of_notMem hx', tensorFun, indicator_of_notMem hx, smul_zero, inner_zero_left]

/-- **Explicit horizontal Fourier coefficients.** For `ω ∈ L²(cell)`,
`(modes ω)_k(η) = ∫_{-c/2}^{c/2} (√c)⁻¹ e^{-2πikq/c} ω(q, η) dq` for a.e. `η`. -/
theorem modes_apply_ae_integral (c : ℝ) [hc : Fact (0 < c)] (k : ℤ)
    (ω : Lp F 2 (cellVol c)) :
    ((modes c ω : ModeSeq F) k : ℝ → F) =ᵐ[volume]
      fun η => ∫ q in qInt c, coeffIntegrand c k ω (q, η) := by
  have hf : MemLp (ω : B0579.Plane → F) 2 ((μq c).prod volume) := by
    rw [← cellVol_eq]; exact Lp.memLp ω
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ hμs => ?_)
    (fun s _ hμs => ?_) (fun s hs hμs => ?_)
  · exact integrableOn_Lp_of_measure_ne_top _ one_le_two hμs.ne
  · exact (integrable_coeffIntegrand c k hf hμs.ne).integral_prod_right
  · refine ext_inner_left ℂ fun v => ?_
    have hint := integrable_coeffIntegrand c k hf hμs.ne
    rw [← L2.inner_indicatorConstLp_eq_inner_setIntegral (𝕜 := ℂ) hs hμs.ne v, inner_modes_apply,
      L2.inner_def, ← integral_prod_symm _ hint, ← integral_inner hint v, prod_restrict_snd,
      ← integral_indicator (MeasurableSet.univ.prod hs)]
    have h1 := coeFn_tensorLM c k (indicatorConstLp 2 hs hμs.ne v)
    rw [EventuallyEq, ae_cellVol] at h1
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μq c)
      (ν := (volume : Measure ℝ))).ae_eq_comp (indicatorConstLp_coeFn (p := 2) (hs := hs)
        (hμs := hμs.ne) (c := v))
    rw [integral_cellVol]
    refine integral_congr_ae ?_
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Function.comp_apply] at hx2
    rw [tensorLI_apply, hx1]
    have : tensorFun c k (indicatorConstLp 2 hs hμs.ne v : ℝ → F) x =
        tensorFun c k (s.indicator fun _ => v) x := by
      simp only [tensorFun, hx2]
    rw [this, inner_tensorFun_indicator]

/-- **Explicit horizontal Fourier coefficients**, normalized form:
`(modes ω)_k = √c · ω_k` a.e., `ω_k(η) = c⁻¹ ∫ e^{-2πikq/c} ω(q, η) dq` (`modeCoeff`). -/
theorem modes_apply_ae (c : ℝ) [hc : Fact (0 < c)] (k : ℤ) (ω : Lp F 2 (cellVol c)) :
    ((modes c ω : ModeSeq F) k : ℝ → F) =ᵐ[volume]
      fun η => ((Real.sqrt c : ℝ) : ℂ) • modeCoeff c k ω η := by
  filter_upwards [modes_apply_ae_integral c k ω] with η h
  rw [h, integral_coeffIntegrand hc.out]

end UnforcedLeray.B0581
