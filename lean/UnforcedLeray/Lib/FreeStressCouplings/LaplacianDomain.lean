import UnforcedLeray.Lib.FreeStressCouplings.FourierLaplacian
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The domain of `A = -νΔ` is the maximal distributional domain (INF10 F1, part A)


§4 bypass **B9** and §5 Level F, target **F1**; blueprint units **B0459** (tex 7704-7722) and
**B0473** (tex 7774-7788: the adjoint domain is exactly the distributional graph).

The manuscript's graph is distributional: `D_(ν,2) = {w ∈ Y₂ : νΔw ∈ Y₂, T₀w ∈ Y₂}`
(`eq:free-stress-1`, tex 7320-7326), with no boundary condition (tex 7328-7330).  This file
shows that the Fourier representation `laplaceRep ν` of `FourierLaplacian.lean` is exactly that
operator on `L²(V; F)`: for `x y ∈ L²`, `A x = y` in the representation iff `-νΔx = y` as
tempered distributions (`laplaceRep_hasPow_one_iff`).  So `dom A = {x ∈ L² : Δx ∈ L²}`.

Auxiliary: `smulLeft_toTemperedDistribution_eq_iff` (multiplication of an `L²` function by a
temperate symbol, read in `𝓢'`, determines the product a.e.).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory SchwartzMap FourierTransform Real
open scoped Laplacian ContDiff

namespace UnforcedLeray.FreeStress

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- For `g, h ∈ L²(V; F)` and a temperate symbol `σ`, `σ · g = h` in `𝓢'` iff `h = σ g` a.e. -/
theorem smulLeft_toTemperedDistribution_eq_iff {σ : V → ℂ} (hσ : σ.HasTemperateGrowth)
    (g h : Lp F 2 (volume : Measure V)) :
    TemperedDistribution.smulLeftCLM F σ (g : 𝓢'(V, F)) = (h : 𝓢'(V, F)) ↔
      (h : V → F) =ᵐ[volume] fun x => σ x • g x := by
  constructor
  · intro heq
    have hloc_h : LocallyIntegrable (h : V → F) volume :=
      (Lp.memLp h).locallyIntegrable one_le_two
    have hloc_g : LocallyIntegrable (fun x => σ x • (g : V → F) x) volume :=
      ((Lp.memLp g).locallyIntegrable one_le_two).continuous_smul hσ.1.continuous
    refine ae_eq_of_integral_contDiff_smul_eq hloc_h hloc_g fun φ hφ hφc => ?_
    have hφc' : HasCompactSupport (fun x => (φ x : ℂ)) := hφc.comp_left Complex.ofReal_zero
    have hφd : ContDiff ℝ ∞ (fun x => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    have hψx : ∀ x, (hφc'.toSchwartzMap hφd) x = (φ x : ℂ) := fun _ => rfl
    have h1 := congrArg (fun T : 𝓢'(V, F) => T (hφc'.toSchwartzMap hφd)) heq
    simp only [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
      SchwartzMap.smulLeftCLM_apply_apply hσ, hψx] at h1
    have e1 : ∀ x, (φ x : ℂ) • (h : V → F) x = φ x • (h : V → F) x := fun x =>
      Complex.coe_smul _ _
    have e2 : ∀ x, (σ x • (φ x : ℂ)) • (g : V → F) x = φ x • σ x • (g : V → F) x := fun x => by
      rw [smul_eq_mul, mul_comm, mul_smul, Complex.coe_smul]
    simp_rw [e1, e2] at h1
    exact h1.symm
  · intro hae
    ext ψ
    simp only [TemperedDistribution.smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
      SchwartzMap.smulLeftCLM_apply_apply hσ]
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx, smul_smul, smul_eq_mul, mul_comm, ← smul_smul]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The symbol of `A`, as a complex temperate function. -/
theorem hasTemperateGrowth_laplaceSym (ν : ℝ) :
    (fun ξ : V => ((laplaceSym ν ξ : ℝ) : ℂ)).HasTemperateGrowth := by
  unfold laplaceSym
  fun_prop

omit [CompleteSpace F] in
/-- `𝓕(-νΔ T) = (ν (2π)² |ξ|²) · 𝓕 T` for tempered distributions. -/
theorem fourier_neg_smul_laplacian (ν : ℝ) (T : 𝓢'(V, F)) :
    𝓕 ((-(ν : ℂ)) • Δ T) =
      TemperedDistribution.smulLeftCLM F (fun ξ : V => ((laplaceSym ν ξ : ℝ) : ℂ)) (𝓕 T) := by
  have hg : (fun x : V => Complex.ofReal (‖x‖ ^ 2)).HasTemperateGrowth := by fun_prop
  have hfun : (fun ξ : V => ((laplaceSym ν ξ : ℝ) : ℂ)) =
      ((ν : ℂ) * (2 * π) ^ 2) • fun x : V => Complex.ofReal (‖x‖ ^ 2) := by
    funext ξ
    simp only [laplaceSym, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hfun, TemperedDistribution.smulLeftCLM_smul hg,
    TemperedDistribution.laplacian_eq_fourierMultiplierCLM, FourierTransform.fourier_smul,
    ← Complex.coe_smul, FourierTransform.fourier_smul,
    TemperedDistribution.fourierMultiplierCLM_apply, fourier_fourierInv_eq, smul_smul,
    smul_apply]
  congr 1
  push_cast
  ring

/-- **`dom A` is the distributional domain** (B0459, B0473; tex 7320-7330): for `x y ∈ L²`,
`A x = y` in the Fourier representation iff `-νΔ x = y` in `𝓢'`. -/
theorem laplaceRep_hasPow_one_iff (ν : ℝ) (hν : 0 ≤ ν) (x y : Lp F 2 (volume : Measure V)) :
    (laplaceRep ν hν).HasPow 1 x y ↔
      (-(ν : ℂ)) • Δ (x : 𝓢'(V, F)) = (y : 𝓢'(V, F)) := by
  have hU : ∀ z : Lp F 2 (volume : Measure V), (laplaceRep ν hν).U z = 𝓕 z := fun _ => rfl
  have hiff : (-(ν : ℂ)) • Δ (x : 𝓢'(V, F)) = (y : 𝓢'(V, F)) ↔
      𝓕 ((-(ν : ℂ)) • Δ (x : 𝓢'(V, F))) = 𝓕 (y : 𝓢'(V, F)) := by
    constructor
    · intro h; rw [h]
    · intro h
      have := congrArg (fun T : 𝓢'(V, F) => 𝓕⁻ T) h
      simpa only [fourierInv_fourier_eq] using this
  rw [hiff, fourier_neg_smul_laplacian, Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq,
    smulLeft_toTemperedDistribution_eq_iff (hasTemperateGrowth_laplaceSym ν), ← hU, ← hU]
  unfold MulRep.HasPow
  simp only [Real.rpow_one]
  rfl

end UnforcedLeray.FreeStress
