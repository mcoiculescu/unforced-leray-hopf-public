import UnforcedLeray.Lib.FreeStressCouplings.Shift
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Concrete diagonalisation of `A = -νΔ` by the `L²` Fourier transform (INF10 F1, part A)


§4 bypass **B9** ("`A = -νΔ` is diagonalized by the `L²` Fourier transform on `ℝ³`, Mathlib
`Lp.fourierTransformₗᵢ`") and §5 Level F, target **F1**; blueprint units **B0459** (tex
7704-7722: `A = -νΔ`) and **B0474** (tex 7789: `D₀ = 1 + A`).

On `L²(V; F)` (`V` a finite-dimensional real inner product space, e.g. `ℝ³`; `F` a complex
Hilbert space, e.g. `ℂ³`), `laplaceRep ν` is the `MulRep` with unitary `𝓕` (Mathlib's
convention `𝓕 f(ξ) = ∫ e^{-2πi⟨x,ξ⟩} f(x) dx`) and symbol `ν (2π)² |ξ|² ≥ 0` (for `ν ≥ 0`).

* `fourier_laplacian_apply`: `𝓕(Δf)(ξ) = -(2π)²|ξ|² 𝓕f(ξ)` for Schwartz `f`;
* `laplaceRep_hasPow_one`: on Schwartz functions the represented operator is `-νΔ`;
* `laplaceRep_onePlus_hasPow_one`: on Schwartz functions `D₀ = 1 + A` acts as `f - νΔf`.

Scope: `L²(V; F)` only.  The manuscript's `A` acts on `Y₂ = L²(ℝ/Pℤ; L²(ℝ³))` fibrewise in the
phase; transporting this representation to `Y₂` needs the identification
`L²(ℝ/Pℤ; L²(ℝ³)) ≅ L²(ℝ/Pℤ × ℝ³)`, which is not built here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory SchwartzMap FourierTransform Real
open scoped Laplacian

namespace UnforcedLeray.FreeStress

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The symbol `ν (2π)² |ξ|²` of `A = -νΔ` in Mathlib's Fourier convention. -/
def laplaceSym (ν : ℝ) (ξ : V) : ℝ := ν * ((2 * π) ^ 2 * ‖ξ‖ ^ 2)

/-- `𝓕(Δ f)(ξ) = -(2π)² |ξ|² 𝓕 f(ξ)` for Schwartz `f`. -/
theorem fourier_laplacian_apply (f : 𝓢(V, F)) (ξ : V) :
    𝓕 (Δ f) ξ = (-((2 * π) ^ 2 * ‖ξ‖ ^ 2) : ℝ) • 𝓕 f ξ := by
  have hg : (fun x : V => ‖x‖ ^ 2).HasTemperateGrowth := by fun_prop
  rw [laplacian_eq_fourierMultiplierCLM, FourierTransform.fourier_smul,
    fourierMultiplierCLM_apply, fourier_fourierInv_eq, smul_apply,
    smulLeftCLM_apply_apply hg, smul_smul]
  congr 1
  ring

/-- **`A = -νΔ` diagonalised** (bypass B9): the `MulRep` on `L²(V; F)` with unitary the `L²`
Fourier transform and symbol `ν (2π)² |ξ|²`. -/
def laplaceRep (ν : ℝ) (hν : 0 ≤ ν) :
    MulRep (Lp F 2 (volume : Measure V)) (volume : Measure V) F where
  U := Lp.fourierTransformₗᵢ V F
  sym := laplaceSym ν
  measurable_sym := by unfold laplaceSym; fun_prop
  sym_nonneg := fun ξ => mul_nonneg hν (by positivity)

/-- On Schwartz functions, the operator represented by `laplaceRep ν` is `-νΔ`:
`A (f) = -ν Δ f`. -/
theorem laplaceRep_hasPow_one (ν : ℝ) (hν : 0 ≤ ν) (f : 𝓢(V, F)) :
    (laplaceRep ν hν).HasPow 1 (f.toLp 2) ((-(ν : ℂ)) • (Δ f).toLp 2) := by
  have h1 : (laplaceRep ν hν).U (f.toLp 2) = (𝓕 f).toLp 2 := SchwartzMap.toLp_fourier_eq f
  have h2 : (laplaceRep ν hν).U ((-(ν : ℂ)) • (Δ f).toLp 2) =
      (-(ν : ℂ)) • (𝓕 (Δ f)).toLp 2 := by
    rw [map_smul]
    congr 1
    exact SchwartzMap.toLp_fourier_eq (Δ f)
  unfold MulRep.HasPow
  rw [h1, h2]
  filter_upwards [Lp.coeFn_smul (-(ν : ℂ)) ((𝓕 (Δ f)).toLp 2), coeFn_toLp (𝓕 (Δ f)) 2 volume,
    coeFn_toLp (𝓕 f) 2 volume] with ξ ha hb hc
  rw [ha, Pi.smul_apply, hb, hc, fourier_laplacian_apply, Real.rpow_one, ← Complex.coe_smul,
    smul_smul]
  change _ = ((laplaceSym ν ξ : ℝ) : ℂ) • _
  congr 1
  unfold laplaceSym
  push_cast
  ring

/-- On Schwartz functions, `D₀ = 1 + A` acts as `f ↦ f - νΔf` (tex 7789). -/
theorem laplaceRep_onePlus_hasPow_one (ν : ℝ) (hν : 0 ≤ ν) (f : 𝓢(V, F)) :
    (laplaceRep ν hν).onePlus.HasPow 1 (f.toLp 2 volume)
      (f.toLp 2 volume + (-(ν : ℂ)) • (Δ f).toLp 2 volume) := by
  rw [MulRep.onePlus_hasPow_one_iff, add_sub_cancel_left]
  exact laplaceRep_hasPow_one ν hν f

end UnforcedLeray.FreeStress
