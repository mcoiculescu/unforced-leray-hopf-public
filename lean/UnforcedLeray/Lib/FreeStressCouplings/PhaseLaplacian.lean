import UnforcedLeray.Lib.FreeStressCouplings.ProdLp
import UnforcedLeray.Lib.FreeStressCouplings.LaplacianDomain
import UnforcedLeray.Lib.PhaseSpace.Test

/-!
# `A = -νΔ` diagonalised on `Y₂ = L²(ℝ/Pℤ; L²(ℝ³; ℂ³))` (INF10 F1, part A)


§4 bypass **B9** ("`A = -νΔ` is diagonalized by the `L²` Fourier transform on `ℝ³`") and §5
Level F, target **F1**; blueprint units **B0459** (tex 7698-7722: `A = -νΔ` on the unrestricted
`Y₂`), **B0473** (tex 7774-7788) and **B0474** (tex 7789: `D₀ = 1 + A`).

The phase space is `Yq P 2 = Lp (Lp CVec3 2 volume) 2 haarAddCircle` (decision D2,
`Lib/PhaseSpace/Test.lean`).  `A` acts in the spatial variable only.  Its diagonalising unitary
`phaseFourier P` is the fibrewise `L²` Fourier transform followed by the Fubini isometry
`prodLpEquiv` (`ProdLp.lean`); the symbol is `ν (2π)² |ξ|²` on `(ℝ/Pℤ) × ℝ³`.

* `fiberLp e`: fibrewise application of a unitary on a Bochner `L^p` space;
* `laplaceRepY P ν hν`: the `MulRep` of `A` on `Y₂`;
* `laplaceRepY_hasPow_iff`: `A^s x = y` on `Y₂` iff `A^s x(τ) = y(τ)` on `L²(ℝ³)` for a.e.
  phase `τ` (every real power `s`);
* `laplaceRepY_hasPow_one_iff`: `A x = y` iff `-νΔ x(τ) = y(τ)` in `𝓢'(ℝ³; ℂ³)` for a.e. `τ`.
  So the domain of `A` is the distributional graph `{x ∈ Y₂ : νΔx ∈ Y₂}` of tex 7320-7330 in
  its fibrewise form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory SchwartzMap FourierTransform Filter
open scoped ENNReal Laplacian

namespace UnforcedLeray.FreeStress

open UnforcedLeray.PhaseSpace

section Fiber

variable {β : Type*} [MeasurableSpace β] {m : Measure β} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup H']
  [NormedSpace ℂ H']

/-- Fibrewise application of a linear isometry equivalence `e : H ≃ H'` on `L^p(m; H)`. -/
def fiberLp (e : H ≃ₗᵢ[ℂ] H') : Lp H p m ≃ₗᵢ[ℂ] Lp H' p m where
  toFun := e.toLinearIsometry.toContinuousLinearMap.compLpL p m
  invFun := e.symm.toLinearIsometry.toContinuousLinearMap.compLpL p m
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv f := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL e.symm.toLinearIsometry.toContinuousLinearMap
      (e.toLinearIsometry.toContinuousLinearMap.compLpL p m f),
      ContinuousLinearMap.coeFn_compLpL e.toLinearIsometry.toContinuousLinearMap f] with a h1 h2
    rw [h1, h2]
    simp
  right_inv g := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL e.toLinearIsometry.toContinuousLinearMap
      (e.symm.toLinearIsometry.toContinuousLinearMap.compLpL p m g),
      ContinuousLinearMap.coeFn_compLpL e.symm.toLinearIsometry.toContinuousLinearMap g]
      with a h1 h2
    rw [h1, h2]
    simp
  norm_map' f := by
    change ‖e.toLinearIsometry.toContinuousLinearMap.compLpL p m f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae
    filter_upwards [ContinuousLinearMap.coeFn_compLpL e.toLinearIsometry.toContinuousLinearMap f]
      with a h
    rw [h]
    simp

theorem fiberLp_ae (e : H ≃ₗᵢ[ℂ] H') (f : Lp H p m) :
    (fiberLp e f : β → H') =ᵐ[m] fun a => e (f a) :=
  ContinuousLinearMap.coeFn_compLpL e.toLinearIsometry.toContinuousLinearMap f

end Fiber

variable (P : ℝ) [Fact (0 < P)]

/-- The normalised phase measure times Lebesgue measure on `(ℝ/Pℤ) × ℝ³`. -/
abbrev phaseVol : Measure (AddCircle P × Space) :=
  (AddCircle.haarAddCircle (T := P)).prod (volume : Measure Space)

/-- The diagonalising unitary of `A` on `Y₂`: the fibrewise `L²` Fourier transform in `y`,
then the Fubini isometry onto `L²((ℝ/Pℤ) × ℝ³)`. -/
def phaseFourier : Yq P 2 ≃ₗᵢ[ℂ] Lp CVec3 2 (phaseVol P) :=
  (fiberLp (Lp.fourierTransformₗᵢ Space CVec3)).trans prodLpEquiv.symm

/-- For a.e. phase, the slice of `phaseFourier P x` is the Fourier transform of `x(τ)`. -/
theorem phaseFourier_slice_ae (x : Yq P 2) :
    ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
      (fun ξ => (phaseFourier P x : AddCircle P × Space → CVec3) (τ, ξ)) =ᵐ[volume]
        (Lp.fourierTransformₗᵢ Space CVec3 (x τ) : Space → CVec3) := by
  filter_upwards [prodLpEquiv_symm_ae (ν := AddCircle.haarAddCircle (T := P))
      (fiberLp (p := 2) (Lp.fourierTransformₗᵢ Space CVec3) x),
    fiberLp_ae (p := 2) (Lp.fourierTransformₗᵢ Space CVec3) x] with τ h1 h2
  refine h1.trans ?_
  rw [h2]

/-- **`A = -νΔ` on `Y₂`, diagonalised** (bypass B9): unitary `phaseFourier P`, symbol
`ν (2π)² |ξ|²` on `(ℝ/Pℤ) × ℝ³`. -/
def laplaceRepY (ν : ℝ) (hν : 0 ≤ ν) : MulRep (Yq P 2) (phaseVol P) CVec3 where
  U := phaseFourier P
  sym z := laplaceSym ν z.2
  measurable_sym := by unfold laplaceSym; fun_prop
  sym_nonneg z := mul_nonneg hν (by positivity)

/-- **`A^s` acts fibrewise in the phase**: `A^s x = y` on `Y₂` iff, for a.e. phase `τ`,
`A^s x(τ) = y(τ)` for the Fourier representation of `-νΔ` on `L²(ℝ³; ℂ³)`. -/
theorem laplaceRepY_hasPow_iff (ν : ℝ) (hν : 0 ≤ ν) (s : ℝ) (x y : Yq P 2) :
    (laplaceRepY P ν hν).HasPow s x y ↔
      ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)), (laplaceRep ν hν).HasPow s (x τ) (y τ) := by
  set X := phaseFourier P x
  set Yv := phaseFourier P y
  have hc : AEStronglyMeasurable
      (fun z : AddCircle P × Space => ((laplaceSym ν z.2 ^ s : ℝ) : ℂ) • X z) (phaseVol P) := by
    have hm : Measurable fun z : AddCircle P × Space => ((laplaceSym ν z.2 ^ s : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((laplaceRepY P ν hν).measurable_sym.pow_const s)
    exact hm.aestronglyMeasurable.smul (Lp.aestronglyMeasurable X)
  change (Yv : AddCircle P × Space → CVec3) =ᵐ[phaseVol P]
    (fun z : AddCircle P × Space => ((laplaceSym ν z.2 ^ s : ℝ) : ℂ) • X z) ↔ _
  rw [ae_eq_prod_iff (Lp.aestronglyMeasurable Yv) hc]
  constructor
  · intro h
    filter_upwards [h, phaseFourier_slice_ae P x, phaseFourier_slice_ae P y] with τ h1 hx hy
    change ∀ᵐ ξ ∂(volume : Measure Space),
      (Lp.fourierTransformₗᵢ Space CVec3 (y τ) : Space → CVec3) ξ =
        ((laplaceSym ν ξ ^ s : ℝ) : ℂ) •
          (Lp.fourierTransformₗᵢ Space CVec3 (x τ) : Space → CVec3) ξ
    filter_upwards [h1, hx, hy] with ξ e1 e2 e3
    rw [← e3, ← e2]
    exact e1
  · intro h
    filter_upwards [h, phaseFourier_slice_ae P x, phaseFourier_slice_ae P y] with τ h1 hx hy
    have h1' : ∀ᵐ ξ ∂(volume : Measure Space),
        (Lp.fourierTransformₗᵢ Space CVec3 (y τ) : Space → CVec3) ξ =
          ((laplaceSym ν ξ ^ s : ℝ) : ℂ) •
            (Lp.fourierTransformₗᵢ Space CVec3 (x τ) : Space → CVec3) ξ := h1
    filter_upwards [h1', hx, hy] with ξ e1 e2 e3
    change (phaseFourier P y : AddCircle P × Space → CVec3) (τ, ξ) =
      ((laplaceSym ν ξ ^ s : ℝ) : ℂ) • (phaseFourier P x : AddCircle P × Space → CVec3) (τ, ξ)
    rw [e3, e2]
    exact e1

/-- **The domain of `A` on `Y₂` is the fibrewise distributional graph** (B0459, B0473; tex
7320-7330): `A x = y` iff `-νΔ x(τ) = y(τ)` in `𝓢'(ℝ³; ℂ³)` for a.e. phase `τ`. -/
theorem laplaceRepY_hasPow_one_iff (ν : ℝ) (hν : 0 ≤ ν) (x y : Yq P 2) :
    (laplaceRepY P ν hν).HasPow 1 x y ↔
      ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
        (-(ν : ℂ)) • Δ ((x τ : Lp CVec3 2 (volume : Measure Space)) : 𝓢'(Space, CVec3)) =
          ((y τ : Lp CVec3 2 (volume : Measure Space)) : 𝓢'(Space, CVec3)) := by
  rw [laplaceRepY_hasPow_iff]
  simp_rw [laplaceRep_hasPow_one_iff]

/-- `D₀ = 1 + A` on `Y₂` (tex 7789). -/
abbrev phaseD0 (ν : ℝ) (hν : 0 ≤ ν) : MulRep (Yq P 2) (phaseVol P) CVec3 :=
  (laplaceRepY P ν hν).onePlus

end UnforcedLeray.FreeStress
