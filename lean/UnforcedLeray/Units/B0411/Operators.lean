import UnforcedLeray.Lib.PhaseSpace.Graph
import UnforcedLeray.Lib.PhaseSpace.CutoffCalc

/-!
# The operators `T₀`, `L₀` and their transposes (helper for B0411)

Blueprint unit B0411 (`eq:free-stress-1`), `paper/main.tex` lines 7318–7319:
`T₀ = ∂_τ − ½ y·∇` and `L₀ = T₀ − νΔ − ½`. In `Y_q` these operators act in distributions,
through their transposes on phase tests (`Lib/PhaseSpace/Ops.lean`: `driftT`, `lapT`,
`nuLapT`). This file defines the forward operators on smooth fields (`T0`, `L0`), the
transposes of the two summands of `T₀` (`dτT`, `radialTT`) and of `L₀` (`L0T`), and proves the
pointwise **Lagrange identities**

  `T₀ᵗΦ · u − Φ · T₀u = −∂_τ(Φ·u) + ½ ∑ⱼ ∂ⱼ(yⱼ Φ·u)`,
  `ΔΦ · u − Φ · Δu = ∑ⱼ ∂ⱼ(∂ⱼΦ·u − Φ·∂ⱼu)`,
  `L₀ᵗΦ · u − Φ · L₀u = −∂_τ(Φ·u) + ½ ∑ⱼ ∂ⱼ(yⱼ Φ·u) − ν ∑ⱼ ∂ⱼ(∂ⱼΦ·u − Φ·∂ⱼu)`,

with `a · b = ∑ᵢ aᵢ bᵢ` the bilinear dot product (`dotL`). They certify that `driftT` and
`L0T` are the formal transposes of `T₀` and `L₀`: the right-hand sides are `τ`- and
`y`-derivatives, which integrate to zero over one period and over `ℝ³` when `Φ` is a phase
test. The integration step itself is not carried out here.

Status: helper infrastructure for B0411; Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0411

open UnforcedLeray.PhaseSpace

/-! ### The operators -/

/-- The drift `T₀ = ∂_τ − ½ y·∇` on smooth fields (tex 7318). -/
def T0 (u : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun p => dτ u p - (1 / 2 : ℝ) • radialT u p

/-- `L₀ = T₀ − νΔ − ½` on smooth fields (tex 7319). -/
def L0 (ν : ℝ) (u : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun p => T0 u p - ν • lapT u p - (1 / 2 : ℝ) • u p

/-- The transpose of `∂_τ`: `Φ ↦ −∂_τ Φ`. -/
def dτT (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 := -dτ Φ

/-- The transpose of `y·∇`: `Φ ↦ −∇·(yΦ) = −y·∇Φ − 3Φ` (`div y = 3`). -/
def radialTT (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 := -radialT Φ - (3 : ℝ) • Φ

/-- The transpose of `L₀ = T₀ − νΔ − ½`: `Φ ↦ T₀ᵗΦ − νΔΦ − ½Φ`. -/
def L0T (ν : ℝ) (Φ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  driftT Φ - nuLapT ν Φ - (1 / 2 : ℝ) • Φ

/-- The transpose `driftT` of `T₀` is the combination `∂_τᵗ − ½ (y·∇)ᵗ` of the transposes of
its two summands. -/
theorem driftT_eq_transpose_parts (Φ : ℝ × Space → CVec3) :
    driftT Φ = dτT Φ - (1 / 2 : ℝ) • radialTT Φ := by
  funext p
  simp only [driftT, dτT, radialTT, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply]
  module

/-! ### Derivatives of the pointwise pairing -/

/-- The dot product as a real bilinear map. -/
def dotLR : CVec3 →L[ℝ] CVec3 →L[ℝ] ℂ :=
  (ContinuousLinearMap.restrictScalarsL ℂ CVec3 ℂ ℝ ℝ).comp (dotL.restrictScalars ℝ)

theorem dotLR_apply (a b : CVec3) : dotLR a b = dotL a b := rfl

/-- The pointwise pairing `(Φ · u)(p) = ∑ᵢ Φᵢ(p) uᵢ(p)`. -/
def dotFn (Φ u : ℝ × Space → CVec3) : ℝ × Space → ℂ := fun p => dotL (Φ p) (u p)

variable {Φ u : ℝ × Space → CVec3}

theorem hasFDerivAt_dotFn (hΦ : Differentiable ℝ Φ) (hu : Differentiable ℝ u)
    (p : ℝ × Space) :
    HasFDerivAt (dotFn Φ u)
      (dotLR.precompR (ℝ × Space) (Φ p) (fderiv ℝ u p) +
        dotLR.precompL (ℝ × Space) (fderiv ℝ Φ p) (u p)) p :=
  dotLR.hasFDerivAt_of_bilinear (hΦ p).hasFDerivAt (hu p).hasFDerivAt

theorem differentiable_dotFn (hΦ : Differentiable ℝ Φ) (hu : Differentiable ℝ u) :
    Differentiable ℝ (dotFn Φ u) :=
  fun p => (hasFDerivAt_dotFn hΦ hu p).differentiableAt

/-- Leibniz rule for the pointwise pairing. -/
theorem fderiv_dotFn (hΦ : Differentiable ℝ Φ) (hu : Differentiable ℝ u) (p v : ℝ × Space) :
    fderiv ℝ (dotFn Φ u) p v = dotL (fderiv ℝ Φ p v) (u p) + dotL (Φ p) (fderiv ℝ u p v) := by
  rw [(hasFDerivAt_dotFn hΦ hu p).fderiv, add_apply, add_comm]
  rfl

theorem dτ_dotFn (hΦ : Differentiable ℝ Φ) (hu : Differentiable ℝ u) (p : ℝ × Space) :
    dτ (dotFn Φ u) p = dotL (dτ Φ p) (u p) + dotL (Φ p) (dτ u p) :=
  fderiv_dotFn hΦ hu p _

theorem dy_dotFn (hΦ : Differentiable ℝ Φ) (hu : Differentiable ℝ u) (j : Fin 3)
    (p : ℝ × Space) :
    dy j (dotFn Φ u) p = dotL (dy j Φ p) (u p) + dotL (Φ p) (dy j u p) :=
  fderiv_dotFn hΦ hu p _

/-- `∂ⱼ(yⱼ g) = g + yⱼ ∂ⱼ g`. -/
theorem dy_coord_mul {g : ℝ × Space → ℂ} (hg : Differentiable ℝ g) (j : Fin 3)
    (p : ℝ × Space) :
    dy j (fun p => ((p.2 j : ℝ) : ℂ) * g p) p = g p + ((p.2 j : ℝ) : ℂ) * dy j g p := by
  let L : ℝ × Space →L[ℝ] ℂ := Complex.ofRealCLM.comp
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.snd ℝ ℝ Space))
  have hc : HasFDerivAt (fun p : ℝ × Space => ((p.2 j : ℝ) : ℂ)) L p := L.hasFDerivAt
  have h : HasFDerivAt (fun p : ℝ × Space => ((p.2 j : ℝ) : ℂ) * g p)
      (((p.2 j : ℝ) : ℂ) • fderiv ℝ g p + g p • L) p := hc.mul (hg p).hasFDerivAt
  simp only [dy]
  rw [h.fderiv]
  simp [L, coordinateVector]
  ring

/-! ### Lagrange identities -/

/-- **Lagrange identity for `T₀`**: `T₀ᵗΦ · u − Φ · T₀u = −∂_τ(Φ·u) + ½ ∑ⱼ ∂ⱼ(yⱼ Φ·u)`. -/
theorem lagrange_T0 (hΦ : Differentiable ℝ Φ) (hu : Differentiable ℝ u) (p : ℝ × Space) :
    dotL (driftT Φ p) (u p) - dotL (Φ p) (T0 u p) =
      -dτ (dotFn Φ u) p +
        (1 / 2 : ℂ) * ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) p := by
  have hg := differentiable_dotFn hΦ hu
  simp only [dy_coord_mul hg, dy_dotFn hΦ hu, dτ_dotFn hΦ hu]
  simp [driftT, T0, radialT, dotFn, dotL_apply, Fin.sum_univ_three, Complex.real_smul]
  ring

/-- **Lagrange identity for `Δ`**: `ΔΦ · u − Φ · Δu = ∑ⱼ ∂ⱼ(∂ⱼΦ·u − Φ·∂ⱼu)`. -/
theorem lagrange_lap (hΦ : ContDiff ℝ ∞ Φ) (hu : ContDiff ℝ ∞ u) (p : ℝ × Space) :
    dotL (lapT Φ p) (u p) - dotL (Φ p) (lapT u p) =
      ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) p := by
  have hD : ∀ {G : ℝ × Space → CVec3}, ContDiff ℝ ∞ G → Differentiable ℝ G :=
    fun hG => hG.differentiable (by simp)
  have hdy : ∀ {G : ℝ × Space → CVec3}, ContDiff ℝ ∞ G → ∀ j, Differentiable ℝ (dy j G) :=
    fun hG j => hD (contDiff_dy hG j)
  have hsub : ∀ j : Fin 3, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) p =
      dy j (dotFn (dy j Φ) u) p - dy j (dotFn Φ (dy j u)) p := fun j => by
    have h : HasFDerivAt (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p)
        (fderiv ℝ (dotFn (dy j Φ) u) p - fderiv ℝ (dotFn Φ (dy j u)) p) p :=
      ((differentiable_dotFn (hdy hΦ j) (hD hu)) p).hasFDerivAt.sub
        ((differentiable_dotFn (hD hΦ) (hdy hu j)) p).hasFDerivAt
    simp only [dy]
    rw [h.fderiv]
    rfl
  simp only [hsub, dy_dotFn (hdy hΦ _) (hD hu), dy_dotFn (hD hΦ) (hdy hu _)]
  simp [lapT, dotL_apply, Fin.sum_univ_three]
  ring

/-- **Lagrange identity for `L₀`**: `L₀ᵗΦ · u − Φ · L₀u` is the divergence-form expression
`−∂_τ(Φ·u) + ½ ∑ⱼ ∂ⱼ(yⱼ Φ·u) − ν ∑ⱼ ∂ⱼ(∂ⱼΦ·u − Φ·∂ⱼu)`. -/
theorem lagrange_L0 (ν : ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hu : ContDiff ℝ ∞ u) (p : ℝ × Space) :
    dotL (L0T ν Φ p) (u p) - dotL (Φ p) (L0 ν u p) =
      -dτ (dotFn Φ u) p +
        (1 / 2 : ℂ) * ∑ j : Fin 3, dy j (fun p => ((p.2 j : ℝ) : ℂ) * dotFn Φ u p) p -
        (ν : ℂ) * ∑ j : Fin 3, dy j (fun p => dotFn (dy j Φ) u p - dotFn Φ (dy j u) p) p := by
  have hD : ∀ {G : ℝ × Space → CVec3}, ContDiff ℝ ∞ G → Differentiable ℝ G :=
    fun hG => hG.differentiable (by simp)
  rw [← lagrange_T0 (hD hΦ) (hD hu) p, ← lagrange_lap hΦ hu p]
  simp only [L0T, L0, nuLapT, Pi.sub_apply, Pi.smul_apply]
  simp [dotL_apply, Fin.sum_univ_three, Complex.real_smul]
  ring

end UnforcedLeray.B0411
