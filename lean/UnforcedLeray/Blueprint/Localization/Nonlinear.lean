import UnforcedLeray.Blueprint.Localization.Linear
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Localization proof, nonlinear part: steps L9–L12

`paper/main.tex` lines 430–524 and 563–572 of the proof of `thm:localization`.

| Step | Lines | Blueprint units | Content |
|---|---|---|---|
| L9 `CompactDatumStep` | 430–461 | B0717, B0718, B0719, B0720 | `u_{0,h} = curl(χA_loc)`, `‖K_loc‖_{W^{2,∞}} ≤ Ce^{τ/2}` |
| L10 `NonlinearStep` | 462–491 | B0721, B0722 | `𝓝`, `𝓒(K_loc,·)`, `G_*` and their bounds |
| L11 `AffineBoundStep` | 493–514 | B1021, B1023 | the two correction maps on `𝒵_β(τ₀)`, `loc:eq:affine-bound` |
| L12 `EquivarianceStep` | 563–572 | B1025 | the `𝒪`-action commutes with both maps |

The datum is the manuscript's explicit `u_{0,h} = curl(χ A_loc)` with
`A_loc(x) = -∫₀¹ r x × u_dss(rx) dr` (definitions adapted from
`SkeletonDesignA/LocalizationObjects.lean` and `SkeletonDesignB/LocalizationDefs.lean`).
The contraction (B1024), the choice of `τ₀`, invariance by uniqueness (B1025, line 572) and
the separation (B1027) are proved in `Compose.lean`. All four steps here are OPEN.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology BoundedContinuousFunction

namespace UnforcedLeray.Blueprint

open SobolevGraph

/-! ## The compact datum and the common heat tail (lines 430–450) -/

/-- The cross product on `ℝ³`. -/
def crossProd (a b : Space) : Space :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))

/-- `curl A = ∑_j e_j × ∂_j A`. -/
def curl (A : Space → Space) (x : Space) : Space :=
  ∑ j : Fin 3, crossProd (coordinateVector j) (fderiv ℝ A x (coordinateVector j))

/-- `A_loc(x) = -∫₀¹ r x × u_dss(rx) dr` (line 433). The integrand is bounded by
`|x||u(rx)| r ≤ C` under `loc:eq:dss`, so the interval integral converges. -/
def homotopyPotential (u : SpatialField) (x : Space) : Space :=
  -∫ r in (0 : ℝ)..1, r • crossProd x (u (r • x))

/-- "A smooth compactly supported radial `χ = 1` near zero" (line 441). -/
structure IsRadialCutoff (χ : Space → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  compact : HasCompactSupport χ
  one_near_zero : ∃ r : ℝ, 0 < r ∧ ∀ x : Space, ‖x‖ < r → χ x = 1
  radial : ∀ x y : Space, ‖x‖ = ‖y‖ → χ x = χ y

/-- `u_{0,h} = curl(χ A_loc)` (`loc:eq:compact-datum`, line 442). -/
def compactDatum (χ : Space → ℝ) (u : SpatialField) : SpatialField :=
  curl (fun x => χ x • homotopyPotential u x)

/-- `K_loc(y,τ) = √t H_loc(√t y, t)`, `H_loc = e^{htΔ} d_loc`, `d_loc = u₀ - u_dss`, `t = e^τ`
(line 446): the heat profile `H_h[d_loc]`. -/
def heatTail (D : BackgroundData) (u₀ : SpatialField) : ℝ → SpatialField :=
  heatProfile D.h (u₀ - D.udss)

/-- The properties of `u_{0,h}` used later (lines 451–461, 568–571): a nonzero compactly
supported solenoidal `L²` datum, `𝒪`-invariant, equal to `u_dss` near zero, smooth off zero;
every heat integral of the defect converges; `loc:eq:heat-correction`. -/
structure IsCompactDatum (D : BackgroundData) (u₀ : SpatialField) : Prop where
  datum : IsInitialDatum u₀
  symmetric : IsAxisymmetricNoSwirl u₀
  agrees_near_zero : ∃ r : ℝ, 0 < r ∧ ∀ x : Space, x ≠ 0 → ‖x‖ < r → u₀ x = D.udss x
  smooth_away : ContDiffOn ℝ ∞ u₀ {0}ᶜ
  defect_heat_integrable : ∀ s : ℝ, 0 < s → ∀ x : Space,
    Integrable (fun z : Space => Heat.kernel s z • (u₀ - D.udss) (x - z))
  tail_smooth : ∀ τ, ContDiff ℝ ∞ (heatTail D u₀ τ)
  tail_bound : ∃ C : ℝ, ∀ τ : ℝ, τ ≤ 0 → ∀ y : Space,
    ‖heatTail D u₀ τ y‖ ≤ C * Real.exp ((1 / 2) * τ) ∧
    ‖fderiv ℝ (heatTail D u₀ τ) y‖ ≤ C * Real.exp ((1 / 2) * τ) ∧
    ‖iteratedFDeriv ℝ 2 (heatTail D u₀ τ) y‖ ≤ C * Real.exp ((1 / 2) * τ)

/-- **Step L9** `CompactDatumStep`: for some radial cutoff `χ`, the explicit datum
`curl(χ A_loc)` has the properties above.
* Tex: lines 430–461 (`loc:eq:compact-datum`, `loc:eq:heat-correction`).
* Units: B0717, B0718, B0719, B0720.
* Infrastructure: `curl A_loc = u_dss` distributionally across `0` (vector calculus, INF23,
  INF31); symmetry of the azimuthal potential (INF24); Gaussian heat bounds for fields with
  `|x|^{-1}` decay vanishing near `0` (INF04, INF22, INF27). -/
def CompactDatumStep : Prop :=
  ∀ D : BackgroundData, IsUnstableBackground D →
    ∃ χ : Space → ℝ, IsRadialCutoff χ ∧ IsCompactDatum D (compactDatum χ D.udss)

/-! ## L10. Nonlinear operators and the cutoff force (lines 462–491) -/

/-- `𝓝(f,g) = -𝔓 div(f ⊗ g)` on `Z × Z → X`; `𝓒(K_loc(τ), ·)`; and `G_*(τ)`. -/
structure NonlinearMaps where
  N : Z →L[ℝ] Z →L[ℝ] X
  CK : ℝ → (Z →L[ℝ] X)
  Gstar : ℝ → X

/-- `𝓝(f,g) = -𝔓 div(f ⊗ g)`, `𝓒(f,g) = 𝔓 div(f ⊗ g + g ⊗ f)` (lines 464–465), and
`G_* = -𝓒(U_*, K_loc) + 𝓝(K_loc) = -𝔓 div(U_* ⊗ K + K ⊗ U_* + K ⊗ K)` (line 466), each
characterized by the literal weak `-𝔓 div`. Bounds: `‖𝓒(K_loc(τ),·)‖_{Z→X} ≤ Ce^{τ/2}`
(`H²` product and `W^{2,∞}` multiplication, line 506) and `loc:eq:force-bound`
`‖G_*(τ)‖_{H¹} ≤ Ce^{τ/2}`, for `τ ≤ 0`. -/
structure IsNonlinearMaps (D : BackgroundData) (u₀ : SpatialField) (nm : NonlinearMaps) :
    Prop where
  N_weak : ∀ f g : Z, IsMinusLerayDiv (tensorColumns (Zval f) (Zval g)) (Xclass (nm.N f g))
  CK_weak : ∀ τ, τ ≤ 0 → ∀ g : Z,
    IsMinusLerayDiv (symTensorColumns (heatTail D u₀ τ) (Zval g)) (-(Xclass (nm.CK τ g)))
  Gstar_weak : ∀ τ, τ ≤ 0 →
    IsMinusLerayDiv (addColumns (symTensorColumns (D.Ustar τ) (heatTail D u₀ τ))
      (tensorColumns (heatTail D u₀ τ) (heatTail D u₀ τ))) (Xclass (nm.Gstar τ))
  CK_continuous : ContinuousOn nm.CK (Iic 0)
  Gstar_continuous : ContinuousOn nm.Gstar (Iic 0)
  force_bound : ∃ C : ℝ, ∀ τ : ℝ, τ ≤ 0 → ‖nm.Gstar τ‖ ≤ C * Real.exp ((1 / 2) * τ)
  CK_bound : ∃ C : ℝ, ∀ τ : ℝ, τ ≤ 0 → ‖nm.CK τ‖ ≤ C * Real.exp ((1 / 2) * τ)

/-- **Step L10** `NonlinearStep`.
* Tex: lines 462–491 (`loc:eq:force-bound`).
* Units: B0721, B0722.
* Infrastructure: the `H²` algebra and `W^{2,∞}` multipliers (INF11); the compiled
  `h1Projection` (INF06); physical-space residual estimates `C⟨x⟩^{-3}`, `C⟨x⟩^{-4}` and
  super-polynomial decay of `H_loc` on an inner ball (INF04, INF22). -/
def NonlinearStep : Prop :=
  ∀ D : BackgroundData, IsUnstableBackground D → ∀ u₀ : SpatialField, IsCompactDatum D u₀ →
    ∃ nm : NonlinearMaps, IsNonlinearMaps D u₀ nm

/-! ## L11. The two correction maps and their bounds (lines 493–514) -/

/-- The quadratic, linear and affine parts of `loc:eq:local-fixed-point` on `𝒵_β(τ₀)`, in
weighted coordinates, for `j = 0, 1`. -/
structure CorrectionMaps (τ₀ : ℝ) where
  Bq : WeightedZ τ₀ →L[ℝ] WeightedZ τ₀ →L[ℝ] WeightedZ τ₀
  L : Fin 2 → (WeightedZ τ₀ →L[ℝ] WeightedZ τ₀)
  G : Fin 2 → WeightedZ τ₀

/-- The amplitude `j ∈ {0,1}` of the mode. -/
def jcoef (j : Fin 2) : ℝ := (j.val : ℝ)

/-- `z_j = 𝓡_β[G_* + j𝓝(v) - j𝓒(K,v) - 𝓒(K + jv, z_j) + 𝓝(z_j)]`, `v = e^{στ} b̂`, written
as `w = Bq w w + L_j w + G_j` with `z = e^{βτ} w`. Using `𝓒(f,g) = -(𝓝(f,g) + 𝓝(g,f))`:
* `Bq w₁ w₂ = 𝓡_β[e^{βτ} 𝓝(w₁, w₂)]`;
* `L_j w = 𝓡_β[-𝓒(K,w) + j e^{στ}(𝓝(b̂,w) + 𝓝(w,b̂))]`;
* `G_j = 𝓡_β[e^{-βτ}(G_* + j(e^{2στ} 𝓝(b̂,b̂) - e^{στ} 𝓒(K,b̂)))]`.
(Adapted from `SkeletonDesignC/LocalizationNonlinear.lean`.) -/
structure IsCorrectionMaps (D : BackgroundData) (ld : LinearData) (nm : NonlinearMaps)
    (τ₀ : ℝ) (cm : CorrectionMaps τ₀) : Prop where
  Bq_spec : ∀ w₁ w₂ : WeightedZ τ₀, ∃ F : WeightedX τ₀,
    (∀ τ : Iic τ₀, F τ = Real.exp (ld.sp.β * (τ : ℝ)) • nm.N (w₁ τ) (w₂ τ)) ∧
    cm.Bq w₁ w₂ = ld.R τ₀ F
  L_spec : ∀ (j : Fin 2) (w : WeightedZ τ₀), ∃ F : WeightedX τ₀,
    (∀ τ : Iic τ₀, F τ = -(nm.CK (τ : ℝ) (w τ)) +
      (jcoef j * Real.exp (D.σ * (τ : ℝ))) •
        (nm.N (ld.bhat (τ : ℝ)) (w τ) + nm.N (w τ) (ld.bhat (τ : ℝ)))) ∧
    cm.L j w = ld.R τ₀ F
  G_spec : ∀ j : Fin 2, ∃ F : WeightedX τ₀,
    (∀ τ : Iic τ₀, F τ = Real.exp (-(ld.sp.β * (τ : ℝ))) •
      (nm.Gstar (τ : ℝ) + jcoef j •
        (Real.exp (2 * D.σ * (τ : ℝ)) • nm.N (ld.bhat (τ : ℝ)) (ld.bhat (τ : ℝ)) -
          Real.exp (D.σ * (τ : ℝ)) • nm.CK (τ : ℝ) (ld.bhat (τ : ℝ))))) ∧
    cm.G j = ld.R τ₀ F

/-- **Step L11** `AffineBoundStep` (`loc:eq:affine-bound`): affine
`C₀(e^{(1/2-β)τ₀} + e^{(2σ-β)τ₀})`, linear `C(e^{τ₀/2} + e^{στ₀})`, bilinear `Ce^{βτ₀}`,
constants uniform in `τ₀ ≤ 0`.
* Tex: lines 493–514.
* Units: B1021, B1023.
* Infrastructure: bounded continuous functions into `X`, `Z` (Mathlib `BoundedContinuousFunction`);
  the bounds of L8 and L10; elementary exponential bookkeeping (INF29). -/
def AffineBoundStep : Prop :=
  ∀ D : BackgroundData, IsUnstableBackground D → ∀ ld : LinearData, IsLinearData D ld →
    ∀ u₀ : SpatialField, IsCompactDatum D u₀ → ∀ nm : NonlinearMaps, IsNonlinearMaps D u₀ nm →
      ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 ≤ C ∧ ∀ τ₀ : ℝ, τ₀ ≤ 0 →
        ∃ cm : CorrectionMaps τ₀, IsCorrectionMaps D ld nm τ₀ cm ∧
          (∀ j, ‖cm.G j‖ ≤ C₀ * (Real.exp ((1 / 2 - ld.sp.β) * τ₀) +
            Real.exp ((2 * D.σ - ld.sp.β) * τ₀))) ∧
          (∀ j, ‖cm.L j‖ ≤ C * (Real.exp ((1 / 2) * τ₀) + Real.exp (D.σ * τ₀))) ∧
          ‖cm.Bq‖ ≤ C * Real.exp (ld.sp.β * τ₀)

/-! ## L12. Equivariance (lines 563–572) -/

/-- For each `g ∈ 𝒪` an isometry of `𝒵_β(τ₀)` acting by `(g·f)(x) = g f(g⁻¹x)` at each phase
and preserving both correction maps (line 570). -/
def IsEquivariantCorrections {τ₀ : ℝ} (cm : CorrectionMaps τ₀) : Prop :=
  ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
    ∃ A : WeightedZ τ₀ →L[ℝ] WeightedZ τ₀,
      (∀ w, ‖A w‖ = ‖w‖) ∧
      (∀ w₁ w₂, cm.Bq (A w₁) (A w₂) = A (cm.Bq w₁ w₂)) ∧
      (∀ j w, cm.L j (A w) = A (cm.L j w)) ∧
      (∀ j, A (cm.G j) = cm.G j) ∧
      (∀ w (τ : Iic τ₀), Zval (A w τ) =ᵐ[volume] rotateField g (Zval (w τ)))

/-- **Step L12** `EquivarianceStep`.
* Tex: lines 563–572.
* Units: B1025 (equivariance part).
* Infrastructure: `𝒪` acts isometrically on `H¹_div`, `H²_div` and commutes with `𝔓`, the
  heat flow, `𝓑_*`, `E`, `P₊`, `Π₊`, `𝓡_β` (INF24, using the commutant clause of L6 and the
  uniqueness in L8). -/
def EquivarianceStep : Prop :=
  ∀ D : BackgroundData, IsUnstableBackground D → ∀ ld : LinearData, IsLinearData D ld →
    ∀ u₀ : SpatialField, IsCompactDatum D u₀ → ∀ nm : NonlinearMaps, IsNonlinearMaps D u₀ nm →
      ∀ τ₀ : ℝ, τ₀ ≤ 0 → ∀ cm : CorrectionMaps τ₀, IsCorrectionMaps D ld nm τ₀ cm →
        IsEquivariantCorrections cm

end UnforcedLeray.Blueprint
