import UnforcedLeray.Blueprint.Localization.Nonlinear
import UnforcedLeray.Analysis.Heat.IntegrationByParts
import UnforcedLeray.Analysis.ViscosityTransport.Solution

/-!
# Localization proof, realization: steps L13–L14

`paper/main.tex` lines 501–503 and 525–561 of the proof of `thm:localization`.

Blueprint units: B1022, B1025, B1026, B1028, B1029, B1030, B1031, B1032.

Following the feasibility judgment, the realization is split into
* L13 `PhysicalRemainderStep` (package-specific): fixed points of the two correction maps
  give physical remainders `ρ_j(t) = t^{-1/2}[r_heat + j e^{στ}b̂ + z_j](·/√t, log t)` in
  `H²_div` that solve the strong projected equation over the heat flow of the datum, with
  the rates of line 540;
* L14 `RealizationStep` (package-free): a strong `H²` remainder over the heat flow of a
  compact datum gives a member of the full Lean solution class `IsTheoremASolutionViscosity`
  (jointly measurable representatives, weak derivatives, the `L^{5/3}` pressure with the
  weak form including the datum, the energy equality) together with its symmetry.

This isolates the infrastructure of critic §5a (measurable representatives) and §6 (the
pressure identity) in L14, which mentions no package object. Adapted from
`SkeletonDesignB/LocalizationSteps.lean` (L12, L13), with the literal `-𝔓 div`.
Both steps are OPEN.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology BoundedContinuousFunction

namespace UnforcedLeray.Blueprint

open SobolevGraph

/-- The similarity remainder `r_heat + j e^{στ} b̂ + z` at phase `τ` (lines 517, 536), as an
`L²` class; `z(τ) = e^{βτ} w(τ)` is the correction (`0` after `τ₀`). -/
def remainderClass (D : BackgroundData) (bhat : ℝ → Z) (β : ℝ) {τ₀ : ℝ} (w : WeightedZ τ₀)
    (j : ℝ) (τ : ℝ) : L2Space :=
  (D.rheat τ).value + (j * Real.exp (D.σ * τ)) • Zclass (bhat τ) + Zclass (unweight β w τ)

/-- A physical remainder `ρ(t) ∈ H²_div` on `(0,T]` for the total field
`u = e^{htΔ}u₀ + ρ` (`loc:eq:total-field`): continuity in `H²`, the `L²` and squared gradient
rates of line 540, `N = -𝔓 div(u ⊗ u)` (literal), the strong projected equation
`∂_t ρ = hΔρ + N` in `L²` at interior times (lines 546–547), and `𝒪`-invariance. -/
structure IsPhysicalStrongRemainder (h T : ℝ) (u₀ : SpatialField) (ρ : ℝ → H2)
    (N : ℝ → L2Space) (C : ℝ) : Prop where
  continuous : ContinuousOn ρ (Ioc 0 T)
  solenoidal : ∀ t ∈ Ioc 0 T, (ρ t).value ∈ Leray.solenoidalSubspace
  l2_rate : ∀ t ∈ Ioc 0 T, ‖(ρ t).value‖ ≤ C * t ^ (1 / 4 : ℝ)
  gradient_rate : ∀ t ∈ Ioc 0 T, ∑ i : Fin 3, ‖(ρ t).first i‖ ^ 2 ≤ C * t ^ (-(1 / 2 : ℝ))
  nonlinear_weak : ∀ t ∈ Ioc 0 T, IsMinusLerayDiv
    (tensorColumns (physicalVelocity h u₀ ρ t) (physicalVelocity h u₀ ρ t)) (N t)
  nonlinear_continuous : ContinuousOn N (Ioc 0 T)
  equation : ∀ t ∈ Ioo 0 T,
    HasDerivAt (fun s => (ρ s).value) (h • H2.laplace (ρ t) + N t) t
  symmetric : ∀ t ∈ Ioc 0 T, IsAxisymmetricNoSwirl ((ρ t).value : SpatialField)

/-- The physical remainders of the two solutions, their nonlinearities and a common rate
constant. -/
structure PhysicalRemainders where
  ρ : Fin 2 → ℝ → H2
  N : Fin 2 → ℝ → L2Space
  C : ℝ

/-- **Step L13** `PhysicalRemainderStep`: every pair of fixed points of the correction maps
(no smallness needed), with invariant corrections, gives physical remainders with the
representation `ρ_j(t) = t^{-1/2}[r_heat + j v + z_j](·/√t, log t)` on `(0, e^{τ₀}]` and the
strong equation of the total field.
* Tex: lines 501–503 (the expansion with `j² = j`), 525–547.
* Units: B1022, B1026, B1028, B1029 (profile part), B1025 (symmetry of the fields).
* Infrastructure: mild-to-strong regularity for the evolution of L3 and the Green operator
  of L8 (INF07, INF08, INF14); the package equations in strong form (density of tests in
  `L²`, the literal `𝔓`); linearity of the heat profile `H_h[u₀] = H_h[u_dss] + K_loc`
  (uses `defect_heat_integrable`); dilation of Sobolev classes
  (`ViscosityTransport.dilationL2`); `𝒪`-equivariance of the heat flow (INF24). -/
def PhysicalRemainderStep : Prop :=
  ∀ D : BackgroundData, IsUnstableBackground D → ∀ ld : LinearData, IsLinearData D ld →
    ∀ u₀ : SpatialField, IsCompactDatum D u₀ → ∀ nm : NonlinearMaps, IsNonlinearMaps D u₀ nm →
      ∀ τ₀ : ℝ, τ₀ ≤ 0 → ∀ cm : CorrectionMaps τ₀, IsCorrectionMaps D ld nm τ₀ cm →
        ∀ w : Fin 2 → WeightedZ τ₀, (∀ j, w j = cm.Bq (w j) (w j) + cm.L j (w j) + cm.G j) →
          (∀ j (τ : Iic τ₀), IsAxisymmetricNoSwirl (Zval (w j τ))) →
            ∃ pr : PhysicalRemainders, ∀ j : Fin 2,
              (∀ t ∈ Ioc (0 : ℝ) (Real.exp τ₀), (pr.ρ j t).value =
                physicalDilation t
                  (remainderClass D ld.bhat ld.sp.β (w j) (jcoef j) (Real.log t))) ∧
              IsPhysicalStrongRemainder D.h (Real.exp τ₀) u₀ (pr.ρ j) (pr.N j) pr.C

/-- **Step L14** `RealizationStep`: a strong `H²` remainder over the heat flow of a compact
symmetric datum gives a member of the full Lean solution class, with pointwise
representatives agreeing a.e. at every time with the total field (including `u(0) = u₀`),
and with its symmetry. It mentions no package object.
* Tex: lines 539–561 (strong trace, `loc:eq:regularity`, `loc:eq:energy`, the pressure
  `∑ R_iR_k(u_iu_k) ∈ L^{5/3}`, `eq:initial-weak-form`).
* Units: B1029, B1030, B1031, B1032.
* Infrastructure: jointly measurable representatives of Bochner curves and measurable
  weak-derivative witnesses (critic §5a, 1–3k lines); the pressure identity
  `∇p = -(I - 𝔓) div(u ⊗ u)` for the pressure used (critic §6; the compiled Newton pressure
  `Pressure/*` with `Pressure/NewtonIdentity.lean`, or Calderón–Zygmund INF01); the energy
  identity from the strong equation (INF14; compiled `Analysis/Heat/Energy.lean`); the
  `L^{10/3}` interpolation (INF11). -/
def RealizationStep : Prop :=
  ∀ (h T : ℝ) (u₀ : SpatialField) (ρ : ℝ → H2) (N : ℝ → L2Space) (C : ℝ),
    0 < h → 0 < T → IsInitialDatum u₀ → IsAxisymmetricNoSwirl u₀ →
      IsPhysicalStrongRemainder h T u₀ ρ N C →
        ∃ (u : Velocity) (p : Pressure) (G : FirstDerivatives) (H : SecondDerivatives),
          (∀ t ∈ Icc (0 : ℝ) T, u t =ᵐ[volume] physicalVelocity h u₀ ρ t) ∧
          ViscosityTransport.IsTheoremASolutionViscosity h T u₀ u p G H ∧
          ∀ t ∈ Icc (0 : ℝ) T, IsAxisymmetricNoSwirl (u t)

end UnforcedLeray.Blueprint
