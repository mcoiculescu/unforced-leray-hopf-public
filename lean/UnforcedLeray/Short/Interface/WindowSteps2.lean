import UnforcedLeray.Short.Interface.WindowSteps

/-!
# Interface: splitting step W1 into the chart equation (13) and the time change (14)

`paper/main.tex` lines 7485-7497 (old manuscript): `v_t - νe^tΔ_xv = g` in the chart variables
`(t,x)` (13), then the cutoff and the substitution `θ = e^t` (14).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08 UnforcedLeray.Parabolic

/-- `v_t - h e^tΔ_xv = g` in distributions on `ℝ × ℝ³` (`eq:free-stress-13`), tested against
`Ξ ∈ C_c^∞(ℝ × ℝ³)`: `∫ v_i(-∂_tΞ - h e^tΔ_xΞ) = ∫ g_iΞ`, `g = -(f + μw)` in the chart. -/
def ChartEquationHolds (h μ : ℝ) (w f : ℝ → SpatialField) (τ₀ : ℝ) (i : Fin 3) : Prop :=
  ∀ Ξ : PS 3 → ℝ, IsSTTest Ξ →
    (∫ X : PS 3, chartField τ₀ w X.1 X.2 i * (-(tD Ξ X) - h * Real.exp X.1 * sLap Ξ X)) =
      ∫ X : PS 3, (-(chartField τ₀ f X.1 X.2 i + μ * chartField τ₀ w X.1 X.2 i)) * Ξ X

/-- Step W1a (`eq:free-stress-13`): the free equation gives the chart equation. The test is
`phaseTest τ₀ Ξ e_i` (`Units/B0424/Calc.lean`); the identity is a change of variables
`y ↦ x = e^{t/2}y` (`Units/B0424/Chart.lean`, `integral_dilChart`). -/
def WindowChartEquationLocal : Prop :=
  ∀ (h μ P : ℝ) (w f : ℝ → SpatialField) (τ₀ : ℝ) (i : Fin 3), 0 < h → 0 < P →
    B0005.IsY2 P w → B0005.IsY2 P f → IsSourceFreeSolution h μ w f →
    ChartEquationHolds h μ w f τ₀ i

/-- Step W1b (`eq:free-stress-14`): cutoff and time change `θ = e^t` turn the chart equation
into the heat equation for `u = χ v`. The test is `timeTest χ Ψ` (`Units/B0424/Tests.lean`);
the substitution is `integral_expChart` (`Units/B0424/Chart.lean`). -/
def WindowChartTimeChange : Prop :=
  ∀ (h μ P : ℝ) (w f : ℝ → SpatialField) (χ : ℝ → ℝ) (τ₀ : ℝ) (i : Fin 3), 0 < h → 0 < P →
    B0005.IsY2 P w → B0005.IsY2 P f → IsWindowCutoff χ → ChartEquationHolds h μ w f τ₀ i →
    B0423.IsWeakHeatSol (d := 3) h (windowU χ τ₀ w i) (windowF χ μ τ₀ w f i)

end UnforcedLeray.Short.Interface
