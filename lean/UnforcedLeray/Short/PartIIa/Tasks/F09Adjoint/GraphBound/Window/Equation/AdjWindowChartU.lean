import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_1
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.AdjChart
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Chart.Rev

/-!


Source `the November 2 reference manuscript` lines 1426-1442 (`θ = 1 - e^{-t}`,
`x = e^{-t/2} y`). Uses the Bochner reversed chart `integral_adjChart` (`AdjChart.lean`) and the
pointwise value `rev_windowField_chart` (`Chart/Rev.lean`): `adjWindowField` at
`(1 - e^{-t}, e^{-t/2} y)` equals `χ(t) W(τ₀ - t, y)_c`. The weight is `e^{-5t/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic

namespace UnforcedLeray.Short.PartIIa

theorem adjWindowChartU : AdjWindowChartU := by
  intro χ τ₀ W c ζ
  have hG : ∀ X : PS 3, 1 ≤ X.1 → adjWindowField χ τ₀ W c X * (ζ X : ℂ) = 0 := by
    intro X hX
    simp [adjWindowField, not_lt.2 hX]
  refine (integral_adjChart (fun X => adjWindowField χ τ₀ W c X * (ζ X : ℂ)) hG).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  have hc : adjWindowField χ τ₀ W c (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) =
      ((χ p.1 : ℝ) : ℂ) * W (τ₀ - p.1, p.2) c :=
    rev_windowField_chart χ τ₀ W c p
  rw [hc, Complex.real_smul]
  push_cast
  ring

end UnforcedLeray.Short.PartIIa
