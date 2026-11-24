import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_1
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.AdjChart
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Chart.Rev

/-!


Source `the November 2 reference manuscript` lines 1426-1442 (`θ = 1 - e^{-t}`,
`x = e^{-t/2} y`). Uses the Bochner reversed chart `integral_adjChart` (`AdjChart.lean`) and the
pointwise value `rev_windowForce_chart` (`Chart/Rev.lean`): `adjWindowForce` at
`(1 - e^{-t}, e^{-t/2} y)` equals `e^{t}[(χ' - (1+μ̄)χ) W + χ Fr](τ₀ - t, y)`. The total weight is
`e^{-5t/2} · e^{t} = e^{-3t/2}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic

namespace UnforcedLeray.Short.PartIIa

theorem adjWindowChartF : AdjWindowChartF := by
  intro μ χ τ₀ W Fr c φ
  have hG : ∀ X : PS 3, 1 ≤ X.1 → adjWindowForce μ χ τ₀ W Fr c X * (φ X : ℂ) = 0 := by
    intro X hX
    simp [adjWindowForce, not_lt.2 hX]
  refine (integral_adjChart (fun X => adjWindowForce μ χ τ₀ W Fr c X * (φ X : ℂ)) hG).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [show -p.1 / 2 = -(p.1 / 2) by ring]
  have hc : adjWindowForce μ χ τ₀ W Fr c (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) =
      ((Real.exp p.1 : ℝ) : ℂ) *
        ((((deriv χ p.1 : ℝ) : ℂ) - (1 + (starRingEnd ℂ) μ) * ((χ p.1 : ℝ) : ℂ)) *
            W (τ₀ - p.1, p.2) c + ((χ p.1 : ℝ) : ℂ) * Fr (τ₀ - p.1, p.2) c) :=
    rev_windowForce_chart μ χ τ₀ W Fr c p
  have he : ((Real.exp (-(5 * p.1 / 2)) : ℝ) : ℂ) * ((Real.exp p.1 : ℝ) : ℂ) =
      ((Real.exp (-(3 * p.1 / 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show -(5 * p.1 / 2) + p.1 = -(3 * p.1 / 2) by ring]
  rw [hc, Complex.real_smul]
  linear_combination
    ((((deriv χ p.1 : ℝ) : ℂ) - (1 + (starRingEnd ℂ) μ) * ((χ p.1 : ℝ) : ℂ)) *
        W (τ₀ - p.1, p.2) c + ((χ p.1 : ℝ) : ℂ) * Fr (τ₀ - p.1, p.2) c) *
      ((φ (1 - Real.exp (-p.1), Real.exp (-(p.1 / 2)) • p.2) : ℝ) : ℂ) * he

end UnforcedLeray.Short.PartIIa
