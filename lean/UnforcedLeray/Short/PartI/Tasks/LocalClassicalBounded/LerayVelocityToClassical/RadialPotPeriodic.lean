import UnforcedLeray.Short.PartI.Sub.T02_1_5
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical.RadialPotGrad

/-!
# Part I, task `PartI:T02/1/5/6` (Leaf 6): periodicity of the radial potential

Source of record: `the November 2 reference manuscript`, lines 261-288.
This file proves `RadialPotPeriodic` (defined in `Short/PartI/Sub/T02_1_5.lean`): if `G` is
smooth, `c`-periodic, curl free and has zero horizontal mean at every height, then
`radialPot G` is `c`-periodic.

Method.  The slice `r ↦ radialPot G (r, η)` has derivative `-G₀(r, η)` (the lemma `rpg_slopeQ`
of `RadialPotGrad.lean`, which is the `q`-slope half of Leaf 5).  The fundamental theorem of
calculus over `[q, q + c]` gives `radialPot G (q + c, η) - radialPot G (q, η) =
-∫_q^{q+c} G₀(r, η) dr`.  The integrand is `c`-periodic in `r`, so the integral does not depend on
the window (`Function.Periodic.intervalIntegral_add_eq`), and it equals `-∫_0^c G₀(r, η) dr = 0`
by the zero-mean hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- **Leaf 6** (periodicity of the radial potential): for a smooth, `c`-periodic, curl-free field
`G` with zero horizontal mean at every height, `radialPot G` is `c`-periodic. -/
theorem radialPotPeriodic : RadialPotPeriodic := by
  unfold RadialPotPeriodic
  intro c G hc hG hper hcurl hmean
  have hcG : ∀ w : Plane, fderiv ℝ G w (1, 0) 1 = fderiv ℝ G w (0, 1) 0 := by
    intro w
    have h := hcurl w
    rw [rpg_partialQ_comp hG 1 w, rpg_partialEta_comp hG 0 w] at h
    exact h
  unfold Cyl.IsPeriodic
  rintro ⟨q, η⟩
  show radialPot G (q + c, η) = radialPot G (q, η)
  -- continuity of the horizontal component along a horizontal line
  have hcont : Continuous fun r : ℝ => G (r, η) 0 := by
    have hGc : Continuous G := hG.continuous
    fun_prop
  -- fundamental theorem of calculus for the slice `r ↦ radialPot G (r, η)`
  have hFTC : ∫ r in q..(q + c), -(G (r, η) 0) =
      radialPot G (q + c, η) - radialPot G (q, η) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => radialPot G (y, η)) (f' := fun r : ℝ => -(G (r, η) 0))
      (fun r _ => rpg_slopeQ hG hcG r η)
      (hcont.neg.intervalIntegrable _ _)
  -- the integrand is `c`-periodic in `r`
  have hperiod : Function.Periodic (fun r : ℝ => G (r, η) 0) c := by
    intro r
    exact congrArg (fun v : Vec => v 0) (hper (r, η))
  -- the integral over `[q, q + c]` equals the integral over `[0, c]`
  have hshift : ∫ r in q..(q + c), G (r, η) 0 = ∫ r in (0 : ℝ)..c, G (r, η) 0 := by
    have h : ∫ r in q..(q + c), G (r, η) 0 = ∫ r in (0 : ℝ)..(0 + c), G (r, η) 0 :=
      hperiod.intervalIntegral_add_eq q 0
    rw [zero_add] at h
    exact h
  have hzero : ∫ r in (0 : ℝ)..c, G (r, η) 0 = 0 := hmean η
  have key : radialPot G (q + c, η) - radialPot G (q, η) = 0 := by
    rw [← hFTC, intervalIntegral.integral_neg, hshift, hzero, neg_zero]
  exact sub_eq_zero.mp key

end UnforcedLeray.Short.PartI
