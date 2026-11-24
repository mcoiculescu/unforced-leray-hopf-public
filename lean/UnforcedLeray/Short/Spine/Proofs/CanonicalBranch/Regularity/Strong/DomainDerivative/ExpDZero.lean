import UnforcedLeray.Short.Spine.Sub.SP_CAN4_2_1
import UnforcedLeray.Cons.L2.CanonicalBranch.CanonicalAmplitudeGenerator

/-!
# Spine: right derivative at `0` of the Gaussian semigroup on `𝒟(D)` (task `Spine:SP-CAN/4/2/1/2`)

Source: `the November 2 reference manuscript` line 1086 and lines 1134-1145.

For `z ∈ 𝒟(D)` and `a ≥ 0`, `e^{aD} z = z + ∫_0^a e^{rD} (D z) dr` (`expD_integral_generator`).
The integral has right derivative `e^{0D} (D z) = D z` at `0` (FTC from the right, `nhdsRight`),
and the two functions agree on `Ici 0`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 UnforcedLeray.B0123

/-- Right derivative at `0` of `a ↦ e^{aD} z` on `𝒟(D)`, within `Ici 0`, equal to `D z`. -/
theorem hasDerivWithinAt_expD_zero_domain (z : UnforcedLeray.B0094.D.domain) :
    HasDerivWithinAt (fun a : ℝ => UnforcedLeray.B0123.expD a (z : UnforcedLeray.B0010.XG))
      (UnforcedLeray.B0094.D z) (Set.Ici 0) 0 := by
  have hcont : Continuous (fun u : ℝ => expD u (UnforcedLeray.B0094.D z)) :=
    UnforcedLeray.Cons.G3b.continuous_expD_apply _
  have hderInt : HasDerivWithinAt (fun u : ℝ => ∫ x in (0 : ℝ)..u, expD x (UnforcedLeray.B0094.D z))
      (expD 0 (UnforcedLeray.B0094.D z)) (Set.Ici 0) 0 :=
    intervalIntegral.integral_hasDerivWithinAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter volume (𝓝[>] (0 : ℝ)))
      hcont.continuousWithinAt
  have hder := hderInt.const_add (z : XG)
  rw [expD_zero, ContinuousLinearMap.one_apply] at hder
  refine hder.congr (fun x hx => ?_) ?_
  · exact UnforcedLeray.Cons.G3b.expD_integral_generator (a := x) hx z
  · simp [expD_zero]

end UnforcedLeray.Short.Spine
