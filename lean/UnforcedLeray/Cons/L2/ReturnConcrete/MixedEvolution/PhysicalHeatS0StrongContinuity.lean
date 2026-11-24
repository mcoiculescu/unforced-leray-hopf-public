import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatStrongContinuityZero
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatS0

/-!
# Age-zero continuity on the actual zero-circulation state

This restricts the weighted heat continuity theorem to the physical state subspace and keeps the
actual `S₀` operator, rather than replacing it by an arbitrary extension.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open Filter
open Set
open scoped Topology
open UnforcedLeray.B0579 hiding Plane

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Positive-side age-zero strong continuity of the actual physical weighted heat `S₀` on the
zero-circulation vorticity subspace. -/
theorem tendsto_actualWeightedHeatS0_apply_zero {c m : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (w : ActualVorticity (c := c) (m := m) hm) :
    Tendsto (fun θ : ℝ =>
      if hθ : 0 < θ then
        if hθ1 : θ ≤ 1 then
          actualWeightedHeatS0 (c := c) hc1 hm (by linarith) hθ1 w
        else w
      else w)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 w) := by
  let U : ℝ → ActualVorticity (c := c) (m := m) hm := fun θ =>
    if hθ : 0 < θ then
      if hθ1 : θ ≤ 1 then
        actualWeightedHeatS0 (c := c) hc1 hm (by linarith) hθ1 w
      else w
    else w
  let Ux : ℝ → X c m := fun θ =>
    if hθ : 0 < θ then
      if hθ1 : θ ≤ 1 then
        xColumnHeatS0Positive (Fact.out : 0 < c) hm hθ hθ1 w.1
      else w.1
    else w.1
  have hX := tendsto_xColumnHeatS0Positive_apply_zero
    (Fact.out : 0 < c) hc1 hm w.1
  have hX' : Tendsto Ux (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 w.1) := by
    simpa [Ux] using hX
  have hval : ∀ θ : ℝ, (U θ).1 = Ux θ := by
    intro θ
    by_cases hθ : 0 < θ
    · by_cases hθ1 : θ ≤ 1
      · have h := actualWeightedHeatS0_apply_of_pos (c := c) hc1 hm hθ hθ1 w
        simpa [U, Ux, hθ, hθ1] using h
      · simp [U, Ux, hθ, hθ1]
    · simp [U, Ux, hθ]
  have hnormX : Tendsto (fun θ : ℝ => ‖Ux θ - w.1‖)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hX')
  have hnormW : Tendsto (fun θ : ℝ => ‖U θ - w‖)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 0) := by
    apply hnormX.congr'
    filter_upwards [] with θ
    change ‖Ux θ - w.1‖ = ‖(U θ).1 - w.1‖
    rw [hval θ]
  have hU : Tendsto U (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 w) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnormW
  simpa [U] using hU

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.tendsto_actualWeightedHeatS0_apply_zero
