import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatS0StrongContinuity

/-!
# Nonnegative-side age-zero continuity of physical weighted heat

The value at age zero supplies the singleton endpoint needed to upgrade the positive-side limit
from the open half-line to the closed nonnegative half-line.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open Filter
open Set
open scoped Topology
open UnforcedLeray.B0579 hiding Plane

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Actual `S₀` is strongly continuous at age zero when approached through the closed
nonnegative half-line, including its exact identity value at zero. -/
theorem tendsto_actualWeightedHeatS0_apply_zero_nonneg {c m : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (w : ActualVorticity (c := c) (m := m) hm) :
    Tendsto (fun θ : ℝ =>
      if hθ : 0 < θ then
        if hθ1 : θ ≤ 1 then
          actualWeightedHeatS0 (c := c) hc1 hm (by linarith) hθ1 w
        else w
      else actualWeightedHeatS0 (c := c) hc1 hm (θ := 0) le_rfl (by norm_num) w)
      (nhdsWithin (0 : ℝ) (Ici (0 : ℝ))) (𝓝 w) := by
  let U : ℝ → ActualVorticity (c := c) (m := m) hm := fun θ =>
    if hθ : 0 < θ then
      if hθ1 : θ ≤ 1 then
        actualWeightedHeatS0 (c := c) hc1 hm (by linarith) hθ1 w
      else w
      else actualWeightedHeatS0 (c := c) hc1 hm (θ := 0) le_rfl (by norm_num) w
  have hpos := tendsto_actualWeightedHeatS0_apply_zero hc1 hm w
  have hposU : Tendsto U (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 w) := by
    apply hpos.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    simp [U, hθ]
  have hzero : U 0 = w := by simp [U]
  have hsingle : Tendsto U (nhdsWithin (0 : ℝ) {0}) (𝓝 w) := by
    have heq : U =ᶠ[nhdsWithin (0 : ℝ) {0}] fun _ : ℝ => w := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hθ0 : θ = 0 := by simpa using hθ
      simp [hθ0, hzero]
    exact tendsto_const_nhds.congr' heq.symm
  have hset : Ioi (0 : ℝ) ∪ {0} = Ici (0 : ℝ) := by
    ext θ
    simp [mem_Ioi, mem_Ici, eq_comm]
  rw [← hset, nhdsWithin_union]
  exact hposU.sup hsingle

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.tendsto_actualWeightedHeatS0_apply_zero_nonneg
