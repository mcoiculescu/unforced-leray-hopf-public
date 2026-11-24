import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Volterra
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatCirculation

/-!
# The actual weighted Gaussian `S₀` on the physical state space

This restricts the concrete weighted heat family to the actual zero-circulation vorticity
subspace. The positive-age restriction is justified by Gaussian cell-integral conservation; the
zero-age value is the identity. Its operator bound is explicit for fixed `c,m`.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open UnforcedLeray.GaussianVortex (Plane)

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

variable {c m : ℝ} [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m)

/-- The actual B0284 weighted heat family restricted to the physical zero-circulation state. -/
noncomputable def actualWeightedHeatS0 {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ActualVorticity (c := c) (m := m) hm →L[ℝ]
      ActualVorticity (c := c) (m := m) hm := by
  let Z := ActualVorticity (c := c) (m := m) hm
  let full := xColumnHeatS0CLM (Fact.out : 0 < c) hc1 hm hθ0 hθ1
  refine (full.comp Z.subtypeL).codRestrict Z ?_
  intro w
  by_cases hθ : 0 < θ
  · change xColumnHeatS0CLM (Fact.out : 0 < c) hc1 hm hθ0 hθ1 w.1 ∈ Z
    rw [xColumnHeatS0CLM_apply_of_pos (Fact.out : 0 < c) hc1 hm hθ hθ1 w.1]
    exact xColumnHeatS0Positive_mem_zeroCirculation
      (Fact.out : 0 < c) hm hθ hθ1 w.1 w.2
  · have hzero : θ = 0 := by linarith
    subst θ
    simpa [full, xColumnHeatS0CLM] using w.2

@[simp] theorem actualWeightedHeatS0_zero :
    actualWeightedHeatS0 (c := c) hc1 hm (θ := 0) le_rfl (by norm_num) =
      ContinuousLinearMap.id ℝ (ActualVorticity (c := c) (m := m) hm) := by
  apply ContinuousLinearMap.ext
  intro w
  apply Subtype.ext
  simp [actualWeightedHeatS0, xColumnHeatS0CLM]

theorem actualWeightedHeatS0_apply_of_pos {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (w : ActualVorticity (c := c) (m := m) hm) :
    (actualWeightedHeatS0 (c := c) hc1 hm (by linarith) hθ1 w :
      UnforcedLeray.B0579.X c m) =
      xColumnHeatS0Positive (Fact.out : 0 < c) hm hθ hθ1 w.1 := by
  apply Subtype.ext
  simp [actualWeightedHeatS0, xColumnHeatS0CLM, hθ,
    xColumnHeatS0PositiveCLM_apply]

/-- Fixed-cylinder short-strip bound on the physical state space, inherited from the actual
weighted Gaussian heat CLM. -/
theorem norm_actualWeightedHeatS0_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖actualWeightedHeatS0 (c := c) hc1 hm hθ0 hθ1‖ ≤
      max 1 ((1 + c ^ 2 / 4) ^ (m / 2) *
        (2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z)) := by
  have hfull := norm_xColumnHeatS0CLM_le (Fact.out : 0 < c) hc1 hm hθ0 hθ1
  have hK : 0 ≤ max 1 ((1 + c ^ 2 / 4) ^ (m / 2) *
      (2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z)) := by
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun w => ?_
  change ‖xColumnHeatS0CLM (Fact.out : 0 < c) hc1 hm hθ0 hθ1 w.1‖ ≤
    max 1 ((1 + c ^ 2 / 4) ^ (m / 2) *
      (2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z)) * ‖w‖
  calc
    ‖xColumnHeatS0CLM (Fact.out : 0 < c) hc1 hm hθ0 hθ1 w.1‖ ≤
        ‖xColumnHeatS0CLM (Fact.out : 0 < c) hc1 hm hθ0 hθ1‖ * ‖w.1‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ max 1 ((1 + c ^ 2 / 4) ^ (m / 2) *
        (2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z)) * ‖w‖ := by
          exact mul_le_mul hfull (le_of_eq rfl) (norm_nonneg _) (by positivity)

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatS0
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatS0_zero
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_actualWeightedHeatS0_le
