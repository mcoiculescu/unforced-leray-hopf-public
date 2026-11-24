import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Volterra
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxHeatCLM
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatS0

/-!
# The physical signed heat response on the zero-circulation state space

This packages the already constructed literal `-B0296.heatDiv` response to actual weighted flux
columns as a CLM with range in the actual zero-circulation vorticity space. The estimate is for a
fixed cylinder and short positive ages; no uniform-in-cylinder evolution rate is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open UnforcedLeray.GaussianVortex (Plane)

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

variable {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)

/-- The actual signed heat-divergence forcing from a two-component weighted flux into the
zero-circulation vorticity state space. It is zero outside the positive short-age strip. -/
noncomputable def actualWeightedHeatResponse (θ : ℝ) :
    ActualFlux (c := c) (m := m) →L[ℝ]
      ActualVorticity (c := c) (m := m) hm := by
  by_cases hθ : 0 < θ
  · by_cases hθ1 : θ ≤ 1
    · let L := xFluxNegativeHeatDivXCLM (Fact.out : 0 < c) hm hθ hθ1
    
      have hrange (F : ActualFlux (c := c) (m := m)) :
          L F ∈ ActualVorticity (c := c) (m := m) hm := by
        change xFluxNegativeHeatDivXLinear (Fact.out : 0 < c) hm hθ hθ1 F ∈ _
        exact xFluxNegativeHeatDivXLinear_mem_zeroCirculation
          (Fact.out : 0 < c) hm hθ hθ1 F
      exact L.codRestrict _ hrange
    · exact 0
  · exact 0

@[simp] theorem actualWeightedHeatResponse_apply_of_pos {θ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (F : ActualFlux (c := c) (m := m)) :
    (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) θ F :
      UnforcedLeray.B0579.X c m) =
    xFluxNegativeHeatDivXCLM (Fact.out : 0 < c) hm hθ hθ1 F := by
  simp [actualWeightedHeatResponse, hθ, hθ1]

/-- The actual response is literally the negative B0296 Gaussian heat-divergence output. -/
theorem actualWeightedHeatResponse_value {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (F : ActualFlux (c := c) (m := m)) :
    (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) θ F :
      UnforcedLeray.B0579.X c m) =
      (memLp_xFlux_negativeHeatDiv_fst_X (Fact.out : 0 < c) hm hθ hθ1 F).toLp
        (fun z => (negativeHeatDiv θ (xFluxPeriodicTensor (Fact.out : 0 < c) F) z).1) := by
  rw [actualWeightedHeatResponse_apply_of_pos (c := c) (m := m) (hm := hm)
    hθ hθ1 F]
  exact xFluxNegativeHeatDivXCLM_apply_eq_actual
    (Fact.out : 0 < c) hm hθ hθ1 F

/-- Fixed-cylinder short-age smoothing estimate for the actual signed response. -/
theorem norm_actualWeightedHeatResponse_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ‖actualWeightedHeatResponse (c := c) (m := m) (hm := hm) θ‖ ≤
      2 * ((1 + c ^ 2 / 4) ^ (m / 2) *
        (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ z : Plane, gradKernelAxialMomentDensity 1 m z)) := by
  let C : ℝ := (1 + c ^ 2 / 4) ^ (m / 2) *
    (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
      ∫ z : Plane, gradKernelAxialMomentDensity 1 m z)
  have hmoment : 0 ≤ ∫ z : Plane, gradKernelAxialMomentDensity 1 m z := by
    apply integral_nonneg_of_ae
    filter_upwards with z
    unfold gradKernelAxialMomentDensity
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have hbase : 0 ≤ (1 + c ^ 2 / 4) ^ (m / 2) :=
      Real.rpow_nonneg (by positivity) _
    have htwo : 0 ≤ (2 : ℝ) ^ (m / 2) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
    have htheta : 0 ≤ θ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hθ.le _
    positivity
  have h2C : 0 ≤ 2 * C := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h2C fun F => ?_
  change ‖((actualWeightedHeatResponse (c := c) (m := m) (hm := hm) θ F :
    ActualVorticity (c := c) (m := m) hm) : UnforcedLeray.B0579.X c m)‖ ≤ _
  rw [actualWeightedHeatResponse_apply_of_pos (c := c) (m := m) (hm := hm)
    hθ hθ1 F]
  have hbound := norm_xFluxNegativeHeatDivXLinear_le
    (Fact.out : 0 < c) hm hθ hθ1 F
  have h0 : ‖F 0‖ ≤ ‖F‖ := norm_le_pi_norm F 0
  have h1 : ‖F 1‖ ≤ ‖F‖ := norm_le_pi_norm F 1
  change ‖xFluxNegativeHeatDivXLinear (Fact.out : 0 < c) hm hθ hθ1 F‖ ≤ _
  calc
    ‖xFluxNegativeHeatDivXLinear (Fact.out : 0 < c) hm hθ hθ1 F‖ ≤
        C * (‖F 0‖ + ‖F 1‖) := by
      simpa [C, mul_assoc, mul_left_comm, mul_comm] using hbound
    _ ≤ C * (‖F‖ + ‖F‖) := mul_le_mul_of_nonneg_left (add_le_add h0 h1) hC
    _ = 2 * C * ‖F‖ := by ring

/-- The actual zero-age heat identity gives the left endpoint of the strip cross-compatibility
law for every actual signed heat response. -/
theorem actualWeightedHeatS0_zero_comp_actualWeightedHeatResponse (hc1 : 1 ≤ c) (θ : ℝ) :
    (actualWeightedHeatS0 (c := c) hc1 hm (θ := 0) le_rfl (by norm_num)).comp
      (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) θ) =
    actualWeightedHeatResponse (c := c) (m := m) (hm := hm) θ := by
  rw [actualWeightedHeatS0_zero]
  simp

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatResponse
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatResponse_value
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.norm_actualWeightedHeatResponse_le
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatS0_zero_comp_actualWeightedHeatResponse
