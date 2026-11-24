import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxHeatCLM
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Volterra

/-!
# Actual fixed-cylinder heat source on the Volterra spaces

This leaf restricts the concrete signed B0296 Gaussian heat-divergence map to the actual
zero-circulation vorticity space used by the train Volterra construction. The radial comparison
constant remains cylinder dependent, so this is fixed-parameter spatial data only.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.B0579

variable {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)

/-- The actual signed Gaussian source from two weighted flux columns into the closed
zero-circulation state space. Its ambient representative is literally B0296's `−heatDiv`. -/
def actualHeatDuhamelSource {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ActualFlux (c := c) (m := m) →L[ℝ] ActualVorticity (c := c) (m := m) hm := by
  let hθm : θ ≤ 1 := hθ1
  exact (xFluxNegativeHeatDivXCLM (Fact.out : 0 < c) hm hθ hθm).codRestrict
    (zeroCirculationSubmodule (c := c) (m := m) (by linarith : 1 / 2 < m))
    (xFluxNegativeHeatDivXCLM_mem_zeroCirculation (Fact.out : 0 < c) hm hθ hθm)

/-- Explicit fixed-cylinder constant in the short-time heat-divergence operator estimate. -/
def actualHeatDuhamelC0 : ℝ :=
  2 * (1 + c ^ 2 / 4) ^ (m / 2) *
    (2 ^ (m / 2) * ∫ z : Plane, gradKernelAxialMomentDensity 1 m z)

theorem actualHeatDuhamelSource_apply_eq_integral {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (F : ActualFlux (c := c) (m := m)) :
    ((actualHeatDuhamelSource (c := c) (m := m) hm hθ hθ1 F :
      ActualVorticity (c := c) (m := m) hm) : X c m) =
      (memLp_xFlux_negativeHeatDiv_fst_X (Fact.out : 0 < c) hm hθ hθ1 F).toLp
        (fun z => (negativeHeatDiv θ (xFluxPeriodicTensor (Fact.out : 0 < c) F) z).1) := by
  rfl

theorem norm_actualHeatDuhamelSource_apply_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (F : ActualFlux (c := c) (m := m)) :
    ‖actualHeatDuhamelSource (c := c) (m := m) hm hθ hθ1 F‖ ≤
      2 * ((1 + c ^ 2 / 4) ^ (m / 2) *
        (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ z : Plane, gradKernelAxialMomentDensity 1 m z)) * ‖F‖ := by
  change ‖xFluxNegativeHeatDivXLinear (Fact.out : 0 < c) hm hθ hθ1 F‖ ≤ _
  have h := norm_xFluxNegativeHeatDivXLinear_le (Fact.out : 0 < c) hm hθ hθ1 F
  have h0 : ‖F 0‖ ≤ ‖F‖ := norm_le_pi_norm F 0
  have h1 : ‖F 1‖ ≤ ‖F‖ := norm_le_pi_norm F 1
  have hmoment : 0 ≤ ∫ z : Plane, gradKernelAxialMomentDensity 1 m z := by
    apply integral_nonneg_of_ae
    filter_upwards with z
    unfold gradKernelAxialMomentDensity
    positivity
  have hC : 0 ≤ (1 + c ^ 2 / 4) ^ (m / 2) *
      (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
        ∫ z : Plane, gradKernelAxialMomentDensity 1 m z) := by
    positivity
  calc
    ‖xFluxNegativeHeatDivXLinear (Fact.out : 0 < c) hm hθ hθ1 F‖ ≤
        ((1 + c ^ 2 / 4) ^ (m / 2) *
          (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
            ∫ z : Plane, gradKernelAxialMomentDensity 1 m z)) *
          (‖F 0‖ + ‖F 1‖) := h
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (add_le_add h0 h1) hC
    _ = _ := by ring

theorem actualHeatDuhamelC0_nonneg : 0 ≤ actualHeatDuhamelC0 (c := c) (m := m) := by
  have hmoment : 0 ≤ ∫ z : Plane, gradKernelAxialMomentDensity 1 m z := by
    apply integral_nonneg_of_ae
    filter_upwards with z
    unfold gradKernelAxialMomentDensity
    positivity
  dsimp [actualHeatDuhamelC0]
  positivity

/-- The actual heat-divergence CLM has the Volterra `θ^(-1/2)` bound, with a precise
fixed-cylinder constant. -/
theorem norm_actualHeatDuhamelSource_le {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ‖actualHeatDuhamelSource (c := c) (m := m) hm hθ hθ1‖ ≤
      actualHeatDuhamelC0 (c := c) (m := m) * θ ^ (-(1 / 2 : ℝ)) := by
  have hθpow : 0 ≤ θ ^ (-(1 / 2 : ℝ)) := (Real.rpow_pos_of_pos hθ _).le
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (actualHeatDuhamelC0_nonneg (c := c) (m := m)) hθpow) fun F => ?_
  have h := norm_actualHeatDuhamelSource_apply_le (c := c) (m := m) hm hθ hθ1 F
  calc
    ‖actualHeatDuhamelSource (c := c) (m := m) hm hθ hθ1 F‖ ≤
      2 * ((1 + c ^ 2 / 4) ^ (m / 2) *
        (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ z : Plane, gradKernelAxialMomentDensity 1 m z)) * ‖F‖ := h
    _ = actualHeatDuhamelC0 (c := c) (m := m) *
        θ ^ (-(1 / 2 : ℝ)) * ‖F‖ := by
      dsimp [actualHeatDuhamelC0]
      ring

#print axioms actualHeatDuhamelSource_apply_eq_integral
#print axioms norm_actualHeatDuhamelSource_apply_le
#print axioms norm_actualHeatDuhamelSource_le

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
