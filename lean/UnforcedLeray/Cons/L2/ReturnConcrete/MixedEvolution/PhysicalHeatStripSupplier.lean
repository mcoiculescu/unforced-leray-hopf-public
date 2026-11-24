import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatResponseContinuity
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Volterra
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatSemigroup

/-!
# The actual short-strip physical heat supplier

This instantiates the Volterra heat-family record with the literal weighted B0284 heat and signed
B0296 heat-divergence response on actual zero-circulation states and actual weighted fluxes.
The zero extension of S₀ outside `[0,1]` only fills its global age parameter; all supplier laws
and estimates are on the physical strip.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Set
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Totalized actual S₀ family: literal physical heat on `[0,1]`, zero outside. -/
noncomputable def actualWeightedHeatS0Totalized {c m : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (t : ℝ) :
    ActualVorticity (c := c) (m := m) hm →L[ℝ]
      ActualVorticity (c := c) (m := m) hm := by
  by_cases ht0 : 0 ≤ t
  · by_cases ht1 : t ≤ 1
    · exact actualWeightedHeatS0 (c := c) hc1 hm ht0 ht1
    · exact 0
  · exact 0

/-- The literal physical short-strip heat and response maps satisfy every field of the Volterra
heat supplier. -/
noncomputable def actualPhysicalWeightedHeatStripSupplier {c m : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) :
    WeightedHeatStripSupplier (c := c) (m := m) hm where
  S₀ := actualWeightedHeatS0Totalized hc1 hm
  S := actualWeightedHeatResponse (c := c) (m := m) (hm := hm)
  M₀ := max 1 ((1 + c ^ 2 / 4) ^ (m / 2) *
    (2 ^ (m / 2) * ∫ z : Plane, axialHeatMomentDensity 1 m z))
  C₀ := 2 * ((1 + c ^ 2 / 4) ^ (m / 2) *
    (2 ^ (m / 2) * ∫ z : Plane, gradKernelAxialMomentDensity 1 m z))
  S₀_zero := by
    simp [actualWeightedHeatS0Totalized, actualWeightedHeatS0_zero]
  norm_S₀_le := by
    intro t ht0 ht1
    simp only [actualWeightedHeatS0Totalized, dif_pos ht0, dif_pos ht1]
    exact norm_actualWeightedHeatS0_le (c := c) (m := m) hc1 hm ht0 ht1
  norm_S_le := by
    intro t ht0 ht1
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (norm_actualWeightedHeatResponse_le (c := c) (m := m) (hm := hm) ht0 ht1)
  continuousOn_S₀ := by
    intro x
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hcont := continuous_actualWeightedHeatS0_apply hc1 hm x
    have hEq : (fun t : Icc (0 : ℝ) 1 =>
        actualWeightedHeatS0Totalized hc1 hm (t : ℝ) x) =
      (fun t : Icc (0 : ℝ) 1 =>
        actualWeightedHeatS0 (c := c) hc1 hm t.property.1 t.property.2 x) := by
      funext t
      have ht := Set.mem_Icc.mp t.property
      simp [actualWeightedHeatS0Totalized, ht.1, ht.2]
    change Continuous (fun t : Icc (0 : ℝ) 1 =>
      actualWeightedHeatS0Totalized hc1 hm (t : ℝ) x)
    rw [hEq]
    exact hcont
  continuousOn_S := by
    intro y
    exact continuousOn_actualWeightedHeatResponse_apply hc1 hm y
  S₀_comp_S₀ := by
    intro a b ha hb hsum
    have ha1 : a ≤ 1 := by linarith
    have hb1 : b ≤ 1 := by linarith
    have hsum0 : 0 ≤ a + b := add_nonneg ha hb
    have hactual := actualWeightedHeatS0_comp_of_nonneg (c := c) (m := m)
      hc1 hm ha hb ha1 hb1 hsum
    apply ContinuousLinearMap.ext
    intro x
    simpa [actualWeightedHeatS0Totalized, ha, hb, ha1, hb1, hsum0, hsum] using
      congrArg (fun L : ActualVorticity (c := c) (m := m) hm →L[ℝ]
        ActualVorticity (c := c) (m := m) hm => L x) hactual
  S₀_comp_S := by
    intro a b ha hb hsum
    have hb0 : 0 ≤ b := le_of_lt hb
    have ha1 : a ≤ 1 := by linarith
    have hb1 : b ≤ 1 := by linarith
    have hsum0 : 0 ≤ a + b := add_nonneg ha hb.le
    have hactual := actualWeightedHeatS0_comp_actualWeightedHeatResponse
      (c := c) (m := m) hc1 hm ha hb ha1 hsum
    apply ContinuousLinearMap.ext
    intro F
    simpa [actualWeightedHeatS0Totalized, ha, hb0, ha1, hb1, hsum0, hsum] using hactual F

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualPhysicalWeightedHeatStripSupplier
