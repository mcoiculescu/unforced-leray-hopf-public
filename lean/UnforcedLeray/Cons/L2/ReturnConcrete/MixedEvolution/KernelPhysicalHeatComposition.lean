import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelPhysicalHeatCovariance
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelFluxL2Covariance
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatSemigroup

/-!
# Actual weighted S₀/response composition on the physical vorticity space

The normalized-cell Gaussian covariance is transported through the proved weighted input
identifications to the literal zero-circulation state and response maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Positive-age actual physical composition law: applying the weighted heat `S₀(a)` to the
actual signed response at age `b` gives the same actual response at the summed age. -/
theorem actualWeightedHeatS0_comp_actualWeightedHeatResponse_of_pos
    {c m α β : ℝ} [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m)
    (hα : 0 < α) (hβ : 0 < β) (hα1 : α ≤ 1) (hβ1 : β ≤ 1)
    (hsum1 : α + β ≤ 1)
    (F : ActualFlux (c := c) (m := m)) :
    (actualWeightedHeatS0 (c := c) hc1 hm (le_of_lt hα) hα1).comp
      (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) β) F =
    actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (α + β) F := by
  apply Subtype.ext
  apply xColumnHeatInput_injective (Fact.out : 0 < c) hm
  change xColumnHeatInput (Fact.out : 0 < c) hm
      (actualWeightedHeatS0 (c := c) hc1 hm (le_of_lt hα) hα1
        (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) β F)) =
    xColumnHeatInput (Fact.out : 0 < c) hm
      (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (α + β) F)
  rw [actualWeightedHeatS0_apply_of_pos (c := c) (m := m) hc1 hm hα hα1
    (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) β F)]
  rw [actualWeightedHeatResponse_apply_of_pos (c := c) (m := m) (hm := hm)
    hβ hβ1 F]
  rw [actualWeightedHeatResponse_apply_of_pos (c := c) (m := m) (hm := hm)
    (add_pos hα hβ) hsum1 F]
  calc
    xColumnHeatInput (Fact.out : 0 < c) hm
        (xColumnHeatS0Positive (Fact.out : 0 < c) hm hα hα1
          (xFluxNegativeHeatDivXCLM (Fact.out : 0 < c) hm hβ hβ1 F)) =
        HeatCylinder.heatL2CLM (Fact.out : 0 < c) α
          (xColumnHeatInput (Fact.out : 0 < c) hm
            (xFluxNegativeHeatDivXCLM (Fact.out : 0 < c) hm hβ hβ1 F)) :=
      xColumnHeatInput_xColumnHeatS0Positive_eq_heatL2CLM
        (Fact.out : 0 < c) hc1 hm hα hα1 _
    _ = HeatCylinder.heatL2CLM (Fact.out : 0 < c) α
          (xFluxNegativeHeatDivL2CLM (Fact.out : 0 < c) hm hβ F) := by
      rw [xColumnHeatInput_xFluxNegativeHeatDivXCLM_eq
        (Fact.out : 0 < c) hc1 hm hβ hβ1 F]
    _ = xFluxNegativeHeatDivL2CLM (Fact.out : 0 < c) hm (add_pos hα hβ) F :=
      heatL2CLM_comp_xFluxNegativeHeatDivL2CLM
        (Fact.out : 0 < c) hm hα hβ F
    _ = xColumnHeatInput (Fact.out : 0 < c) hm
          (xFluxNegativeHeatDivXCLM (Fact.out : 0 < c) hm (add_pos hα hβ) hsum1 F) :=
      (xColumnHeatInput_xFluxNegativeHeatDivXCLM_eq
        (Fact.out : 0 < c) hc1 hm (add_pos hα hβ) hsum1 F).symm

/-- Exact nonnegative-strip compatibility for the actual physical heat and response maps. The
response age is strictly positive, exactly as required by the Volterra strip law. -/
theorem actualWeightedHeatS0_comp_actualWeightedHeatResponse
    {c m α β : ℝ} [Fact (0 < c)] (hc1 : 1 ≤ c) (hm : 1 ≤ m)
    (hα0 : 0 ≤ α) (hβ : 0 < β) (hα1 : α ≤ 1) (hsum1 : α + β ≤ 1)
    (F : ActualFlux (c := c) (m := m)) :
    (actualWeightedHeatS0 (c := c) hc1 hm hα0 hα1).comp
      (actualWeightedHeatResponse (c := c) (m := m) (hm := hm) β) F =
    actualWeightedHeatResponse (c := c) (m := m) (hm := hm) (α + β) F := by
  by_cases hα : α = 0
  · subst α
    have h := actualWeightedHeatS0_zero_comp_actualWeightedHeatResponse
      (c := c) (m := m) (hm := hm) hc1 β
    simpa using congrArg (fun L : ActualVorticity (c := c) (m := m) hm →L[ℝ]
        ActualVorticity (c := c) (m := m) hm => L F) h
  · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hα)
    have hβ1 : β ≤ 1 := by linarith
    exact actualWeightedHeatS0_comp_actualWeightedHeatResponse_of_pos
      (c := c) (m := m) hc1 hm hαpos hβ hα1 hβ1 hsum1 F

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatS0_comp_actualWeightedHeatResponse_of_pos
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatS0_comp_actualWeightedHeatResponse
