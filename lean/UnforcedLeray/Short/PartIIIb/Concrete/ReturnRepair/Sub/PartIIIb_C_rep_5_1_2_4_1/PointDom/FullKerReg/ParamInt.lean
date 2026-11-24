import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Two derivatives under the integral sign (helper for `pdFullKerReg`, `pdYKerBound`)

A parametric integral `Ψ(p) = ∫ F p u dμ(u)` on an open set `U` of a normed space: if `F(·,u)` has a
`C²`-type derivative structure with integrable `U`-uniform majorants, then `Ψ` has a derivative
`∫ F1`, that derivative has a derivative `∫ F2`, and `∫ F2` is continuous.  Hence `Ψ` is `C²` on
`U`, with the derivatives bounded by the integrals of the majorants.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem paramInt_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure ℝ)
    {U : Set E} (hU : IsOpen U)
    (F : E → ℝ → ℝ) (F1 : E → ℝ → (E →L[ℝ] ℝ)) (F2 : E → ℝ → (E →L[ℝ] E →L[ℝ] ℝ))
    (B0 B1 B2 : ℝ → ℝ) (hB0 : Integrable B0 μ) (hB1 : Integrable B1 μ) (hB2 : Integrable B2 μ)
    (hd1 : ∀ᵐ u ∂μ, ∀ p ∈ U, HasFDerivAt (fun q => F q u) (F1 p u) p)
    (hd2 : ∀ᵐ u ∂μ, ∀ p ∈ U, HasFDerivAt (fun q => F1 q u) (F2 p u) p)
    (hc2 : ∀ᵐ u ∂μ, ContinuousOn (fun p => F2 p u) U)
    (m0 : ∀ p ∈ U, AEStronglyMeasurable (F p) μ)
    (m1 : ∀ p ∈ U, AEStronglyMeasurable (F1 p) μ)
    (m2 : ∀ p ∈ U, AEStronglyMeasurable (F2 p) μ)
    (b0 : ∀ p ∈ U, ∀ᵐ u ∂μ, ‖F p u‖ ≤ B0 u)
    (b1 : ∀ᵐ u ∂μ, ∀ p ∈ U, ‖F1 p u‖ ≤ B1 u)
    (b2 : ∀ᵐ u ∂μ, ∀ p ∈ U, ‖F2 p u‖ ≤ B2 u) :
    (∀ p ∈ U, HasFDerivAt (fun q => ∫ u, F q u ∂μ) (∫ u, F1 p u ∂μ) p) ∧
    (∀ p ∈ U, HasFDerivAt (fun q => ∫ u, F1 q u ∂μ) (∫ u, F2 p u ∂μ) p) ∧
    ContinuousOn (fun p => ∫ u, F2 p u ∂μ) U := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, ?_⟩
  · refine hasFDerivAt_integral_of_dominated_of_fderiv_le (hU.mem_nhds hp)
      (Filter.eventually_of_mem (hU.mem_nhds hp) fun q hq => m0 q hq)
      (Integrable.mono' hB0 (m0 p hp) (b0 p hp))
      (m1 p hp) b1 hB1 hd1
  · refine hasFDerivAt_integral_of_dominated_of_fderiv_le (hU.mem_nhds hp)
      (Filter.eventually_of_mem (hU.mem_nhds hp) fun q hq => m1 q hq)
      (Integrable.mono' hB1 (m1 p hp) (b1.mono fun u hu => hu p hp))
      (m2 p hp) b2 hB2 hd2
  · refine continuousOn_of_dominated (fun p hp => m2 p hp)
      (fun p hp => b2.mono fun u hu => hu p hp) hB2 ?_
    exact hc2

end UnforcedLeray.Short.PartIIIb.Concrete

end
