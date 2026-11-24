import UnforcedLeray.Short.PartIIb.Sub.T22_1_10
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatPeriodic

/-!


Source: `the November 2 reference manuscript`, lines 2074-2093 and 2103-2105.
If every slice `F r` is `c`-periodic in the first variable (for `r ∈ [s, T]`), then so is
`G(τ) = ∫_s^τ H_{ν(τ-r)} F(r) dr`: the heat semigroup preserves periodicity (`heatPeriodic`), and
the integrand is then pointwise equal on the interval of integration.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.CylPDE

/-- **`T22/1/10/4`** Periodicity of `G(τ)` (`CRPer`). -/
theorem crPer : UnforcedLeray.Short.IIb.CylPDE.CRPer := by
  intro ν s T hν hsT F b hH c hcp τ hτ x
  have hτs : s ≤ τ := hτ.1
  have hτT : τ ≤ T := hτ.2
  unfold duhamelConv
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [Set.uIcc_of_le hτs] at hr
  have hrT : r ∈ Icc s T := ⟨hr.1, le_trans hr.2 hτT⟩
  exact (heatPeriodic c (F r) (hcp r hrT) (ν * (τ - r)) x).1

end UnforcedLeray.Short.IIb.CylPDE
