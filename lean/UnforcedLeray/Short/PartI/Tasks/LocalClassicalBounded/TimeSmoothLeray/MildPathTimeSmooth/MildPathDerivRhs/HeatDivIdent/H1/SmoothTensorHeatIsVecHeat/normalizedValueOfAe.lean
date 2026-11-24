import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1_2

/-!
# `normalizedValueOfAe`: the normalized value of an `H³` class is a.e. its periodic centered value

Proves `NormalizedValueOfAe` (defined in `PartI_T02_1_4_4_1_5_1_1_2.lean`, source
`the November 2 reference manuscript` lines 3594-3625). The periodic
representative `vectorH3PeriodicValueRep` agrees a.e. with the centered value on the cell
(`vectorH3PeriodicValueRep_ae_value`); two periodic functions that agree a.e. on the centered cell
agree a.e. on the normalized cell (`ae_eq_of_ae_centered_periodic`, as in `H3ValueLimit.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.HeatCylinder

theorem normalizedValueOfAe : NormalizedValueOfAe := by
  intro c hc X f hper _hcont hval
  have hcenter : vectorH3PeriodicValueRep hc X =ᵐ[UnforcedLeray.Cyl.cellμ c] f := by
    filter_upwards [vectorH3PeriodicValueRep_ae_value hc X, hval] with z h1 h2
    exact h1.trans h2
  have hglobal := ae_eq_of_ae_centered_periodic hc (periodic_vectorH3PeriodicValueRep hc X)
    hper hcenter
  filter_upwards [vectorH3NormalizedValue_coe_ae hc X, hglobal] with z h1 h2
  exact h1.trans h2

end UnforcedLeray.Short.PartI
