import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2.FiberCont
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2.FiberBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2.FibreBasic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2.AgeFormula
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2.AgeMass
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2.AgeMeas

/-!
# Strong continuity at age `0` of the age-dependent cylinder heat (assembly)

Source `the November 2 reference manuscript` lines 1650-1656.

Assembles the six leaf statements (`FiberCont`, `FiberBound`, `FibreBasic`, `AgeFormula`,
`AgeMass`, `AgeMeas`) through `tendsto_heatH_heatTime_zero_of` of the parent file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

theorem tendsto_heatH_heatTime_zero (c ν : ℝ) (hc : 0 < c)
    (g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) :
    Filter.Tendsto (fun s : ℝ => UnforcedLeray.B0224.heatH hc
        (UnforcedLeray.B0224.measurable_heatTime ν s) g)
      (nhdsWithin 0 (Set.Ici 0)) (nhds g) :=
  UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.tendsto_heatH_heatTime_zero_of c ν hc
    (heatFiberCont_holds c hc) (heatFiberBound_holds c hc) (heatFibreBasic_holds c)
    (heatAgeFormula_holds c) (heatAgeMass_holds c) (heatAgeMeas_holds c) g

end UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong
