import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2_1.EqConv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2_1.ConvStrip
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_2_1_2_1.Reduce

/-!
# Fibre strong continuity of the planar heat (assembly of `heatFiberCont_holds`)

Source `the November 2 reference manuscript` lines 1650-1656.

Assembles the three leaf statements: `PlaneHeatEqConv` (`EqConv.lean`), `VecConvStripCont`
(`ConvStrip.lean`, via `vecConvStripCont_holds`) and `HeatFiberContReduce` (`Reduce.lean`), through
`heatFiberCont_holds_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong

/-- Fibre strong continuity of the planar heat at time `0` (tex 1650-1656). -/
theorem heatFiberCont_holds (c : ℝ) (hc : 0 < c) :
    UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong.HeatFiberCont c :=
  heatFiberCont_holds_of c planeHeatEqConv_holds (vecConvStripCont_holds c hc)
    (heatFiberContReduce_holds c)

end UnforcedLeray.Short.PartIIIb.Concrete.HeatStrong
