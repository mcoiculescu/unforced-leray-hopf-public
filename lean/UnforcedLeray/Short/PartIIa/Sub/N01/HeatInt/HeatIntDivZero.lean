import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2_4_4
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatSliceDivZero
import UnforcedLeray.Short.PartIIa.Sub.N01.HeatInt.HeatIntFderivFormula

/-!
# `PartII-a:N01/9/1/2/4/4` (heat integral): `HeatIntDivZero`

Source `the November 2 reference manuscript`
lines 1684-1689, 3379-3383, 3426-3430.  The two ingredients are the slice divergence
vanishing (`heatSliceDivZero`) and the differentiation formula of the heat integral
(`heatIntFderivFormula`); they are combined by `heatIntDivZero_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIa.N01

theorem heatIntDivZero : UnforcedLeray.Short.PartIIa.N01.HeatIntDivZero :=
  heatIntDivZero_of heatSliceDivZero heatIntFderivFormula

end UnforcedLeray.Short.PartIIa.N01
