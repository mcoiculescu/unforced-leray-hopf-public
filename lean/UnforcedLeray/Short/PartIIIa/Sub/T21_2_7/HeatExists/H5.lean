import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H5.S0Dual
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H5.S0Time

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/5`: (H5) the weak heat equation of the free flow

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. Statement: `HeatExists/Leaves.lean` (`AdjHeatS0Weak`).
Assembly: `adjHeatS0Weak_of` from the dual identity `adjHeatS0Dual` (H5.1) and the time identity
`adjHeatS0Time` (H5.2).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjHeatS0Weak (m : ℝ) (hm : 8 < m) : AdjHeatS0Weak m :=
  adjHeatS0Weak_of m (adjHeatS0Dual m hm) (adjHeatS0Time m hm)

end UnforcedLeray.Short.IIIa
