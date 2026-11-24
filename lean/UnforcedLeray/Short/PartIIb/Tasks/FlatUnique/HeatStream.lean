import UnforcedLeray.Short.PartIIb.Sub.T11_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.NiceClosure
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Smooth
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Cpd
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.HeatEq
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Contraction
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Tendsto
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.DerivMemLp

/-!
# Part II-b, leaf `PartII-b:T11/3` (`HeatStreamDual`): assembly

Source of record: `the November 2 reference manuscript` lines 1923-1927.
Assembles the heat-flow dual statement from the proved leaves `T11/3/1`-`T11/3/9` through the
proved conditional `heatStreamDual_of` (`Sub/T11_3.lean`).
-/

set_option autoImplicit false

theorem heatStreamDual : UnforcedLeray.Short.IIb.HeatStreamDual :=
  UnforcedLeray.Short.IIb.heatStreamDual_of
    UnforcedLeray.Short.IIb.niceStreamClosure
    UnforcedLeray.Short.IIb.heatConvSmooth
    UnforcedLeray.Short.IIb.heatConvCpd
    UnforcedLeray.Short.IIb.heatConvEq
    UnforcedLeray.Short.IIb.heatConvContraction
    UnforcedLeray.Short.IIb.heatConvTendsto
    UnforcedLeray.Short.IIb.heatDerivMemLp

#print axioms heatStreamDual
