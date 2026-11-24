import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.SliceOrth.DualVanish
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.SliceOrth.JointNull
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.SliceOrth.Pointwise
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.SliceOrth.ProductFormula

/-!
# Part II-b, task `PartII-b:T11/5` (`FlatSliceOrthogonality`): assembly

Source of record: `the November 2 reference manuscript` lines 1923-1938.
Assembles the flat slice orthogonality from the proved leaves `T11/5/1`-`T11/5/4`
(`sliceDualVanish`, `sliceJointNull`, `slicePointwise`, `sliceProductFormula`) and the heat-flow
dual `heatStreamDual` (`T11/3`), through the proved conditional `flatSliceOrthogonality_of`
(`Sub/PartII-b_T11_5.lean`).
-/

set_option autoImplicit false

theorem flatSliceOrthogonality : UnforcedLeray.Short.IIb.FlatSliceOrthogonality :=
  UnforcedLeray.Short.IIb.flatSliceOrthogonality_of heatStreamDual
    UnforcedLeray.Short.IIb.sliceDualVanish UnforcedLeray.Short.IIb.sliceJointNull
    UnforcedLeray.Short.IIb.slicePointwise UnforcedLeray.Short.IIb.sliceProductFormula

#print axioms flatSliceOrthogonality
