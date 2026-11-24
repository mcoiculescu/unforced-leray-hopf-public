import UnforcedLeray.Short.PartIIb.Sub.T11_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.PlanarTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.Commutator
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.PeriodicUnfold
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.Coeffs

/-!
# Part II-b, leaf `PartII-b:T11/1` (`FlatEqCellStream`): periodic stream tests (unconditional)

Source of record: `the November 2 reference manuscript`, the flat equation
`(μ + S - νsΔ_{q,η}) b = P_0 F` tested against planar solenoidal tests (SP 1923-1927), with the
periodic unfolding of the cell described in the proof sketch of `Sub/T11_1.lean`.

The conditional form `flatEqCellStream_of` is proved in `Sub/T11_1.lean`. Its four hypotheses are
discharged by the accepted leaves `cellStreamPlanarTest` (`PartII-b:T11/1/1`, `CellStream/PlanarTest`),
`cellStreamCommutator` (`T11/1/2`, `CellStream/Commutator`), `coordPeriodicUnfold` (`T11/1/3`,
`CellStream/PeriodicUnfold`) and `cellStreamCoeffs` (`T11/1/5`, `CellStream/Coeffs`, which uses
`hrBoxIntegrable`, `T11/1/4`, `CellStream/HrBox`). The statement `FlatEqCellStream` is unchanged.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Leaf `PartII-b:T11/1`** (`FlatEqCellStream`): the flat equation holds for `q`-periodic
streams `ψ` supported in `s > 0`, with the integral taken over the cell. -/
theorem flatEqCellStream : UnforcedLeray.Short.IIb.FlatEqCellStream :=
  flatEqCellStream_of cellStreamPlanarTest cellStreamCommutator coordPeriodicUnfold cellStreamCoeffs

end UnforcedLeray.Short.IIb
