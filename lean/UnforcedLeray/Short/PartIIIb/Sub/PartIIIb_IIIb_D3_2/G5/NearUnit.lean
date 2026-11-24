import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5Org

/-!
# `PartIII-b:IIIb-D3/2/G5/1`: `FlatNearUnit`

Source `the November 2 reference manuscript` lines 3874-3887
(`near:flat-bound`, `D₀ = I + M₀S₀` a unit). The unit property is the field `flatUnit` of
`SeqData.RepairStanding` (`Concrete/ReturnRepair/Estimates.lean`), so the statement is the
projection of that field.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5

theorem flatNearUnit (D : SeqData) : FlatNearUnit D :=
  fun _ _ hst => hst.flatUnit

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G5
