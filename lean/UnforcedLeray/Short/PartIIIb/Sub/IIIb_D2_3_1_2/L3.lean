import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K4

/-!
# Ward `X₀` axisymmetry (`PartIII-b:IIIb-D2/3/1/2/3`, final assembly)

Source of record: `the November 2 reference manuscript` lines 4171-4178.
`WardX0Axi` follows from `wardX0Axi_of` (Sub file `IIIb-D2_3_1_2_3`) applied to the four
equivariance statements proved in `K2` (`sepWEquivariance`), `K3` (`oldPhysRotEquiv`) and
`K4` (`oldPhysReflEquiv`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Ward `X₀` axisymmetry** (`PartIII-b:IIIb-D2/3/1/2/3`): the axisymmetric Ward
statement `WardX0Axi` holds. -/
theorem wardX0Axi_all : WardX0Axi :=
  wardX0Axi_of sepWEquivariance oldPhysRotEquiv oldPhysReflEquiv

end UnforcedLeray.Short.PartIIIb.Concrete
