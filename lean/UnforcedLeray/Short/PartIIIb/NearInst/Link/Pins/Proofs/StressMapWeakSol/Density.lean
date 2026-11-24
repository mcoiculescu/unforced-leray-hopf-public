import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5_3
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Density.RealDense

/-!
# `PartIII-b:C/near/pins/5/3`: `SWDensity` from `SWRealDense`

Source `the November 2 reference manuscript`
1678 (completion from smooth tensors), 2698-2700, 3874.

`swDensity_of` (Sub 5/3) reduces `SWDensity` to the real density `SWRealDense`, which is proved in
`Density.RealDense` (task 5/3/2).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- **`SWDensity`** (source 1678, 2698-2700): the real density of smooth band tests in `H_T`
transfers to the stress density on `Z`. -/
theorem swDensity : SWDensity := swDensity_of swRealDense

end UnforcedLeray.Short.PartIIIb.NearInst
