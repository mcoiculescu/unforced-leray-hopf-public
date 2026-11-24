import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.A
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B1a
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.B1b

/-!
# `wardX0SmoothInf_proved` (`PartIII-b:IIIb-D2/3/2/11/2/2`, source 3604-3621, 4161-4186)

Source of record: `the November 2 reference manuscript`.
`WardX0SmoothInf` (joint `C^∞` of `X₀ = wardX0` on the young region) follows from
`wardX0SmoothInf_proved_of` applied to the three proved source facts

* `smoothOldSource_proved` (A.lean, source 4155-4166),
* `oldPhysSmooth_proved` (B1a.lean, source 3604-3621, 4161-4186),
* `sepWSmoothTop_proved` (B1b.lean, source 3604-3621).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **`wardX0SmoothInf_proved`** (source 3604-3621, 4161-4186): `X₀` is jointly `C^∞` on the young
region for smooth old data, assembled from the three proved source facts. -/
theorem wardX0SmoothInf_proved : WardX0SmoothInf :=
  wardX0SmoothInf_proved_of smoothOldSource_proved oldPhysSmooth_proved sepWSmoothTop_proved

end UnforcedLeray.Short.PartIIIb.Concrete
