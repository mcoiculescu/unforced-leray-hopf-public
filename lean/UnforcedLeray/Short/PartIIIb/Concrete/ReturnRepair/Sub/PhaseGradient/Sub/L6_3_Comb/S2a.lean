import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1.L4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1.L5

/-!
# `kerIntKdDeriv` (`PartIII-b:C/rep/2/6/3/2/1`)

Source `the November 2 reference manuscript` lines 3603-3626, 3800-3807, 4171-4200.
The statement `KerIntKdDeriv` is the `τ`-derivative of the complex kernel integral. It is
`kerIntKdDeriv_of` applied to the five analytic inputs `kerIntShift` (L1), `extIntPointDeriv` (L2),
`extIntMeasurable` (L3), `extIntKdIntegrable` (L4) and `extIntKdLipschitz` (L5).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`kerIntKdDeriv`** (`PartIII-b:C/rep/2/6/3/2/1`): differentiation of the kernel integral in `τ`. -/
theorem kerIntKdDeriv : KerIntKdDeriv :=
  kerIntKdDeriv_of kerIntShift extIntPointDeriv extIntMeasurable extIntKdIntegrable
    extIntKdLipschitz

end UnforcedLeray.Short.PartIIIb.Concrete
