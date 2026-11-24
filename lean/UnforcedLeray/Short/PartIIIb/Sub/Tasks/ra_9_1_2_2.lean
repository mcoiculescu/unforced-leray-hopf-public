import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_2
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_2_3

/-!
# `PartIII-b:C/asrc/ra/9/1/2/2` : `RingLapRule` from the second-order meridional chain rule

Source: `the November 2 reference manuscript` lines 5034-5039.
The rule is `ringLapRule_of` applied to `ringLapMerChain` (task 2/3).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ringLapRule : RingLapRule := ringLapRule_of ringLapMerChain

end UnforcedLeray.Short.PartIIIb.Concrete
