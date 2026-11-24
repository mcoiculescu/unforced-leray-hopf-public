import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2.Reduce
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2.Closed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2.Periodize
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_2.Schwartz

/-!
# `FlatForceSmooth` (decomposition of `PartIII-b:C/flatset/col/1/2`)

Source of record `the November 2 reference manuscript`: 4594-4596, 4976, 4988.

Assembly of the three leaves: `flatForceClosed` (`Closed.lean`, components of `f_A` as lattice
sums of `ftF1`, `ftF2`), `periodizeSchwartzSmooth` (`Periodize.lean`, the `c`-periodization of a
Schwartz function is `C^∞`) and `flatTermSchwartz` (`Schwartz.lean`, `ftF1, ftF2` are Schwartz
for `a > 0`), through `flatForceSmooth_of` (`Reduce.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatForceSmooth : FlatForceSmooth :=
  flatForceSmooth_of flatForceClosed periodizeSchwartzSmooth flatTermSchwartz

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
