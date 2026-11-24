import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_1

/-!
# `PartIII-b:C/asrc/kflat/2` : `frakTLinear`

Source of record: `the November 2 reference manuscript` (4605-4612, 4985).

Assembles the four leaves of `FrakTLinear` (`kflat/2/1` duhIntegrable, `kflat/2/2` xiDLinear,
`kflat/2/3` kcMerLinear, `kflat/1/1` frakTMeas) through `frakTLinear_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`A ↦ 𝔗A` is linear a.e. on the old region** (the leaf statement `FrakTLinear`). -/
theorem frakTLinear (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : FrakTLinear as χf m :=
  frakTLinear_of as χf m (duhIntegrable as χf m) (xiDLinear m) (kcMerLinear m)
    (frakTMeas as χf m)

end UnforcedLeray.Short.PartIIIb.Concrete
