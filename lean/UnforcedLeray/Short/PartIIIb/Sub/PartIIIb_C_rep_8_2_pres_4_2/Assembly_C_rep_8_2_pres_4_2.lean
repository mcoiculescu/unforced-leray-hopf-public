import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_lp

/-!
# `PartIII-b:C/rep/8/2/pres/4/2`: `CoefChgQuant D`

Source: `the November 2 reference manuscript` lines 5287-5289, 2715-2725.
Assembles `coefChgQuant` from `coefChgQuant_of`, `coefChgLp`, `coefChgSup`, and
`nuLeOneRhoNonneg`. Placed in `Assembly_C_rep_8_2_pres_4_2.lean` to avoid an import cycle
with `_4_2_2` and `_4_2_lp`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem coefChgQuant (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : CoefChgQuant D :=
  coefChgQuant_of D (coefChgLp D hst) (coefChgSup D hst) (nuLeOneRhoNonneg D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
