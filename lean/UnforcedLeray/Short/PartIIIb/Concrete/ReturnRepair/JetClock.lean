import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L3

/-!
# `jetClock` (`PartIII-b:C/rep/7`, source 5438-5458, `repair:exact-jet-clock`)

The sequence statement `D.JetClock` from the three kernel lemmas:
`newtonVCutBound` (`PartIII-b:C/rep/7/1`), `streamCutThird` (`PartIII-b:C/rep/7/2`) and
`n0cutLeN1` (`PartIII-b:C/rep/7/3`), via `jetClock_of` (`Sub/PartIII-b_C_rep_7.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`jetClock`.** The sequence statement `D.JetClock` under the repair standing hypotheses. -/
theorem jetClock (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.JetClock :=
  jetClock_of D hst (newtonVCutBound _) (streamCutThird _) n0cutLeN1

end UnforcedLeray.Short.PartIIIb.Concrete
