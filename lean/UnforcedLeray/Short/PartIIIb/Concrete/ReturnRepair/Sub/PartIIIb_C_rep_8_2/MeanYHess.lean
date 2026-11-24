import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHessOrg.Main
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHessOrg.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHessOrg.XJetOff4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7.L1

/-!
# `PartIII-b:C/rep/8/2/2/2`: the Hessian bound for the mean `Y^mt`

Source `the November 2 reference manuscript`
5438-5448 and 5380-5387. The Hessian bound follows from the fourth-derivative jet bound
`XmtJetOff4` of `X^mt`, which is supplied by the Newton kernel bound `newtonVCutBound` and the
`m = 4` scaled-jet bound `scXJetOff4`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The mean Hessian bound for `Y^mt`** (source 5438-5448, 5380-5387). -/
theorem meanYHess (D : SeqData) {dm dp : ℝ} : D.MeanYHessSeq dm dp :=
  meanYHess_of D (xmtJetOff4_of (newtonVCutBound D.K.χo) (scXJetOff4 D.K.χy))

end UnforcedLeray.Short.PartIIIb.Concrete
end
