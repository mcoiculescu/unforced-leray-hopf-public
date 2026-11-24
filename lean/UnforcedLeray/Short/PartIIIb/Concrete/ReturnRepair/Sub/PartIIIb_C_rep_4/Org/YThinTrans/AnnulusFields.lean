import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.Reduction
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.TwoPeriod
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.ChartPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.ChartMass
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.RepAE

/-!
# `PartIII-b:C/rep/4/2/org/3/3`: `AnnulusFields` (wrapper)

Source `the November 2 reference manuscript` 3669-3674 (`sep:thin-global`),
3730, 4163-4168, 5342-5355, 5571-5576. Proof: `annulusFields_of` applied to the four leaves
`twoPeriodLtau`, `chartMassLe_of chartPhaseNorm`, `oldThinPhysAE`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`AnnulusFields`** (source 3669-3674, 3730, 5342-5355, 5571-5576). -/
theorem annulusFields (dm dp : ℝ) : AnnulusFields dm dp :=
  annulusFields_of twoPeriodLtau (chartMassLe_of chartPhaseNorm) oldThinPhysAE dm dp

end UnforcedLeray.Short.PartIIIb.Concrete
