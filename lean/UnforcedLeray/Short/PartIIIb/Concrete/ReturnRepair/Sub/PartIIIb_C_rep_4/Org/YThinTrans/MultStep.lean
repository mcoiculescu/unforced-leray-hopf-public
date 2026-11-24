import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MultStepOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MultStep.PointMass
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.MultStep.MassL223
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.ChartPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Annulus.ChartMass
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransSepDom
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransMajFacts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.ThinChart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.RepChart

/-!
# `PartIII-b:C/rep/4/2/org/3/4`: `transMultiplierStep`

Source `the November 2 reference manuscript` 5312-5352, 3669-3701, 3729-3730.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The multiplier step along the sequence** (source 5312-5352, 3669-3701, 3729-3730). -/
theorem transMultiplierStep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : TransMultiplierStep Pl σ₀ mZ dm dp :=
  transMultiplierStep_of transSepDom transMajFacts (thinChart dm dp) (repChart dm dp)
    transMajPointMass transMajMassL223 (chartMassLe_of chartPhaseNorm)

end UnforcedLeray.Short.PartIIIb.Concrete

end
