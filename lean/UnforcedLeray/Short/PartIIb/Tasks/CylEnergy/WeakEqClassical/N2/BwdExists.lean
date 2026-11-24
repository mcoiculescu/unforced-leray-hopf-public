import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1.Route
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists.TrainCylCoeff
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists.LocBase
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists.LocStep
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists.LocAssemble
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists.JointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardLimit
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.DuhamelToPde

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T22/2/3/1`**: existence of a bounded classical periodic backward solution
(SP 2100-2105), assembled from the route in `Sub/PartIIb_T22_2_3_1/Route.lean`. -/
theorem bwdExists : UnforcedLeray.Short.IIb.BwdExists :=
  BwdRoute.bwdExists_of_route trainCylCoeff
    (CylPDE.duhamelExists_of_parts CylPDE.picardIterates CylPDE.picardLimit)
    CylPDE.duhamelToPde locBase BwdRoute.locStep BwdRoute.locAssemble BwdRoute.fwdJointSmooth

end UnforcedLeray.Short.IIb
