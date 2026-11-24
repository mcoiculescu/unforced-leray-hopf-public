import UnforcedLeray.Short.PartIIb.Sub.T22_1.Plan
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.EtaCosh
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardIterates
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.PicardLimit
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.DuhamelToPde

/-!


Source of record: `the November 2 reference manuscript`, lines 2074-2093, 2103-2105.
Proved by the reduction `CylPDE.cylClassicalExists_of_parts` (`Sub/T22_1/Plan.lean`) applied to the
leaves `trainCoeffBdd` (T22/1/1), `etaPowLeCosh` (T22/1/2), `duhamelExists_of_parts picardIterates
picardLimit` (T22/1/14, T22/1/15) and `duhamelToPde` (T22/1/16).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:T22/1`** `CylClassicalExists`, assembled from the 16 leaves. -/
theorem cylClassicalExists : CylClassicalExists :=
  CylPDE.cylClassicalExists_of_parts trainCoeffBdd CylPDE.etaPowLeCosh
    (CylPDE.duhamelExists_of_parts CylPDE.picardIterates CylPDE.picardLimit)
    CylPDE.duhamelToPde

end UnforcedLeray.Short.IIb

end
