import UnforcedLeray.Short.PartI.Sub.T05Class
import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.SlicePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.VelocityDecayOfEnergy
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound

/-!
# Part I, task `PartI:T08/4/1/1/1/2/1/2` (`TrainLocalBoundsBUC`): uniform cell energy bound

Source of record: `the November 2 reference manuscript`, lines 276-283.

Assembly. `trainLocalBoundsBUC_of` (in `Sub/T05Class.lean`) derives `TrainLocalBoundsBUC` from
`ClassicalPressureBound` and `ClassicalEnergyBound`. Both are now proved unconditionally:
`classicalPressureBound_of` (`Sub/T02_3.lean`) takes the three pressure leaves `SlicePoisson`,
`VelocityDecayOfEnergy`, `CylinderPoissonBound`, each proved in `Tasks/ClassicalOdd/`, and
`classicalEnergyBound` is proved in `Tasks/ClassicalOdd/ClassicalEnergyBound.lean`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **`TrainLocalBoundsBUC`** (proved, lines 276-283): assembly of the proved pressure bound
(`classicalPressureBound_of` applied to `slicePoisson`, `velocityDecayOfEnergy`,
`cylinderPoissonBound`) and the proved energy bound `classicalEnergyBound`. -/
theorem trainLocalBoundsBUC_proof : UnforcedLeray.Short.PartI.TrainLocalBoundsBUC :=
  trainLocalBoundsBUC_of
    (classicalPressureBound_of slicePoisson velocityDecayOfEnergy cylinderPoissonBound)
    classicalEnergyBound

end UnforcedLeray.Short.PartI
