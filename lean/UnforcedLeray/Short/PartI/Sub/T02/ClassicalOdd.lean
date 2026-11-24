import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ReflectClassical
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ReflectBoundedDerivs
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ReflectPressureDecay
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.SlicePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.VelocityDecayOfEnergy
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalUniquenessBounded

/-!
# Part I, task `PartI:T02/3`: `ClassicalOdd` (assembly)

Source of record: `the November 2 reference manuscript`, line 288
("Uniqueness gives `v(-q,-η,s) = -v(q,η,s)`").

The statement `ClassicalOdd` is defined in `Short/PartI/Sub/T02.lean`. The argument
`classicalOdd_of` (in `Short/PartI/Sub/T02_3.lean`) reduces it to six leaf statements, and
`classicalPressureBound_of` reduces the pressure bound to three further leaves. Each leaf is
proved in its own module under `Short/PartI/Tasks/ClassicalOdd/`; this file only composes them.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- `ClassicalOdd`: a classical solution with bounded derivatives and decaying pressure is
centrally odd on `[0,T]`. -/
theorem classicalOdd : ClassicalOdd :=
  classicalOdd_of reflectClassical reflectBoundedDerivs reflectPressureDecay
    (classicalPressureBound_of slicePoisson velocityDecayOfEnergy cylinderPoissonBound)
    classicalEnergyBound
    (classicalUniquenessBounded_of classicalCutoffEnergyIneq)

end UnforcedLeray.Short.PartI
