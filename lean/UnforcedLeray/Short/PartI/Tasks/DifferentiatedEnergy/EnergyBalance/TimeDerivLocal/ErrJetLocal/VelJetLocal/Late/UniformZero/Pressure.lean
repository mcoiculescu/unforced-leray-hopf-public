import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3
import UnforcedLeray.Short.PartI.TrainClass
import UnforcedLeray.Short.PartI.Sub.T02_3
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.SlicePoisson
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.VelocityDecayOfEnergy
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3/1` (`TrainPressureBounded`)

Source: `the November 2 reference manuscript` lines 273-275.  A `BUC` train is a
classical solution on `[0, S]` with bounded derivatives and decaying pressure, so the proved
`classicalPressureBound_of slicePoisson velocityDecayOfEnergy cylinderPoissonBound` applies.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem trainPressureBounded_proof : UnforcedLeray.Short.PartI.TrainPressureBounded := by
  intro ν c hν hc tr htr S hS
  obtain ⟨M, hM⟩ := classicalPressureBound_of slicePoisson velocityDecayOfEnergy
    cylinderPoissonBound ν c S tr.v tr.p hν hc hS (trainSol_isClassicalOn tr S)
    (htr S hS.le) (trainSol_pressureDecayOn tr S)
  exact ⟨M, fun r hr z => hM r hr z⟩

end UnforcedLeray.Short.PartI
