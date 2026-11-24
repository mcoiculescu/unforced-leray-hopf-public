import UnforcedLeray.Short.PartI.Sub.T02_3_10
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.SliceSmooth
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.StripBound
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.DerivBounds
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.Continuity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.Decomp
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.ConvIdentity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.PressureIdentity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.FluxBound
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalEnergyBound.Limit

/-!
# Part I, task `PartI:T02/3/10`: the classical energy bound (assembler)

Source: `the November 2 reference manuscript`, lines 276-282. Assembles the eleven
leaf theorems through the compiled conditional `classicalEnergyBound_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem classicalEnergyBound : ClassicalEnergyBound :=
  classicalEnergyBound_of etaCutoffFacts (ebContinuous etaCutoffFacts) (ebHasDeriv etaCutoffFacts)
    (ebDecomp etaCutoffFacts ebSliceSmooth cellToolkit.1)
    (ebViscousIdentity etaCutoffFacts cellToolkit.1 cellToolkit.2 ebSliceSmooth)
    (ebConvIdentity etaCutoffFacts cellToolkit.1 cellToolkit.2 ebSliceSmooth)
    (ebPressureIdentity etaCutoffFacts cellToolkit.1 cellToolkit.2 ebSliceSmooth)
    (ebFluxBound (ebStripBound etaCutoffFacts) (ebDerivBounds ebSliceSmooth) ebSliceSmooth)
    (ebLimit etaCutoffFacts)

end UnforcedLeray.Short.PartI
