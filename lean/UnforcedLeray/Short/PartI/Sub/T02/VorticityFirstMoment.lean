import UnforcedLeray.Short.PartI.Sub.T02_4
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.ParabolicMinPrinciple
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.SechSupersolution
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.ParabolicSechBarrier
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.TrainDatumCurlSech
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.SechMomentIntegrable

/-!
# Part I, task `PartI:T02/4`: `VorticityFirstMoment` (unconditional assembly)

Source of record: `the November 2 reference manuscript`, lines 276-288 (the
vorticity equation with weight `1 + |η|`).  The statement is `VorticityFirstMoment` from
`Short/PartI/Sub/T02.lean`.

The proof applies the conditional glue `vorticityFirstMoment_of` (`Sub/T02_4.lean`) to the seven
leaf theorems, the comparison theorem `parabolicSechBarrier_of` being fed the minimum principle and
the sech supersolution property.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T02/4`**: the first moment of the vorticity of a classical solution with bounded
derivatives is finite (source lines 276-288). -/
theorem vorticityFirstMoment : VorticityFirstMoment :=
  vorticityFirstMoment_of localVorticityEquation curlRegularity
    (parabolicSechBarrier_of parabolicMinPrinciple sechSupersolution)
    trainDatumCurlSech sechMomentIntegrable

end UnforcedLeray.Short.PartI
