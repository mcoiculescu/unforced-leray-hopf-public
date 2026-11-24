import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_2
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.JointRepVecC
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.LerayClassCont
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.LerayClassEnergy
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0DivFreeC
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0OrthC
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0CommWeakC
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.GaussianSliceMemLp
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.SmoothSliceWeak

/-!
# Part III-a, task `PartIII-a:T18/2/4/2`: Leray projection of the slices (assembly)

Target: `LerayProjectSlices` (`Sub/T18_2_4.lean`, SIZE S). The conditional wiring
`lerayProjectSlices_of` (`Sub/T18_2_4_2.lean`) is applied to the eight unconditional leaves
`PartIII-a:T18/2/4/2/1 ... /8`, each in its own file under `LerayProjectSlices/`.
Source of record: `the November 2 reference manuscript`, lines 3442-3465.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem lerayProjectSlices : UnforcedLeray.Short.IIIa.LerayProjectSlices :=
  lerayProjectSlices_of jointRepVecC lerayClassCont lerayClassEnergy p0DivFreeC p0OrthC
    p0CommWeakC gaussianSliceMemLp smoothSliceWeak

end UnforcedLeray.Short.IIIa

end
