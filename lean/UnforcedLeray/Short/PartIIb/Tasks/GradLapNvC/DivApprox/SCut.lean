import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivApprox.SCut.Weak
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivApprox.SCut.InHr
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivApprox.SCut.Conv

/-!
# Part II-b, task `PartII-b:T09/2/1` (`DivSCutApproxW`): the corrected `s`-cutoff stage

Source of record: `the November 2 reference manuscript`, lines 1912-1918.
Assembly of `divSCutApproxW_of` (`Sub/PartII-b_T09_2_1.lean`) from the leaves
`T09/2/1/1` (`divSCutWeak_proof`), `T09/2/1/2` (`divSCutInHr_proof`),
`T09/2/1/3` (`divSCutConv_proof`).  (The old strong-norm target `DivSCutApprox` is false:
`Sub/T09_2_1/Refute.lean`.)
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:T09/2/1`.** -/
theorem divSCutApproxW_proof : UnforcedLeray.Short.IIb.DivSCutApproxW :=
  divSCutApproxW_of divSCutWeak_proof divSCutInHr_proof divSCutConv_proof

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.divSCutApproxW_proof
