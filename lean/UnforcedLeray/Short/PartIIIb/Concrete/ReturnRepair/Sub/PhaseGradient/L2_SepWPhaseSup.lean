import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L1_SepDomPhaseSup
import UnforcedLeray.Short.PartIIIa.Tasks16.Dominated
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `PartIII-b:C/rep/2/2` (task L2): `SepWPhaseSup`

Source `the November 2 reference manuscript` 3603-3647 (`sep:kernel`, `sep:resolvent`,
`sep:young`) and 5212-5221 (the phase supremum of the separated resolvent).  The pointwise
domination `IIIa.SepWDominated` (`PartIII-a:T16/1`), the kernel bounds `IIIa.sepKernelBounds` and
the scalar phase estimate `sepDomPhaseSup` (task `PartIII-b:C/rep/2/1`) are proved; the assembly
is `sepWPhaseSup_of` in `Defs.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(S1) The separated resolvent in phase supremum** (source 3622-3647, 5212-5221): from the
pointwise domination, the kernel bounds and the scalar phase estimate. -/
theorem sepWPhaseSup : SepWPhaseSup :=
  sepWPhaseSup_of UnforcedLeray.Short.IIIa.sepWDominated UnforcedLeray.Short.IIIa.sepKernelBounds
    sepDomPhaseSup

end UnforcedLeray.Short.PartIIIb.Concrete

end
