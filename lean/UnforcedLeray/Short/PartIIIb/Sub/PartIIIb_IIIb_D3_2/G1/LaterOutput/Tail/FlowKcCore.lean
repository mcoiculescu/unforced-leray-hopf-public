import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoRemOrg

/-!
# `PartIII-b:IIIb-D3/2/G1/5/2/2`: Unforced flat evolution `kcLp` core window bound

Source of record: `the November 2 reference manuscript`
lines 4442-4445, 3272-3277.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

/-- Unforced linearised flow `K_c` velocity bound on the core tail `2/ν ≤ s ≤ IIIa.coreEnd ν b`
from `IIIa.FullClockLongForward` (source lines 4442-4445, 3272-3277). -/
theorem unforcedFlowKcCoreBound_of (D : SeqData)
    (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward) :
    G1.LaterOutput.UnforcedFlowKcCoreBound D :=
  G3.unforcedFlowKcCoreBound_of_longForward D hLF

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

end
