import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoRemOrg

/-!
# `PartIII-b:IIIb-D3/2/G1/5/2/3`: Unforced flat evolution `kcLp` post-core impulse bound

Source of record: `the November 2 reference manuscript`
lines 4442-4445, 3277-3284.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

/-- Unforced linearised flow `K_c` velocity bound past the long clock `s ≥ IIIa.coreEnd ν b`
from `IIIa.FullClockLongForward` and `IIIa.CTKineticImpulse` (source lines 4442-4445, 3277-3284). -/
theorem unforcedFlowKcImpulseBound_of (D : SeqData)
    (hLF : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    G1.LaterOutput.UnforcedFlowKcImpulseBound D :=
  G3.unforcedFlowKcImpulseBound_of_longForward D hLF hKI

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G1.LaterOutput

end
