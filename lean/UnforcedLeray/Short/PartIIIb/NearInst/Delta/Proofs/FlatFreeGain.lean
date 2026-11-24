import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.AEInvariant
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.AgeMeasureAC
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.SourceMeasRep
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.VelNormBridge

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- The flat free response in the gain norm (target `PartIII-b:C/near/delta/7`), from the four
lemma theorems and the free solver `hU`. -/
theorem flatFreeGainBound_of (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) :
    FlatFreeGainBound :=
  flatFreeGainBound_core hU freeSolAEInvariant sourceMeasRep velNormBridge ageMeasureAC

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
