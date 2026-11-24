import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.TrainFlowKinetic

/-!
# `PartIII-b:C/asrc/kflat/1/2`: `frakTInt`

Assembles `frakTInt` from `frakTIntProp_of`, `frakTMeas`, `duhIntegrable`, `kcMerLinear`,
`xiDLate`, `trainOldStressBound_of`, `trainEnergyUnif_of`, `trainL2Decay_unconditional`,
`symOuterSlice`, and `trainFlowKinetic`.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem frakTInt (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : FrakTIntProp as χf m :=
  frakTIntProp_of as χf m (frakTMeas as χf m) (duhIntegrable as χf m) (kcMerLinear m)
    (xiDLate m)
    (trainOldStressBound_of m (trainEnergyUnif_of trainL2Decay_unconditional)
      (symOuterSlice m) (trainFlowKinetic m))

end UnforcedLeray.Short.PartIIIb.Concrete
