import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D5_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_kflat_1_2_3.Long

/-!
# `PartIII-b:C/asrc/kflat/1/2/3`: `trainFlowKinetic`

Assembles `trainFlowKinetic` from `trainFlowKinetic_of`, `tfkShortAll`, and `tfkLongAll`.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem trainFlowKinetic (m : ℝ) [Fact (1 < m)] : TrainFlowKinetic m :=
  trainFlowKinetic_of m (tfkShortAll m) (tfkLongAll m)

end UnforcedLeray.Short.PartIIIb.Concrete
