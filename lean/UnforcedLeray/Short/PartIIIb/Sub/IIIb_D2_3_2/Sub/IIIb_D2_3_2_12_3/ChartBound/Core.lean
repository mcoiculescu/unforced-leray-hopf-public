import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.StressPointwise
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.StressMeasurable
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.StressBallLintegral

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1/4`: assembly of `StressCSRegion`

Combines the three leaf proofs `stressPointwise_proof`, `stressMeasurable_proof`,
`stressBallLintegral_proof` through `stressCSRegion_of`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem stressCSRegion_proved : UnforcedLeray.Short.PartIIIb.Concrete.StressCSRegion :=
  stressCSRegion_of stressPointwise_proof stressMeasurable_proof stressBallLintegral_proof

end UnforcedLeray.Short.PartIIIb.Concrete
