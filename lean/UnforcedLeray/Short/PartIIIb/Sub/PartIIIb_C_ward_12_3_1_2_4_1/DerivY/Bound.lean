import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1_2_a
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingResidualProved

/-!
# `ringResidualDerivBound_thm` (`PartIII-b:C/ward/12/3/1/2/4/1/2/a`)

Source of record: `the November 2 reference manuscript`
lines 1206-1222, 1305-1322, 2542-2551.

Combines `ringResidualDerivBound_of` (`PartIII-b_C_ward_12_3_1_2_4_1_2_a`) with
`ringResidualBound_proved` (`PartII-b:R1/1`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb

/-- Spatial derivative bound for the ring residual (`RingResidualDerivBound`), obtained from
`ringResidualDerivBound_of` and `ringResidualBound_proved`. -/
theorem ringResidualDerivBound_thm : UnforcedLeray.Short.PartIIIb.Concrete.RingResidualDerivBound :=
  Concrete.ringResidualDerivBound_of UnforcedLeray.Short.IIb.ringResidualBound_proved

namespace Concrete

export UnforcedLeray.Short.PartIIIb (ringResidualDerivBound_thm)

end Concrete

end UnforcedLeray.Short.PartIIIb
