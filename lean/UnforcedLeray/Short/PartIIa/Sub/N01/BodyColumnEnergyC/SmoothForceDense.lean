import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamIsSmoothForce
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamSolenoidal
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense

/-!


Source of record: `the November 2 reference manuscript`, lines 1684-1689.

Assembly: `smoothForceDense_of` (in `Sub/PartII-a_N01_9_1_1.lean`) applied to the three step lemmas
`streamIsSmoothForce` (`/1`), `streamSolenoidal` (`/2`) and `streamDense` (`/3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem smoothForceDense : UnforcedLeray.Short.PartIIa.N01.SmoothForceDense :=
  smoothForceDense_of streamIsSmoothForce streamSolenoidal streamDense

end UnforcedLeray.Short.PartIIa.N01
