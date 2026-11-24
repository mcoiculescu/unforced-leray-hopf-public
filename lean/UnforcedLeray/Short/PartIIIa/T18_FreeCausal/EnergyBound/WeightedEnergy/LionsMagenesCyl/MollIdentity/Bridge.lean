import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_3_2.Bridge_Sub
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity.Bridge.RepExists
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity.Bridge.RepIdentity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity.Bridge.RepPair

/-!
# `PartIII-a:T18/3/1/3/2/1` (`lmEnergyBridge`)

Assembles `LMEnergyBridge` from the three leaf statements `lmRepExists`, `lmRepIdentity`,
`lmRepPair` via `lmEnergyBridge_of` (`Sub/T18_3_1_3_2/Bridge_Sub.lean`).
Source: `the November 2 reference manuscript` 3541-3552.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem lmEnergyBridge : UnforcedLeray.Short.IIIa.LMEnergyBridge :=
  lmEnergyBridge_of lmRepExists lmRepIdentity lmRepPair

end UnforcedLeray.Short.IIIa
