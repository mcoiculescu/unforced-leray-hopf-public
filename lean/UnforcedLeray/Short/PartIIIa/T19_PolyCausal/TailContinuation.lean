import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_3
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.AdvectionEnergy
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.TailEnergyBound
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.GlobalExistence
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.TailContinuation.CoreUniqueness

/-!
# Part III-a, task `PartIII-a:T19/3`: tail energy continuation across `s = H` to `(0, ∞)`

Source of record: `the November 2 reference manuscript` (SP), lines 3517-3545
(Steps P5-P6 of `prop:short-polynomial-causal`).

Assembles `tailEnergyContinuation : UnforcedLeray.Short.IIIa.TailEnergyContinuation` from the four
leaf modules `AdvectionEnergy`, `TailEnergyBound`, `GlobalExistence`, and `CoreUniqueness`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem tailEnergyContinuation : UnforcedLeray.Short.IIIa.TailEnergyContinuation :=
  tailEnergyContinuation_of
    trainAdvectionEnergyIdentity
    trainTailEnergyFromAdvection
    trainCausalExistence
    coreCausalHomogeneousZero

end UnforcedLeray.Short.IIIa
