import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F7
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation

namespace UnforcedLeray.Short.IIb

/-!
# Part II-b — Task F7: Tail Source and Global Energy (`short-bg:tail-source`, `short-bg:global-energy`)

Assembles `TailSourceAndGlobalEnergy` from `tailSourceAndGlobalEnergy_of_leaves`,
`tailSourceSliceBound_proof`, and `globalEnergyContinuation_proof`.
-/

theorem tailSourceAndGlobalEnergy_of
    (hEB : UnforcedLeray.Short.IIb.EarlyBound)
    (hBS : UnforcedLeray.Short.IIb.BodySourceBound) :
    UnforcedLeray.Short.IIb.TailSourceAndGlobalEnergy :=
  tailSourceAndGlobalEnergy_of_leaves
    tailSourceSliceBound_proof globalEnergyContinuation_proof hEB hBS

end UnforcedLeray.Short.IIb
