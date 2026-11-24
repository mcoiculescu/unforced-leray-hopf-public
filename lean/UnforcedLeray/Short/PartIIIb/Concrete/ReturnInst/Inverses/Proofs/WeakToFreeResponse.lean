import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.LerayPairSol
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Proofs.YrSub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Proofs.WeakDmuSubY
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Proofs.FreeResponseAECongr

/-!
# The weak-to-graph upgrade of free responses (source 1351-1362, 1580-1583)

Assembly of `WeakToFreeResponse`: the proof is `weakToFreeResponse_of` (Level.lean, source
1351-1362 and 1580-1583) applied to the Leray pair solution `lerayPairSol`, the homogeneous
uniqueness `fwuHomog`, and the three leaves `yrSub`, `weakDmuSubY`, `freeResponseAECongr`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The weak free solution is the free response** (source 1351-1362, 1580-1583): a weakly
solenoidal distributional solution `w ∈ Y_2` of `D_μ w = ℙf` with `f ∈ Y_2` is the free response
of `f`, by the graph solution, subtraction of two solutions and a.e. congruence. -/
theorem weakToFreeResponse : WeakToFreeResponse :=
  weakToFreeResponse_of UnforcedLeray.Short.IIb.lerayPairSol fwuHomog yrSub weakDmuSubY
    freeResponseAECongr

end UnforcedLeray.Short.PartIIIb.Concrete
