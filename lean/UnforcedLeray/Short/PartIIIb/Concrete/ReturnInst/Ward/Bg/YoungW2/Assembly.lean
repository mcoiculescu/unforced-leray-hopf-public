import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.RingLiftYoung
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.RawProfileSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.InletProfileJetsAt

/-!
# `BgYoungW2` from the two open leaves (source 1206-1222, 2347-2387, 2525-2562, 5461-5464)

Source of record: `the November 2 reference manuscript` (73 pages).

Task `PartIII-b:C/ward/12/org`.  With the proved pieces `bgRingLiftYoung`, `bgRawProfileSmooth`
and `bgInletProfileJetsAt`, `BgYoungW2` follows from the weighted young jets of the raw profile
(`BgRawProfileYoungJets`, source 1206-1222, 5461-5464) and the young `W^{2,∞}` bound of the repair
(`BgCorrYoungJets`, source 2525-2562, 2607-2609).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`BgYoungW2`** from the weighted young jets of the raw profile and the repair bound. -/
theorem bgYoungW2_of_corr (hRP : BgRawProfileYoungJets) (hCo : BgCorrYoungJets) : BgYoungW2 :=
  bgYoungW2_of (bgRawYoungJets_of bgRawProfileSmooth hRP bgRingLiftYoung)
    (bgInletColumnJets_of bgInletProfileJetsAt) hCo

#print axioms bgYoungW2_of_corr

end UnforcedLeray.Short.PartIIIb.Concrete
