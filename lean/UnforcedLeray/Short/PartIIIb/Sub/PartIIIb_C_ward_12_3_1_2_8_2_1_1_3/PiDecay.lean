import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_3_1.FarDeriv

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/3/1/3/1`: `PiDecay` from the far-field derivative bounds

Source `the November 2 reference manuscript`
lines 1393-1400, 1409-1412.  The far-field derivative bounds `PiFarDeriv` (proved in
`FarDeriv.lean` as `piFarDeriv`) reduce to `PiDecay` by `PiDecayAssembly.piDecay_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `PiDecay` holds: the Newton potential `projPot Ψ` has order-zero and derivative decay. -/
theorem piDecay : UnforcedLeray.Short.PartIIIb.Concrete.PiDecay :=
  UnforcedLeray.Short.PartIIIb.Concrete.PiDecayAssembly.piDecay_of
    UnforcedLeray.Short.PartIIIb.Concrete.PiDecayAssembly.piFarDeriv

end UnforcedLeray.Short.PartIIIb.Concrete
