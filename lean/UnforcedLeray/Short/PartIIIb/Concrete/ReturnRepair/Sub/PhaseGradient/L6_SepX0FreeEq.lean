import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_1_HRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb

/-!
# `sepX0FreeEq`: the free equation of `X₀` (`ward:shifted-resolvent`, source 4199-4200)

Assembles the three analytic inputs `sepWHRep` (`Sub/L6_1_HRep.lean`), `sepKerPDE`
(`Sub/L6_2_KerPDE.lean`) and `sepX0Comb` (`Sub/L6_3_Comb.lean`) into `SepX0FreeEq` via
`sepX0FreeEq_of` (`Sub/PartIII-b_C_rep_2_6.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepX0FreeEq : SepX0FreeEq :=
  sepX0FreeEq_of sepWHRep sepKerPDE sepX0Comb

end UnforcedLeray.Short.PartIIIb.Concrete
