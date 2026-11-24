import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.D
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.E

/-!
# `SepKerPDE` (`sep:kernel`, source 3603-3610, 3800-3807)

Assembles the two analytic inputs `gkerHasDerivH` (file `L6_2_KerPDE/D.lean`) and
`lkerKdSplit` (file `L6_2_KerPDE/E.lean`) into `SepKerPDE` via `sepKerPDE_of`
(`Sub/PartIII-b_C_rep_2_6_2.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepKerPDE : SepKerPDE :=
  sepKerPDE_of gkerHasDerivH lkerKdSplit

end UnforcedLeray.Short.PartIIIb.Concrete
