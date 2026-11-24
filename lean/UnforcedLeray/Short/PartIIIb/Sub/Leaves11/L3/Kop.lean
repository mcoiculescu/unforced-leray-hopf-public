import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_3_3
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.Core.Unfold
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.Core.Weight
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.Core.GaussInt
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.Core.TsumCS

/-!
# `PartIII-b:C/inst/11/3/3`: `HAcPieceKop` from the four elementary lattice lemmas

Source `the November 2 reference manuscript`:
lattice sums 4973-4975, the operator `𝒦 = η∂_η + 2s∂_s` 4979-4980, size 5009-5016, 5063-5079.

Assembles `hAcPieceKop_of_lemmas` (instance file `PartIII-b_C_inst_11_3_3`) with the four
lemmas `latUnfold`, `latWeight`, `gaussInt8`, `tsumCS` proved in `Sub/Leaves11/L3/Core/`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hAcPieceKop : HAcPieceKop :=
  hAcPieceKop_of_lemmas latUnfold latWeight gaussInt8 tsumCS

end UnforcedLeray.Short.PartIIIb.Concrete
