import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.Hp
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.Psi
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.Kop
import UnforcedLeray.Short.PartIIIb.Sub.Leaves11.L3.KopEq
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11_3

/-!
# `PartIII-b:C/inst/11/3`: `HAcCellBound` from the four Gaussian-lattice leaves

Source `the November 2 reference manuscript`:
`ĥ_A` 4979-4980, lattice sums 4973-4975, size 5009-5016, 5063-5079.

Assembles `hAcCellBound_of` (in `Sub/PartIII-b_C_inst_11_3.lean`) with the leaves
`hAcPieceHp` (`Leaves11/L3/Hp.lean`), `hAcPiecePsi` (`Leaves11/L3/Psi.lean`),
`hAcPieceKop` (`Leaves11/L3/Kop.lean`) and `hAcKopEq` (`Leaves11/L3/KopEq.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hAcCellBound : HAcCellBound :=
  hAcCellBound_of hAcPieceHp hAcPiecePsi hAcPieceKop hAcKopEq

end UnforcedLeray.Short.PartIIIb.Concrete
