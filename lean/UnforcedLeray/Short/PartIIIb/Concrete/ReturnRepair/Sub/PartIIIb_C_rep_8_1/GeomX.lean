import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.TaylorWidth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.ZRegular
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Measurable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.StreamCutEq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.ZPrimRegular
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.GeomXOfPieces

/-!
# `PartIII-b:C/rep/8/1/1/1` (`geomX`): geometric comparison of `X`

Source `the November 2 reference manuscript`
lines 4178-4186, 5400-5427. Assembles `D.GeomX` from `geomX_of_pieces` and the proved leaves
`phasePrimitive`, `taylorWidth`, `zRegular`, `zPrimRegular`, `mnX_eq_wardStreamCut`, and
`xcmp_aemeasurable_cell`.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`PartIII-b:C/rep/8/1/1/1`** (`geomX`): geometric comparison for `X` along the sequence
(source lines 4178-4186, 5400-5427). -/
theorem geomX (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.GeomX := by
  have hν : ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1 := by
    filter_upwards [retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos
      D.coeff_ne] with n hn using hn.1
  have hM : D.XcmpCellMeas := by
    filter_upwards [xcmp_aemeasurable_cell D hst] with n hn z hz T s _ η using hn z hz T s η
  exact geomX_of_pieces D hst.chiY hν (phasePrimitive D hst) (taylorWidth D hst)
    (zRegular D hst) (zPrimRegular D hst) mnX_eq_wardStreamCut hM

end UnforcedLeray.Short.PartIIIb.Concrete
