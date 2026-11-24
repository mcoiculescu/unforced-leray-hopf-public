import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYFormula
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanYFormula
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.YTermsDiff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYA
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.Final

/-!
# `PartIII-b:C/rep/8/1/1/2` (`geomY`): geometric comparison of `Y`

Source `the November 2 reference manuscript`
lines 5415-5432, 4171-4215, 5374-5387. Assembles `D.GeomY` from `SeqData.geomY_of` and the proved
pieces `actYFormula`, `meanYFormulaSeq`, `yTermsDiff`, `geomYA`, and `geomYB`.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`PartIII-b:C/rep/8/1/1/2`** (`geomY`): geometric comparison for `Y` along the sequence
(source lines 5415-5432). -/
theorem geomY (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.GeomY := by
  have hLH : D.LHypSeq :=
    D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt hst.chiY
  have hν : ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1 := by
    filter_upwards [retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos
      D.coeff_ne] with n hn using hn.1
  exact D.geomY_of hLH hν (actYFormula D hst) (meanYFormulaSeq D hst)
    (Sub8_1_1_2_3.yTermsDiff D hst) (geomYA D hst) (geomYB D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
