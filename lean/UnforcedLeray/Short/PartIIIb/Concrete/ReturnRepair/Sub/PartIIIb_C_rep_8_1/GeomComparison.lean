import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.Final

/-!
# `PartIII-b:C/rep/8/1/1` (`geomComparison`): geometric comparison along the sequence

Source `the November 2 reference manuscript`
lines 4171-4215, 5374-5432. Combines `geomX` and `geomY` via `SeqData.geomComparison_of`.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`PartIII-b:C/rep/8/1/1`** (`geomComparison`): geometric comparison along the sequence
(source lines 4171-4215, 5374-5432). -/
theorem geomComparison (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.GeomComparison := by
  have hν : ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1 := by
    filter_upwards [retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos
      D.coeff_ne] with n hn using hn.1
  exact D.geomComparison_of hν (geomX D hst) (geomY D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
