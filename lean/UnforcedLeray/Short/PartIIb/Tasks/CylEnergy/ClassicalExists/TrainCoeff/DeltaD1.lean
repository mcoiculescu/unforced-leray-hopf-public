import UnforcedLeray.Short.PartIIb.Sub.T22_1_1
import UnforcedLeray.Short.PartIIb.Sub.TrainCloseCell

/-!
# Part II-b, task `PartII-b:T22/1/1/3`: the first-derivative leaf `TcDeltaD1`

Source: `TrainClose` at order `j = 1` (`StatementsMixed.lean`), transported from the centered
cell to the whole plane by `c`-periodicity (`TrainClose.norm_fderiv_sub_le`,
`Sub/TrainCloseCell.lean`), using `⟨x⟩⁸ = jb x ^ 4 ≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.IIb.CylPDE

theorem tcDeltaD1 : UnforcedLeray.Short.IIb.CylPDE.TcDeltaD1 := by
  intro Sg hSg ν c δ hν hc hδ tr hcl σ hσ x
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  exact UnforcedLeray.Short.IIb.TrainClose.norm_fderiv_sub_le hc0 hcl hσ.1 hσ.2 x

end UnforcedLeray.Short.IIb.CylPDE
