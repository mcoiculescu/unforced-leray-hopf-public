import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_9
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2

/-!
# `PartIII-b:C/asrc/ra/9/1/2/9` : `LatCellBound` from the `h^p` and `ψ^p` cell bounds

Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079,
5034-5039, 4979-4980. The `h^p` half is `latCellHp` (task `/1`), the `ψ^p` half is `latCellPsi`
(task `/2`); they are merged by `latCellBound_of` (constants by `max`, the cutoff `ν₀` by `min`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem latCellBound (as : ℝ) (χf : ℝ → ℝ) : LatCellBound as χf :=
  latCellBound_of as χf (latCellHp as χf) (latCellPsi as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
