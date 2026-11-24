import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_9_Env
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_2

/-!
# `LatCellHp` (task `PartIII-b:C/asrc/ra/9/1/2/9/1`)

Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079.
The cell `L²` bound on the `h^p` words follows from the pointwise word bound `hpWordPointwise`
(task `/1/1`) and the envelope cell bound `latEnvCell` (task `/1/2`) through `latCellHp_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem latCellHp (as : ℝ) (χf : ℝ → ℝ) : LatCellHp as χf :=
  latCellHp_of as χf (hpWordPointwise as χf) latEnvCell

end UnforcedLeray.Short.PartIIIb.Concrete
