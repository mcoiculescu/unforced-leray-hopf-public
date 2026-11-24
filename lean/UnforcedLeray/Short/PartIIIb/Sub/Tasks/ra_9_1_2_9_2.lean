import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_9_Env
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_1_2

/-!
# `LatCellPsi` (task `PartIII-b:C/asrc/ra/9/1/2/9/2`)

Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079.
The cell `L²` bound on the `ψ^p` words follows from the pointwise word bound `psiWordPointwise`
(task `/2/1`) and the envelope cell bound `latEnvCell` (task `/1/2`) through `latCellPsi_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem latCellPsi (as : ℝ) (χf : ℝ → ℝ) : LatCellPsi as χf :=
  latCellPsi_of as χf (psiWordPointwise as χf) latEnvCell

end UnforcedLeray.Short.PartIIIb.Concrete
