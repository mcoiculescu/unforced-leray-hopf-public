import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.Meas.TermContOn
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FACoefBound.Meas.TermLocBound

/-!
# `PartIII-b:C/inst/9/4`: `FAcMeas`

Source `the November 2 reference manuscript` 5009-5016, proof 5063-5079.
The two Gaussian lattice leaves are `faTermContOn` (`Meas/TermContOn.lean`, leaf 2) and
`faTermLocBound` (`Meas/TermLocBound.lean`, leaf 3); leaf 1 is `bmatContOn` in
`Sub/PartIII-b_C_inst_9_4.lean`.  The final theorem is `fAcMeas_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fAcMeas (as : ℝ) (χf : ℝ → ℝ) : FAcMeas as χf :=
  fAcMeas_of_leaves as χf (bmatContOn χf) faTermContOn faTermLocBound

end UnforcedLeray.Short.PartIIIb.Concrete
