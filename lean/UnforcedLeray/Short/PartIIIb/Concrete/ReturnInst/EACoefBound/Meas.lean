import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.TermCont
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound.TermDom

/-!
# `PartIII-b:C/inst/10/4`: `EAcMeas` (a.e. strong measurability of `EAcoef`)

Source `the November 2 reference manuscript` 4978 (sums and derivatives converge
by Gaussian decay), 5063-5079.

`eaCMeas` is `eaCMeas_of_leaves` (Sub/PartIII-b_C_inst_10_4.lean) applied to the two
Gaussian-lattice leaves: the term continuity `eaTermContLeaf` (TermCont.lean) and the locally
uniform domination `eaTermDomLeaf` (TermDom.lean). The earlier reduction to a continuity leaf
is superseded and removed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem eaCMeas (as : ℝ) (χf : ℝ → ℝ) : EAcMeas as χf :=
  eaCMeas_of_leaves as χf eaTermContLeaf eaTermDomLeaf

end UnforcedLeray.Short.PartIIIb.Concrete
