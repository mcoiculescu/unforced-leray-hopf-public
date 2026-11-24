import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiAprioriEta
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiAprioriQ
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiLimit

/-!
# `PartII-b:T13/1/5` assembly: `CylGradInterp`

Source: `the November 2 reference manuscript` lines 1932-1935.
Composes the four leaves through the proved reduction `cylGradInterp_of`
(Sub file `PartII-b_T13_1_5`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem cylGradInterp : UnforcedLeray.Short.IIb.CylGradInterp :=
  cylGradInterp_of cgiAprioriEta_proof cgiAprioriQ_proof cgiMollify_proof cgiLimit_proof

end UnforcedLeray.Short.IIb
