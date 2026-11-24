import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont.WeightedCS
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont.AdjMDominated
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont.AdjMPointwiseCont
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.RhsCont.AdjMMeasurable

/-!
# `PartIII-a:T21/2/7/2/1/1/3`: continuity of the tested right-hand side (`adjTestedRhsCont`)

Source: `the November 2 reference manuscript` lines 3052-3061.
The four leaves are proved in `RhsCont/`; this file assembles them with `adjTestedRhsCont_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem adjTestedRhsCont (m : ℝ) : AdjTestedRhsCont m :=
  adjTestedRhsCont_of m weightedCS (adjMDominated m) adjMPointwiseCont adjMMeasurable

end UnforcedLeray.Short.IIIa
