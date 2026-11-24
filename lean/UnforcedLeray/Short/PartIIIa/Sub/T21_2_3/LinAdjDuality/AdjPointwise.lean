import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakPointwise

/-!
# `PartIII-a:T21/2/3/1/7` (`ladAdjPointwise`)

An adjoint flow is a jointly smooth weak solution, so `ladAdjPointwise_of_weak` applied to
`adjWeakPointwise m` gives `LadAdjPointwise m`. Source: SP 3052-3060.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

theorem ladAdjPointwise (m : ℝ) : LadAdjPointwise m :=
  ladAdjPointwise_of_weak m (adjWeakPointwise m)

end UnforcedLeray.Short.IIIa
