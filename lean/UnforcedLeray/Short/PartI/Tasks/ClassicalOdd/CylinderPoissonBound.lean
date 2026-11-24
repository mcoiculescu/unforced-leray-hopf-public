import UnforcedLeray.Short.PartI.Sub.T02_3_8
import UnforcedLeray.Short.PartI.Sub.T02_3_8.Mean
import UnforcedLeray.Short.PartI.Sub.T02_3_8.Osc
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.SourceBound
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.HmeanC2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.HmeanLap
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.MeanSource
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.AffineZero
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.ModeC2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.ModeLaplace
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.QModeEstimates
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.MaxPrinciple
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.FourierPointwise
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.CylinderPoissonBound.QAvgReal

/-!
# Part I, task `PartI:T02/3/8`: the unconditional cylinder pressure bound `CylinderPoissonBound`

Source of record: `the November 2 reference manuscript`, lines 276-288 (the bounded
periodic pressure of Gallay-Slijepcevic, line 277; the Poisson equation for the pressure, line 447).

Target: `CylinderPoissonBound` (`Short/PartI/Sub/T02_3.lean`, line 168): for `c > 0` and `B` there is
`M` such that every smooth `c`-periodic divergence-free `u` with `‖D^k u‖ ≤ B` (`k ≤ 4`) and every
`C²` `c`-periodic `q` with `Δq = -∂_i u_j ∂_j u_i`, both tending to `0` as `|η| → ∞`, satisfy
`|q| ≤ M`.

This file is the assembly step.  The conditional theorem `cylinderPoissonBound_of`
(`Sub/T02_3_8.lean`) reduces the target to three statements (the source bound, the mean-part bound
and the oscillation bound).  `cylPoisMeanPartBound_of` (`Sub/T02_3_8/Mean.lean`) and
`cylPoisOscPartBound_of` (`Sub/T02_3_8/Osc.lean`) reduce the latter two to eleven leaves, each
proved in its own file under `Tasks/ClassicalOdd/CylinderPoissonBound/`.  This file adds no
placeholder or unchecked assumption of its own.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

/-- **Unconditional bounded pressure on the cylinder** (source lines 276-288): the target
`CylinderPoissonBound` of `Sub/T02_3.lean`, proved from the eleven leaves. -/
theorem cylinderPoissonBound : CylinderPoissonBound :=
  cylinderPoissonBound_of cylPoisSourceBound
    (cylPoisMeanPartBound_of cylPoisHmeanC2 cylPoisHmeanLap cylPoisMeanSource cylPoisAffineZero)
    (cylPoisOscPartBound_of cylPoisModeC2 cylPoisModeLaplace cylPoisQModeEstimates cylPoisMaxPrinciple
      cylPoisFourierPointwise cylPoisQAvgReal)

end UnforcedLeray.Short.PartI
