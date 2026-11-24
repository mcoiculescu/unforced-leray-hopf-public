import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1.l2SqMeas
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1.l2SqDiff
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2_1.l2SqWeak
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# `l2Sq_hasDerivAt`: derivative of the cell energy (source 341-348)

The unconditional statement, obtained from `l2Sq_hasDerivAt_of` by supplying the three
analytic facts `l2SqMeas`, `l2SqDiff`, `l2SqWeak`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.Short.PartI.L2SqDeriv

theorem l2Sq_hasDerivAt {μ : MeasureTheory.Measure Plane} (F : ℝ → Plane → ℝ) (s ε K : ℝ) (hε : 0 < ε) (hC : ∀ z, ContDiff ℝ 1 (fun t => F t z)) (hF : MeasureTheory.MemLp (F s) 2 μ) (hD : ∀ r, |r - s| < ε → MeasureTheory.MemLp (fun z => deriv (fun t => F t z) r) 2 μ ∧ ∫ z, (deriv (fun t => F t z) r) ^ 2 ∂μ ≤ K) : (∀ᶠ r in nhds s, MeasureTheory.MemLp (F r) 2 μ) ∧ HasDerivAt (fun r => ∫ z, (F r z) ^ 2 ∂μ) (2 * ∫ z, F s z * deriv (fun t => F t z) s ∂μ) s :=
  l2Sq_hasDerivAt_of l2SqMeas l2SqDiff l2SqWeak F s ε K hε hC hF hD

end UnforcedLeray.Short.PartI.L2SqDeriv
