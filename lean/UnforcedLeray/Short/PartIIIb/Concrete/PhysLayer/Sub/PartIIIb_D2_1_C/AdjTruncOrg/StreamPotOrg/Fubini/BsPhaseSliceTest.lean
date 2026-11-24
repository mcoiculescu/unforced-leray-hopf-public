import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Lib.PhaseSpace.Test
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Phase tests have smooth compactly supported slices

Source `the November 2 reference manuscript` lines 1351-1362. A phase test
`Θ` (smooth, periodic in the phase, vanishing for large `‖y‖`) has, at each fixed phase `t`,
a slice `y ↦ Θ(t, y)` which is smooth and compactly supported.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace
open scoped ContDiff

/-- Corrected slice statement with `C^∞` regularity (`∞`). The target `BSPhaseSliceTest` writes
`ContDiff ℝ ⊤`, which in `WithTop ℕ∞` is analytic (`ω`), not smooth, so it is not implied by
`IsPhaseTest`; this lemma is the provable version. -/
theorem bsPhaseSliceTest_inf :
    ∀ (P : ℝ) (Θ : ℝ × Space → CVec3), IsPhaseTest P Θ → ∀ t : ℝ,
      ContDiff ℝ ∞ (fun y : Space => Θ (t, y)) ∧ HasCompactSupport (fun y : Space => Θ (t, y)) := by
  intro P Θ hΘ t
  refine ⟨?_, hΘ.hasCompactSupport_slice t⟩
  exact hΘ.smooth.comp (contDiff_const.prodMk contDiff_id)

/-- `BSPhaseSliceTest`, now stated with `C^∞` regularity. -/
theorem bsPhaseSliceTest : BSPhaseSliceTest := bsPhaseSliceTest_inf

end UnforcedLeray.Short.PartIIIb.Concrete
