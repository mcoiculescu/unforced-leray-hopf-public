import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1_1
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.FwdSpatialTaylorReal
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.FwdXkMeas
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.FwdSliceDecomp

/-!
# Part II-a, task `PartII-a:F09/1/3/1/1`: `sliceFwdSpatialTaylor`

Source `the November 2 reference manuscript`, lines 1403-1413, 1426-1428.
Assembles the three step lemmas `fwdSpatialTaylorReal` (task 1/1/1), `fwdXkMeas` (task 1/1/2)
and `fwdSliceDecomp` (task 1/1/3) through `sliceFwdSpatialTaylor_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Forward slice Taylor bound** (task `PartII-a:F09/1/3/1/1`, lines 1403-1413, 1426-1428). -/
theorem sliceFwdSpatialTaylor (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (P : ℝ) [Fact (0 < P)]
    (ν : ℝ) (hν : 0 < ν) (Φ : ℝ × Space → CVec3) (hΦ : IsPhaseTest P Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t s : ℝ, 0 < s → s ≤ 1 →
      ‖B0421.freeC hp ν s (sliceMap (hΦ.isSliceTest p).2 t) - sliceMap (hΦ.isSliceTest p).2 t +
        (s : ℂ) • (sliceMap ((isPhaseTest_L0' hΦ ν).isSliceTest p).2 t -
          sliceMap (hΦ.dτ.isSliceTest p).2 t)‖ ≤ C * s ^ 2 :=
  sliceFwdSpatialTaylor_of fwdSpatialTaylorReal fwdXkMeas fwdSliceDecomp p hp P ν hν Φ hΦ

end UnforcedLeray.Short.PartIIa
