import UnforcedLeray.Lib.LerayC.Phase
import UnforcedLeray.Units.B0412

/-!
# The slice-wise Leray projection preserves phase tests

A projected compact phase test is generally not compact in space. This file proves the weaker
property needed to give its canonical slices a non-junk `Y_q` representative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412
open UnforcedLeray.RieszLp

/-- Pointwise representative of the slice-wise complex Leray projection. -/
def lerayProjectedPhaseTest {P : ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hr1 : 1 < r) (hrtop : r ≠ ⊤) {Φ : ℝ × Space → CVec3}
    (hΦ : IsSliceTest P r Φ) : ℝ × Space → CVec3 := fun x =>
  (lerayC r hr1 hrtop (sliceMap hΦ.2 x.1)) x.2

/-- Projecting each spatial slice by the bounded Leray operator preserves periodicity and
continuity in `L^r`, so the projected field is a genuine slice test. -/
theorem isSliceTest_lerayProjectedPhaseTest {P : ℝ} {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hr1 : 1 < r) (hrtop : r ≠ ⊤) {Φ : ℝ × Space → CVec3}
    (hΦ : IsSliceTest P r Φ) :
    IsSliceTest P r (lerayProjectedPhaseTest hr1 hrtop hΦ) := by
  refine ⟨?_, ?_⟩
  · intro τ y
    change (lerayC r hr1 hrtop (sliceMap hΦ.2 (τ + P))) y =
      (lerayC r hr1 hrtop (sliceMap hΦ.2 τ)) y
    rw [sliceMap_periodic hΦ τ]
  · let path : ℝ → Lp CVec3 r (volume : Measure Space) :=
      fun τ => lerayC r hr1 hrtop (sliceMap hΦ.2 τ)
    let hm : ∀ τ, MemLp (fun y => lerayProjectedPhaseTest hr1 hrtop hΦ (τ, y)) r volume :=
      fun τ => Lp.memLp (path τ)
    refine ⟨hm, ?_⟩
    have hcont : Continuous path := (lerayC r hr1 hrtop).continuous.comp hΦ.2.continuous
    have hpath : (fun τ => MemLp.toLp _ (hm τ)) = path := by
      funext τ
      apply Lp.ext
      exact (hm τ).coeFn_toLp
    change Continuous (fun τ => MemLp.toLp _ (hm τ))
    rw [hpath]
    exact hcont

#print axioms isSliceTest_lerayProjectedPhaseTest

end UnforcedLeray.Cons.C03.Concrete
