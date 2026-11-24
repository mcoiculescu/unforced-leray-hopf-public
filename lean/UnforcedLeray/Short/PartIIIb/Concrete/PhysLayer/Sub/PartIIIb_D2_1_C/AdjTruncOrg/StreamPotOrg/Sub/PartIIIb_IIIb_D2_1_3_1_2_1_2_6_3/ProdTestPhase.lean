import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6_3.Defs

/-!
# The product test `s(t) g(y) eᵢ` is a phase test

Source `the November 2 reference manuscript` lines 1351-1362 (weak `y`-gradient of
the stream potential) and 1334-1337 (`Y_r`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem prodTestPhase : ProdTestPhase := by
  intro P s g i hs hper hg
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness
    have h1 : ContDiff ℝ ∞ (fun x : ℝ × Space => s x.1 * g x.2) :=
      (hs.comp contDiff_fst).mul (hg.1.comp contDiff_snd)
    exact h1.smul contDiff_const
  · -- periodicity in the phase
    intro τ y
    simp only [prodTest, hper]
  · -- bounded support in the spatial variable
    obtain ⟨R, hR⟩ := hg.2.isCompact.isBounded.subset_closedBall (0 : Space)
    refine ⟨R, fun τ y hy => ?_⟩
    have hgy : g y = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hyt
      have h1 := hR hyt
      rw [mem_closedBall_zero_iff] at h1
      linarith
    simp [prodTest, hgy]

end UnforcedLeray.Short.PartIIIb.Concrete
