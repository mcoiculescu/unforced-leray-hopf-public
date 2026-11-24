import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.CurlHelpers

/-!
# `curl A` is a solenoidal phase test (IIIb-D2 1.3.1.2.1.3.1.5)

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480. Helpers in `CurlHelpers.lean`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIIb.Concrete

theorem curlIsSolTest : UnforcedLeray.Short.PartIIIb.Concrete.CurlIsSolTest := by
  intro P A hA
  refine And.intro ?_ ?_
  · rw [curlT_eq_sum]
    exact IsPhaseTest.sum _ fun k _ => (hA.dy k).clm_comp (crossCL _)
  · intro x
    have r10 : UnforcedLeray.PhaseSpace.dy 1 (UnforcedLeray.PhaseSpace.dy 0 A) = UnforcedLeray.PhaseSpace.dy 0 (UnforcedLeray.PhaseSpace.dy 1 A) :=
      UnforcedLeray.PhaseSpace.dy_dy_comm hA.smooth 1 0
    have r20 : UnforcedLeray.PhaseSpace.dy 2 (UnforcedLeray.PhaseSpace.dy 0 A) = UnforcedLeray.PhaseSpace.dy 0 (UnforcedLeray.PhaseSpace.dy 2 A) :=
      UnforcedLeray.PhaseSpace.dy_dy_comm hA.smooth 2 0
    have r21 : UnforcedLeray.PhaseSpace.dy 2 (UnforcedLeray.PhaseSpace.dy 1 A) = UnforcedLeray.PhaseSpace.dy 1 (UnforcedLeray.PhaseSpace.dy 2 A) :=
      UnforcedLeray.PhaseSpace.dy_dy_comm hA.smooth 2 1
    simp only [dy_curlT A hA.smooth]
    simp [Fin.sum_univ_three, crossC, r10, r20, r21]
    ring
