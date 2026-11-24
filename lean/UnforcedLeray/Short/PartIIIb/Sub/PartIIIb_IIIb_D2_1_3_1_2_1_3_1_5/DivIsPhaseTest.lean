import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.CurlHelpers

/-!
# The divergence of a vector phase test is a scalar phase test (IIIb-D2 1.3.1.2.1.3.1.5)

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480. Helpers in `CurlHelpers.lean`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIIb.Concrete

theorem divIsPhaseTest : UnforcedLeray.Short.PartIIIb.Concrete.DivIsPhaseTest := by
  intro P A hA
  rw [divT_eq_sum]
  exact IsPhaseTest.sum _ fun k _ => (hA.dy k).clm_comp (coordL k)
