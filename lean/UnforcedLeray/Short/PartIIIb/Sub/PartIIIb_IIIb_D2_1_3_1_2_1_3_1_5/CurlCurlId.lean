import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.CurlHelpers

/-!
# `curl curl A = ∇ div A - Δ A` (IIIb-D2 1.3.1.2.1.3.1.5)

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480. Helpers in `CurlHelpers.lean`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace UnforcedLeray.Short.PartIIIb.Concrete

theorem curlCurlId : UnforcedLeray.Short.PartIIIb.Concrete.CurlCurlId := by
  intro A hA
  have r10 : UnforcedLeray.PhaseSpace.dy 1 (UnforcedLeray.PhaseSpace.dy 0 A) = UnforcedLeray.PhaseSpace.dy 0 (UnforcedLeray.PhaseSpace.dy 1 A) :=
    UnforcedLeray.PhaseSpace.dy_dy_comm hA 1 0
  have r20 : UnforcedLeray.PhaseSpace.dy 2 (UnforcedLeray.PhaseSpace.dy 0 A) = UnforcedLeray.PhaseSpace.dy 0 (UnforcedLeray.PhaseSpace.dy 2 A) :=
    UnforcedLeray.PhaseSpace.dy_dy_comm hA 2 0
  have r21 : UnforcedLeray.PhaseSpace.dy 2 (UnforcedLeray.PhaseSpace.dy 1 A) = UnforcedLeray.PhaseSpace.dy 1 (UnforcedLeray.PhaseSpace.dy 2 A) :=
    UnforcedLeray.PhaseSpace.dy_dy_comm hA 2 1
  funext x
  rw [curlH_curlT_apply]
  simp only [dy_curlT A hA, dy_divT A hA, gradT, lapT]
  ext i
  fin_cases i <;> simp [crossC, Fin.sum_univ_three, EuclideanSpace.single_apply, r10, r20, r21] <;> ring
