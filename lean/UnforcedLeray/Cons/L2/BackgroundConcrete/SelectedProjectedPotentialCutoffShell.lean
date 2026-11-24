import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffSolenoidal
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffImSolenoidal
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCellPairing
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellPairF

set_option autoImplicit false

noncomputable section

open MeasureTheory
open Set

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open UnforcedLeray.B0412
open NavierStokesR3.ComparisonCutoffs

private theorem pairF_add_left_of_integrable_cell {P : ℝ} [Fact (0 < P)]
    {A B : SpaceTime → CVec3} {W : SpaceTime → CVec3}
    (hA : Integrable (fun z => dotL (A z) (W z))
      (volume.restrict (phaseCell P)))
    (hB : Integrable (fun z => dotL (B z) (W z))
      (volume.restrict (phaseCell P))) :
    pairF P (fun z => A z + B z) W = pairF P A W + pairF P B W := by
  have hsum : Integrable (fun z => dotL (A z + B z) (W z))
      (volume.restrict (phaseCell P)) := by
    refine (hA.add hB).congr (ae_of_all _ fun z => ?_)
    simp [dotL_apply]
  rw [pairF_eq_restrictedProductIntegral hsum,
    pairF_eq_restrictedProductIntegral hA, pairF_eq_restrictedProductIntegral hB]
  have hpoint (z : SpaceTime) : dotL (A z + B z) (W z) =
      dotL (A z) (W z) + dotL (B z) (W z) := by
    simp [dotL_apply]
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_add hA hB]
  simp [smul_add]

/-- The main and cutoff-shell terms of the actual real Newton-gradient correction cancel under
phase solenoidality. Only the two actual product-cell integrability guards are exposed. -/
theorem pairF_projectedPotentialReCutoff_main_eq_neg_shell {P R : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ)
    (hR : 0 < R) {w : Yq P q0E} (hw : IsPhaseSolenoidal w)
    (hmain : Integrable (fun z => dotL
      (ofReV (cutoff R z.2 •
        gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2))
      (rep w z.1 z.2)) (volume.restrict (phaseCell P)))
    (hshell : Integrable (fun z => dotL
      (ofReV (projectedPotentialRePath Φ z • gradField (cutoff R) z.2))
      (rep w z.1 z.2)) (volume.restrict (phaseCell P))) :
    pairF P (fun z => ofReV
      (cutoff R z.2 • gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2))
      (fun z => rep w z.1 z.2) =
    - pairF P (fun z => ofReV
      (projectedPotentialRePath Φ z • gradField (cutoff R) z.2))
      (fun z => rep w z.1 z.2) := by
  let A : SpaceTime → CVec3 := fun z => ofReV
    (cutoff R z.2 • gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2)
  let B : SpaceTime → CVec3 := fun z => ofReV
    (projectedPotentialRePath Φ z • gradField (cutoff R) z.2)
  let W : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  have hzero := phaseSolenoidal_pairF_projectedPotentialReCutoff_zero hΦ hR hw
  have hdecomp : (fun z => ofReV
      (gradField (fun y => projectedPotentialReCutoff R Φ (z.1, y)) z.2)) = fun z => A z + B z := by
    funext z
    rw [gradField_projectedPotentialReCutoff hΦ]
    simp [A, B, map_add, map_smul]
  rw [hdecomp] at hzero
  have hsum := pairF_add_left_of_integrable_cell hmain hshell
  rw [show (fun z => A z) = (fun z => ofReV
      (cutoff R z.2 • gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2)) by rfl,
    show (fun z => B z) = (fun z => ofReV
      (projectedPotentialRePath Φ z • gradField (cutoff R) z.2)) by rfl,
    show (fun z => W z) = (fun z => rep w z.1 z.2) by rfl] at hsum
  rw [hsum] at hzero
  linear_combination hzero

/-- Imaginary-source main/shell cancellation. -/
theorem pairF_projectedPotentialImCutoff_main_eq_neg_shell {P R : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ)
    (hR : 0 < R) {w : Yq P q0E} (hw : IsPhaseSolenoidal w)
    (hmain : Integrable (fun z => dotL
      (ofImV (cutoff R z.2 •
        gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (rep w z.1 z.2)) (volume.restrict (phaseCell P)))
    (hshell : Integrable (fun z => dotL
      (ofImV (projectedPotentialImPath Φ z • gradField (cutoff R) z.2))
      (rep w z.1 z.2)) (volume.restrict (phaseCell P))) :
    pairF P (fun z => ofImV
      (cutoff R z.2 • gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (fun z => rep w z.1 z.2) =
    - pairF P (fun z => ofImV
      (projectedPotentialImPath Φ z • gradField (cutoff R) z.2))
      (fun z => rep w z.1 z.2) := by
  let A : SpaceTime → CVec3 := fun z => ofImV
    (cutoff R z.2 • gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2)
  let B : SpaceTime → CVec3 := fun z => ofImV
    (projectedPotentialImPath Φ z • gradField (cutoff R) z.2)
  let W : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  have hzero := phaseSolenoidal_pairF_projectedPotentialImCutoff_ofIm_zero hΦ hR hw
  have hdecomp : (fun z => ofImV
      (gradField (fun y => projectedPotentialImCutoff R Φ (z.1, y)) z.2)) = fun z => A z + B z := by
    funext z
    rw [gradField_projectedPotentialImCutoff hΦ]
    simp [A, B, map_add, map_smul]
  rw [hdecomp] at hzero
  have hsum := pairF_add_left_of_integrable_cell hmain hshell
  rw [show (fun z => A z) = (fun z => ofImV
      (cutoff R z.2 • gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2)) by rfl,
    show (fun z => B z) = (fun z => ofImV
      (projectedPotentialImPath Φ z • gradField (cutoff R) z.2)) by rfl,
    show (fun z => W z) = (fun z => rep w z.1 z.2) by rfl] at hsum
  rw [hsum] at hzero
  linear_combination hzero

#print axioms pairF_projectedPotentialReCutoff_main_eq_neg_shell
#print axioms pairF_projectedPotentialImCutoff_main_eq_neg_shell

end UnforcedLeray.Cons.C03.Concrete

end
