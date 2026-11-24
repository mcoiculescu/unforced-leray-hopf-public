import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffShell
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffIntegrability
import NavierStokes.R3.ComparisonCutoffs

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open UnforcedLeray.B0412
open NavierStokesR3.ComparisonCutoffs

private theorem pairF_add_left_of_integrable_cell {P : ℝ} [Fact (0 < P)]
    {A B W : SpaceTime → CVec3}
    (hA : Integrable (fun z => dotL (A z) (W z)) (volume.restrict (phaseCell P)))
    (hB : Integrable (fun z => dotL (B z) (W z)) (volume.restrict (phaseCell P))) :
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

/-- The full complex Newton-gradient correction has zero phase pairing after combining its actual
real and imaginary source paths. The four main/shell integrability clauses are derived from the
actual product-cell correction bound and compact cutoff support. -/
theorem pairF_projectedNewtonCorrectionCutoff_main_eq_neg_shell {P R : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ)
    (hR : 0 < R) {w : Yq P q0E} (hw : IsPhaseSolenoidal w) :
    pairF P (fun z =>
      ofReV (cutoff R z.2 •
        gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
      ofImV (cutoff R z.2 •
        gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (fun z => rep w z.1 z.2) =
    - pairF P (fun z =>
      ofReV (projectedPotentialRePath Φ z • gradField (cutoff R) z.2) +
      ofImV (projectedPotentialImPath Φ z • gradField (cutoff R) z.2))
      (fun z => rep w z.1 z.2) := by
  let W : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  let mainRe : SpaceTime → CVec3 := fun z => ofReV
    (cutoff R z.2 • gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2)
  let mainIm : SpaceTime → CVec3 := fun z => ofImV
    (cutoff R z.2 • gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2)
  let shellRe : SpaceTime → CVec3 := fun z => ofReV
    (projectedPotentialRePath Φ z • gradField (cutoff R) z.2)
  let shellIm : SpaceTime → CVec3 := fun z => ofImV
    (projectedPotentialImPath Φ z • gradField (cutoff R) z.2)
  have hmainRe : Integrable (fun z => dotL (mainRe z) (W z))
      (volume.restrict (phaseCell P)) :=
    integrable_projectedPotentialReCutoffMain_pair_rep_cell hΦ
  have hmainIm : Integrable (fun z => dotL (mainIm z) (W z))
      (volume.restrict (phaseCell P)) :=
    integrable_projectedPotentialImCutoffMain_pair_rep_cell hΦ
  have hshellRe : Integrable (fun z => dotL (shellRe z) (W z))
      (volume.restrict (phaseCell P)) :=
    integrable_projectedPotentialReCutoffShell_pair_rep_cell hΦ hR
  have hshellIm : Integrable (fun z => dotL (shellIm z) (W z))
      (volume.restrict (phaseCell P)) :=
    integrable_projectedPotentialImCutoffShell_pair_rep_cell hΦ hR
  have hre := pairF_projectedPotentialReCutoff_main_eq_neg_shell hΦ hR hw hmainRe hshellRe
  have him := pairF_projectedPotentialImCutoff_main_eq_neg_shell hΦ hR hw hmainIm hshellIm
  have hmain := pairF_add_left_of_integrable_cell hmainRe hmainIm
  have hshell := pairF_add_left_of_integrable_cell hshellRe hshellIm
  change pairF P (fun z => mainRe z + mainIm z) W =
      - pairF P (fun z => shellRe z + shellIm z) W
  rw [hmain, hre, him, hshell]
  abel

#print axioms pairF_projectedNewtonCorrectionCutoff_main_eq_neg_shell

end UnforcedLeray.Cons.C03.Concrete

end
