import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCompactCutoff
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF
import UnforcedLeray.Lib.LerayC.PhaseSol

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp UnforcedLeray.B0412

/-- The phase-space gradient of a real-valued smooth scalar is the complexification of its
ordinary spatial gradient. -/
theorem gradT_ofReal_eq_ofReV_gradField {P : ℝ} {ψ : ℝ × Space → ℝ}
    (hψ : IsPhaseTest P ψ) (τ : ℝ) (y : Space) :
    PhaseSpace.gradT (fun z => (ψ z : ℂ)) (τ, y) =
      ofReV (gradField (fun x => ψ (τ, x)) y) := by
  ext i
  rw [RieszLp.gradT_apply_coord]
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (τ, y)) (τ, y) :=
    (hψ.smooth.differentiable (by simp) (τ, y)).hasFDerivAt
  have hcomplex : HasFDerivAt (fun z => (ψ z : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ ψ (τ, y))) (τ, y) :=
    Complex.ofRealCLM.hasFDerivAt.comp (τ, y) hψd
  have hslice : HasFDerivAt (fun x : Space => ψ (τ, x))
      ((fderiv ℝ ψ (τ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hψd.comp y (hasFDerivAt_prodMk_right τ y)
  have hderiv : (fderiv ℝ ψ (τ, y)) (0, coordinateVector i) =
      spatialTestDerivative i (fun x => ψ (τ, x)) y := by
    rw [spatialTestDerivative, hslice.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [PhaseSpace.dy, hcomplex.fderiv]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    ofReV_apply, gradField_apply]
  rw [hderiv]

/-- Phase solenoidality annihilates the actual compactly supported real Newton-potential gradient. -/
theorem phaseSolenoidal_pairF_projectedPotentialReCutoff_zero {P : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) {R : ℝ}
    (hR : 0 < R) {w : Yq P q0E} (hw : IsPhaseSolenoidal w) :
    pairF P
      (fun z => ofReV
        (gradField (fun x => projectedPotentialReCutoff R Φ (z.1, x)) z.2))
      (fun z => rep w z.1 z.2) = 0 := by
  let ψ : SpaceTime → ℝ := projectedPotentialReCutoff R Φ
  have hψ : IsPhaseTest P ψ := isPhaseTest_projectedPotentialReCutoff hΦ hR
  let ψC : SpaceTime → ℂ := fun z => (ψ z : ℂ)
  have hψC : IsPhaseTest P ψC := hψ.clm_comp Complex.ofRealCLM
  have hzero := hw ψC hψC
  rw [phasePair_eq_pairF_rep hψC.gradT w] at hzero
  have hgrad : PhaseSpace.gradT ψC = fun z =>
      ofReV (gradField (fun x => ψ (z.1, x)) z.2) := by
    funext z
    exact gradT_ofReal_eq_ofReV_gradField hψ z.1 z.2
  rw [hgrad] at hzero
  exact hzero

/-- Imaginary-source version of the compact cutoff gradient annihilation. -/
theorem phaseSolenoidal_pairF_projectedPotentialImCutoff_zero {P : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) {R : ℝ}
    (hR : 0 < R) {w : Yq P q0E} (hw : IsPhaseSolenoidal w) :
    pairF P
      (fun z => ofReV
        (gradField (fun x => projectedPotentialImCutoff R Φ (z.1, x)) z.2))
      (fun z => rep w z.1 z.2) = 0 := by
  let ψ : SpaceTime → ℝ := projectedPotentialImCutoff R Φ
  have hψ : IsPhaseTest P ψ := isPhaseTest_projectedPotentialImCutoff hΦ hR
  let ψC : SpaceTime → ℂ := fun z => (ψ z : ℂ)
  have hψC : IsPhaseTest P ψC := hψ.clm_comp Complex.ofRealCLM
  have hzero := hw ψC hψC
  rw [phasePair_eq_pairF_rep hψC.gradT w] at hzero
  have hgrad : PhaseSpace.gradT ψC = fun z =>
      ofReV (gradField (fun x => ψ (z.1, x)) z.2) := by
    funext z
    exact gradT_ofReal_eq_ofReV_gradField hψ z.1 z.2
  rw [hgrad] at hzero
  exact hzero

#print axioms gradT_ofReal_eq_ofReV_gradField
#print axioms phaseSolenoidal_pairF_projectedPotentialReCutoff_zero
#print axioms phaseSolenoidal_pairF_projectedPotentialImCutoff_zero

end UnforcedLeray.Cons.C03.Concrete

end
