import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffSolenoidal
import UnforcedLeray.Lib.LerayC.PhaseSol

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open UnforcedLeray.B0412

/-- Constant complex scaling passes through the phase-space gradient. -/
private theorem gradT_const_smul {P : ℝ} {ψ : SpaceTime → ℂ}
    (hψ : IsPhaseTest P ψ) (c : ℂ) :
    PhaseSpace.gradT (c • ψ) = fun z => c • PhaseSpace.gradT ψ z := by
  funext z
  ext i
  rw [RieszLp.gradT_apply_coord]
  change PhaseSpace.dy i (c • ψ) z = c * PhaseSpace.gradT ψ z i
  rw [RieszLp.gradT_apply_coord]
  simp only [PhaseSpace.dy]
  change (fderiv ℝ (fun y : SpaceTime => c * ψ y) z) (0, coordinateVector i) =
    c * (fderiv ℝ ψ z) (0, coordinateVector i)
  have hfd := fderiv_fun_const_smul ((hψ.smooth.differentiable (by simp) z)) c
  simpa [Pi.smul_apply, smul_eq_mul] using
    congrArg (fun L : SpaceTime →L[ℝ] ℂ => L (0, coordinateVector i)) hfd

/-- The actual imaginary Newton-potential gradient is the phase gradient of its compactly
supported complex test after multiplication by `i`; hence phase solenoidality annihilates its
`ofImV` embedding. -/
theorem phaseSolenoidal_pairF_projectedPotentialImCutoff_ofIm_zero {P : ℝ}
    [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) {R : ℝ}
    (hR : 0 < R) {w : Yq P q0E} (hw : IsPhaseSolenoidal w) :
    pairF P
      (fun z => ofImV
        (gradField (fun x => projectedPotentialImCutoff R Φ (z.1, x)) z.2))
      (fun z => rep w z.1 z.2) = 0 := by
  let ψ : SpaceTime → ℝ := projectedPotentialImCutoff R Φ
  have hψ : IsPhaseTest P ψ := isPhaseTest_projectedPotentialImCutoff hΦ hR
  let ψC : SpaceTime → ℂ := fun z => (ψ z : ℂ)
  have hψC : IsPhaseTest P ψC := hψ.clm_comp Complex.ofRealCLM
  let ψI : SpaceTime → ℂ := Complex.I • ψC
  have hψI : IsPhaseTest P ψI := hψC.const_smul Complex.I
  have hzero := hw ψI hψI
  rw [phasePair_eq_pairF_rep hψI.gradT w] at hzero
  have hbaseGrad : PhaseSpace.gradT ψC = fun z =>
      ofReV (gradField (fun x => ψ (z.1, x)) z.2) := by
    funext z
    exact gradT_ofReal_eq_ofReV_gradField hψ z.1 z.2
  have hgrad : PhaseSpace.gradT ψI = fun z =>
      ofImV (gradField (fun x => ψ (z.1, x)) z.2) := by
    rw [gradT_const_smul hψC Complex.I, hbaseGrad]
    funext z
    exact I_smul_ofReV _
  rw [hgrad] at hzero
  exact hzero

#print axioms phaseSolenoidal_pairF_projectedPotentialImCutoff_ofIm_zero

end UnforcedLeray.Cons.C03.Concrete

end
