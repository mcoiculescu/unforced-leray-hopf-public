import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCellPairing
import UnforcedLeray.Lib.LerayLp.Cutoff

set_option autoImplicit false

noncomputable section

open MeasureTheory
open Set
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open NavierStokesR3.ComparisonCutoffs

/-- The actual real Newton potential, localized by the standard spatial cutoff. -/
def projectedPotentialReCutoff (R : ℝ) (Φ : SpaceTime → CVec3) : SpaceTime → ℝ :=
  fun z => cutoff R z.2 * projectedPotentialRePath Φ z

/-- The actual imaginary Newton potential, localized by the standard spatial cutoff. -/
def projectedPotentialImCutoff (R : ℝ) (Φ : SpaceTime → CVec3) : SpaceTime → ℝ :=
  fun z => cutoff R z.2 * projectedPotentialImPath Φ z

private theorem isPhaseTest_projectedPotentialCutoff_aux {P R : ℝ}
    (hR : 0 < R)
    (ψ : SpaceTime → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic (fun τ => fun y => ψ (τ, y)) P) :
    IsPhaseTest P (fun z : SpaceTime => cutoff R z.2 * ψ z) := by
  refine { smooth := (cutoff_smooth R).comp contDiff_snd |>.mul hψ
           periodic := ?_
           bounded_support := ?_ }
  · intro τ y
    exact congrArg (fun a : ℝ => cutoff R y * a) (congrFun (hper τ) y)
  · refine ⟨2 * R, ?_⟩
    intro τ y hy
    rw [cutoff_eq_zero hR (le_of_lt hy), zero_mul]

/-- The jointly smooth actual real Newton potential becomes a genuine compactly supported phase
test after the standard spatial cutoff. -/
theorem isPhaseTest_projectedPotentialReCutoff {P R : ℝ} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest P Φ) (hR : 0 < R) :
    IsPhaseTest P (projectedPotentialReCutoff R Φ) := by
  unfold projectedPotentialReCutoff
  exact isPhaseTest_projectedPotentialCutoff_aux hR _
    (contDiff_projectedPotentialRePath hΦ) (projectedPotentialRePath_periodic_joint hΦ)

/-- Imaginary-source counterpart of the compactly supported actual potential test. -/
theorem isPhaseTest_projectedPotentialImCutoff {P R : ℝ} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest P Φ) (hR : 0 < R) :
    IsPhaseTest P (projectedPotentialImCutoff R Φ) := by
  unfold projectedPotentialImCutoff
  exact isPhaseTest_projectedPotentialCutoff_aux hR _
    (contDiff_projectedPotentialImPath hΦ) (projectedPotentialImPath_periodic_joint hΦ)

/-- The exact spatial product rule for the localized actual real Newton potential. It separates the
main projected-test correction from the compact cutoff-shell term. -/
theorem gradField_projectedPotentialReCutoff {P R : ℝ} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    gradField (fun x => projectedPotentialReCutoff R Φ (τ, x)) y =
      cutoff R y • gradField (fun x => projectedPotentialRePath Φ (τ, x)) y +
        projectedPotentialRePath Φ (τ, y) • gradField (cutoff R) y := by
  ext i
  change gradField (fun x => projectedPotentialReCutoff R Φ (τ, x)) y i = _
  simp only [gradField_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  change spatialTestDerivative i
      (fun x => cutoff R x * projectedPotentialRePath Φ (τ, x)) y = _
  rw [spatialTestDerivative_mul (cutoff_smooth R)
    (projectedPotentialRePath_contDiff_slice hΦ τ)]

/-- Imaginary-source product rule with the same compact cutoff shell. -/
theorem gradField_projectedPotentialImCutoff {P R : ℝ} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest P Φ) (τ : ℝ) (y : Space) :
    gradField (fun x => projectedPotentialImCutoff R Φ (τ, x)) y =
      cutoff R y • gradField (fun x => projectedPotentialImPath Φ (τ, x)) y +
        projectedPotentialImPath Φ (τ, y) • gradField (cutoff R) y := by
  ext i
  change gradField (fun x => projectedPotentialImCutoff R Φ (τ, x)) y i = _
  simp only [gradField_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  change spatialTestDerivative i
      (fun x => cutoff R x * projectedPotentialImPath Φ (τ, x)) y = _
  rw [spatialTestDerivative_mul (cutoff_smooth R)
    (projectedPotentialImPath_contDiff_slice hΦ τ)]

#print axioms isPhaseTest_projectedPotentialReCutoff
#print axioms isPhaseTest_projectedPotentialImCutoff
#print axioms gradField_projectedPotentialReCutoff
#print axioms gradField_projectedPotentialImCutoff

end UnforcedLeray.Cons.C03.Concrete

end
