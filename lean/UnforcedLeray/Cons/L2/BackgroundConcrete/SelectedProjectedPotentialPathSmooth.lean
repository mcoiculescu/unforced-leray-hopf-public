import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialJointSmooth

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.PressureAnalysis

/-- Joint smoothness of the actual real Newton potential path defining the projected-test
correction. -/
theorem contDiff_projectedPotentialRePath {P : ℝ} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest P Φ) : ContDiff ℝ ∞ (projectedPotentialRePath Φ) := by
  have hD : IsPhaseTest P (projectedPotentialReDiv Φ) :=
    isPhaseTest_projectedPotentialReDiv hΦ
  have hbase := contDiff_newtonSourceParamIntegral hD
  have hEq : projectedPotentialRePath Φ = fun p : SpaceTime =>
      ∫ x, newtonPotential x * projectedPotentialReDiv Φ (p - (0, x)) := by
    funext p
    rcases p with ⟨τ, y⟩
    rw [projectedPotentialRePath_eq_paramIntegral hΦ τ y]
    unfold projectedPotentialReParamIntegral
    apply integral_congr_ae
    filter_upwards [] with x
    have hp : (τ, y) - (0, x) = (τ, y - x) := by ext <;> simp
    rw [hp]
  rw [hEq]
  exact hbase

/-- Joint smoothness of the actual imaginary Newton potential path defining the projected-test
correction. -/
theorem contDiff_projectedPotentialImPath {P : ℝ} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest P Φ) : ContDiff ℝ ∞ (projectedPotentialImPath Φ) := by
  have hD : IsPhaseTest P (projectedPotentialImDiv Φ) :=
    isPhaseTest_projectedPotentialImDiv hΦ
  have hbase := contDiff_newtonSourceParamIntegral hD
  have hEq : projectedPotentialImPath Φ = fun p : SpaceTime =>
      ∫ x, newtonPotential x * projectedPotentialImDiv Φ (p - (0, x)) := by
    funext p
    rcases p with ⟨τ, y⟩
    rw [projectedPotentialImPath_eq_paramIntegral hΦ τ y]
    unfold projectedPotentialImParamIntegral
    apply integral_congr_ae
    filter_upwards [] with x
    have hp : (τ, y) - (0, x) = (τ, y - x) := by ext <;> simp
    rw [hp]
  rw [hEq]
  exact hbase

/-- The actual real Newton-potential pressure primitive has the phase periodicity inherited from
its source. -/
theorem projectedPotentialRePath_periodic_joint {P : ℝ} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest P Φ) :
    Function.Periodic (fun τ => fun y => projectedPotentialRePath Φ (τ, y)) P := by
  intro τ
  funext y
  exact projectedPotentialRePath_periodic hΦ τ y

/-- Imaginary-source counterpart of the actual Newton-potential periodicity. -/
theorem projectedPotentialImPath_periodic_joint {P : ℝ} {Φ : SpaceTime → CVec3}
    (hΦ : IsPhaseTest P Φ) :
    Function.Periodic (fun τ => fun y => projectedPotentialImPath Φ (τ, y)) P := by
  intro τ
  funext y
  exact projectedPotentialImPath_periodic hΦ τ y

#print axioms contDiff_projectedPotentialRePath
#print axioms contDiff_projectedPotentialImPath
#print axioms projectedPotentialRePath_periodic_joint
#print axioms projectedPotentialImPath_periodic_joint

end UnforcedLeray.Cons.C03.Concrete

end
