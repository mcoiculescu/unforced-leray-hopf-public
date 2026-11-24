import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedCurlCutoff
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialJointSmooth

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.PhaseSpace UnforcedLeray.PressureAnalysis
open UnforcedLeray.RieszLp

/-- The vector Newton potential of a compact smooth real phase test, evaluated at the joint
phase/spatial point. -/
def projectedTestNewtonVectorPotential (Φ : SpaceTime → Space) : SpaceTime → Space :=
  fun z => ∑ i : Fin 3,
    (∫ x, newtonPotential x * Φ (z - (0, x)) i) • coordinateVector i

theorem contDiff_projectedTestNewtonVectorPotential {P : ℝ} {Φ : SpaceTime → Space}
    (hΦ : IsPhaseTest P Φ) :
    ContDiff ℝ ∞ (projectedTestNewtonVectorPotential Φ) := by
  unfold projectedTestNewtonVectorPotential
  apply ContDiff.sum
  intro i hi
  have hcoord : IsPhaseTest P (fun z => Φ z i) :=
    hΦ.clm_comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)
  have hpot := contDiff_newtonSourceParamIntegral hcoord
  exact hpot.smul contDiff_const

theorem projectedTestNewtonVectorPotential_periodic {P : ℝ} {Φ : SpaceTime → Space}
    (hΦ : IsPhaseTest P Φ) :
    Function.Periodic (fun τ => fun y => projectedTestNewtonVectorPotential Φ (τ, y)) P := by
  intro τ
  funext y
  unfold projectedTestNewtonVectorPotential
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : (τ + P, y) - (0, x) = (τ + P, y - x) := by ext <;> simp
  have hp' : (τ, y) - (0, x) = (τ, y - x) := by ext <;> simp
  rw [hp, hp']
  exact congrArg (fun v : Space => newtonPotential x * v i) (hΦ.periodic τ (y - x))

theorem contDiff_spatialCurlST_of_contDiff {A : SpaceTime → Space}
    (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (spatialCurlST A) := by
  have hder : ContDiff ℝ ∞ (fun z : SpaceTime => fderiv ℝ A z) :=
    hA.fderiv_right (m := ∞) (by simp)
  unfold spatialCurlST
  apply ContDiff.sum
  intro j hj
  have hcomponent : ContDiff ℝ ∞
      (fun z : SpaceTime => fderiv ℝ A z (0, coordinateVector j)) :=
    hder.clm_apply contDiff_const
  change ContDiff ℝ ∞ (fun z : SpaceTime =>
    UnforcedLeray.L09.crossCLM (coordinateVector j)
      (fderiv ℝ A z (0, coordinateVector j)))
  exact (UnforcedLeray.L09.crossCLM (coordinateVector j)).contDiff.comp hcomponent

theorem spatialCurlST_periodic_of_periodic {P : ℝ} {A : SpaceTime → Space}
    (hA : ∀ τ y, A (τ + P, y) = A (τ, y)) :
    ∀ τ y, spatialCurlST A (τ + P, y) = spatialCurlST A (τ, y) := by
  intro τ y
  have hAper : ∀ z : SpaceTime, A (z + (P, 0)) = A z := by
    rintro ⟨s, x⟩
    have hp : (s, x) + (P, 0) = (s + P, x) := by ext <;> simp
    rw [hp]
    exact hA s x
  have hder := fderiv_add_of_invariant hAper (τ, y)
  have hp : (τ + P, y) = (τ, y) + (P, 0) := by ext <;> simp
  rw [hp]
  unfold spatialCurlST
  simp_rw [hder]

def projectedTestNewtonVectorPotentialCurl (Φ : SpaceTime → Space) : SpaceTime → Space :=
  spatialCurlST (projectedTestNewtonVectorPotential Φ)

theorem isSolTest_projectedTestNewtonVectorPotentialCurlCutoff {P R : ℝ}
    (hP : 0 < P) {Φ : SpaceTime → Space} (hΦ : IsPhaseTest P Φ) (hR : 0 < R) :
    IsSolTest P (projectedPotentialCurlCutoff R
      (projectedTestNewtonVectorPotentialCurl Φ)) := by
  apply isSolTest_projectedPotentialCurlCutoff hP
  · exact contDiff_spatialCurlST_of_contDiff
      (contDiff_projectedTestNewtonVectorPotential hΦ)
  · exact spatialCurlST_periodic_of_periodic (fun τ y =>
      congrFun (projectedTestNewtonVectorPotential_periodic hΦ τ) y)
  · exact hR

#print axioms contDiff_projectedTestNewtonVectorPotential
#print axioms projectedTestNewtonVectorPotential_periodic
#print axioms contDiff_spatialCurlST_of_contDiff
#print axioms spatialCurlST_periodic_of_periodic
#print axioms isSolTest_projectedTestNewtonVectorPotentialCurlCutoff

end UnforcedLeray.Cons.C03.Concrete

end
