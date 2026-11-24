import UnforcedLeray.Short.PartIIb.Sub.B1
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedCurlCellLp

/-!
# Part II-b, task `PartII-b:B1` leaf: `ProjTestIsNewtonCurl`

The slice-wise Leray projection of the complexification of a real phase test is the curl of the
Newton curl potential, a.e. on each phase slice. This is a copy of the private theorem
`lerayProjected_complexify_eq_actual_ae` in
`Cons/L2/BackgroundConcrete/SelectedProjectedCurlCellLp.lean` (lines 35-96). The complexification
is handled by `isPhaseTest_realC_comp`, and the left side is rewritten by `projTest_of_isPhaseTest`.
Private names of that file cannot be imported, so the proof is copied and the source is unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete
open UnforcedLeray.PhaseSpace UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.PressureAnalysis
open NavierStokesR3.ComparisonCutoffs

/-- The complexification `z ↦ realC (Φ z)` of a real-valued field. -/
private def cplxTestAux (Φ : ℝ × Space → Space) : ℝ × Space → CVec3 :=
  fun z => realC (Φ z)

private theorem projTestIsNewtonCurl_realC_eq_ofReV : realC = ofReV := by
  funext x
  ext i
  simp [UnforcedLeray.B0412.realC_apply, ofReV_apply]

private theorem projTestIsNewtonCurl_cplx_phase {P : ℝ} {Φ : ℝ × Space → Space}
    (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (cplxTestAux Φ) :=
  isPhaseTest_realC_comp hΦ

private theorem projTestIsNewtonCurl_ae
    {P : ℝ} [Fact (0 < P)] {Φ : ℝ × Space → Space} (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    (fun y : Space => projTest P (cplxTestAux Φ) (τ, y)) =ᵐ[volume]
      fun y => realC (spatialCurlST (projectedTestNewtonVectorPotentialCurl Φ) (τ, y)) := by
  have hC : IsPhaseTest P (cplxTestAux Φ) := projTestIsNewtonCurl_cplx_phase hΦ
  rw [projTest_of_isPhaseTest hC]
  have hnewton := lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae
    (one_lt_of_holderConjugate q0E_ne_top) (conjExp_ne_top one_lt_q0E) hC τ
  have hreal (i : Fin 3) (y : Space) :
      projectedPotentialReTest (cplxTestAux Φ) τ i y = Φ (τ, y) i := by
    simp [projectedPotentialReTest, cplxTestAux, UnforcedLeray.B0412.realC_apply]
  have himag (i : Fin 3) (y : Space) :
      projectedPotentialImTest (cplxTestAux Φ) τ i y = 0 := by
    simp [projectedPotentialImTest, cplxTestAux, UnforcedLeray.B0412.realC_apply]
  have himagFun : projectedPotentialImTest (cplxTestAux Φ) τ = fun _ _ => 0 := by
    funext i y
    exact himag i y
  have hdiv0 : divTest (fun (_ : Fin 3) (_ : Space) => (0 : ℝ)) = 0 := by
    funext x
    simp [divTest, spatialTestDerivative, fderiv_const_apply]
  have hzero : lerayPotential (fun (_ : Fin 3) (_ : Space) => (0 : ℝ)) = 0 := by
    funext y
    change newtonConv (divTest (fun (_ : Fin 3) (_ : Space) => (0 : ℝ))) y = 0
    rw [hdiv0]
    simp [newtonConv]
  have hzero' : lerayPotential (projectedPotentialImTest (cplxTestAux Φ) τ) = 0 := by
    rw [himagFun]
    exact hzero
  have hReFun : projectedPotentialReTest (cplxTestAux Φ) τ =
      fun i y => Φ (τ, y) i := by
    funext i y
    exact hreal i y
  have hactual (y : Space) :
      realC (spatialCurlST (projectedTestNewtonVectorPotentialCurl Φ) (τ, y)) =
      realC (vecField (fun i x => Φ (τ, x) i) y +
        gradField (lerayPotential (fun i x => Φ (τ, x) i)) y) := by
    have h := projectedTestNewtonCurl_eq_projectionFormula hΦ τ y
    exact congrArg realC h
  filter_upwards [hnewton] with y hy
  rw [hy, hReFun, hzero']
  have hsource : cplxTestAux Φ (τ, y) = ofReV (vecField (fun i x => Φ (τ, x) i) y) := by
    ext i
    simp [cplxTestAux, projTestIsNewtonCurl_realC_eq_ofReV, vecField_apply]
  rw [hsource, hactual y, projTestIsNewtonCurl_realC_eq_ofReV, map_add]
  simp [gradField, spatialTestDerivative]

/-- **The Leray projection of a real test is the curl of its Newton curl potential.** -/
theorem projTestIsNewtonCurl : ProjTestIsNewtonCurl := by
  intro P _ φ hφ τ
  exact projTestIsNewtonCurl_ae hφ τ

end UnforcedLeray.Short.IIb
