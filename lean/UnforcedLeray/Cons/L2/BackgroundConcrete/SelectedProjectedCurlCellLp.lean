import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedTestCellRep
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedCurlProjectionLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedCurlGradientLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedCurlIsLeray
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotential
import UnforcedLeray.Lib.AxisymmetricB.Bridge

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.PressureAnalysis
open NavierStokesR3.ComparisonCutoffs

local instance qDualGeOne : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

local instance qDualNeTop : Fact (conjExp q0E ≠ ⊤) := ⟨conjExp_ne_top one_lt_q0E⟩

private def actualProjectedCurl (Φ : SpaceTime → Space) : SpaceTime → CVec3 :=
  fun z => realC (spatialCurlST (fun x => spatialCurlST
    (projectedTestNewtonVectorPotential Φ) x) z)

private def complexifyTest (Φ : SpaceTime → Space) : SpaceTime → CVec3 :=
  fun z => realC (Φ z)

private theorem realC_eq_ofReV_cell : realC = ofReV := by
  funext x
  ext i
  simp [realC_apply, ofReV_apply]

private theorem isPhaseTest_complexifyTest {P : ℝ} {Φ : SpaceTime → Space}
    (hΦ : IsPhaseTest P Φ) : IsPhaseTest P (complexifyTest Φ) := by
  have hmap : realC = UnforcedLeray.Axi.cplxV := by
    funext x
    ext i
    simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]
  change IsPhaseTest P (fun z => realC (Φ z))
  rw [hmap]
  exact hΦ.clm_comp UnforcedLeray.Axi.cplxV

private theorem lerayProjected_complexify_eq_actual_ae
    {P : ℝ} [Fact (0 < P)] {Φ : SpaceTime → Space} (hΦ : IsPhaseTest P Φ)
    (τ : ℝ) :
    (fun y : Space => lerayProjectedPhaseTest
      (one_lt_of_holderConjugate q0E_ne_top) (conjExp_ne_top one_lt_q0E)
      ((isPhaseTest_complexifyTest hΦ).isSliceTest (conjExp q0E)) (τ, y)) =ᵐ[volume]
      fun y => actualProjectedCurl Φ (τ, y) := by
  let hC := isPhaseTest_complexifyTest hΦ
  have hnewton := lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae
    (one_lt_of_holderConjugate q0E_ne_top) (conjExp_ne_top one_lt_q0E) hC τ
  have hreal (i : Fin 3) (y : Space) :
      projectedPotentialReTest (complexifyTest Φ) τ i y = Φ (τ, y) i := by
    simp [projectedPotentialReTest, complexifyTest, B0412.realC_apply]
  have himag (i : Fin 3) (y : Space) :
      projectedPotentialImTest (complexifyTest Φ) τ i y = 0 := by
    simp [projectedPotentialImTest, complexifyTest, B0412.realC_apply]
  have himagFun : projectedPotentialImTest (complexifyTest Φ) τ = fun _ _ => 0 := by
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
  have hzero' : lerayPotential (projectedPotentialImTest (complexifyTest Φ) τ) = 0 := by
    rw [himagFun]
    exact hzero
  have hReFun : projectedPotentialReTest (complexifyTest Φ) τ =
      fun i y => Φ (τ, y) i := by
    funext i y
    exact hreal i y
  have hactual (y : Space) : actualProjectedCurl Φ (τ, y) =
      realC (vecField (fun i x => Φ (τ, x) i) y +
        gradField (lerayPotential (fun i x => Φ (τ, x) i)) y) := by
    simp [actualProjectedCurl, projectedTestNewtonCurl_eq_projectionFormula hΦ τ y]
  filter_upwards [hnewton] with y hy
  rw [hy, hReFun, hzero']
  have hsource : complexifyTest Φ (τ, y) =
      ofReV (vecField (fun i x => Φ (τ, x) i) y) := by
    ext i
    simp [complexifyTest, realC_eq_ofReV_cell, vecField_apply]
  rw [hsource, hactual y, realC_eq_ofReV_cell, map_add]
  simp [gradField, spatialTestDerivative]

/-- The actual Newton-curl Leray projection has the dual-exponent product-cell bound. -/
theorem memLp_actualProjectedCurl_cell_dual_q0
    {P : ℝ} [Fact (0 < P)] {Φ : SpaceTime → Space} (hΦ : IsPhaseTest P Φ) :
    MemLp (actualProjectedCurl Φ) (conjExp q0E)
      (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) := by
  let Ψ : SpaceTime → CVec3 := lerayProjectedPhaseTest
    (one_lt_of_holderConjugate q0E_ne_top) (conjExp_ne_top one_lt_q0E)
    ((isPhaseTest_complexifyTest hΦ).isSliceTest (conjExp q0E))
  have hΨ : IsSliceTest P (conjExp q0E) Ψ :=
    isSliceTest_lerayProjectedPhaseTest
      (one_lt_of_holderConjugate q0E_ne_top) (conjExp_ne_top one_lt_q0E)
      ((isPhaseTest_complexifyTest hΦ).isSliceTest (conjExp q0E))
  have hrealC : ContDiff ℝ ∞ (fun x : Space => realC x) := by
    have hEq : realC = UnforcedLeray.Axi.cplxV := by
      funext x
      ext i
      simp [realC_apply, UnforcedLeray.Axi.cplxV_apply]
    rw [hEq]
    exact UnforcedLeray.Axi.cplxV.contDiff.comp contDiff_id
  have hcont : StronglyMeasurable (actualProjectedCurl Φ) := by
    exact (hrealC.comp (contDiff_spatialCurlST_of_contDiff
      (contDiff_spatialCurlST_of_contDiff
        (contDiff_projectedTestNewtonVectorPotential hΦ)))).continuous.stronglyMeasurable
  exact memLp_of_ae_sliceTest_on_periodCell (P := P) (q := conjExp q0E)
    (conjExp_ne_top one_lt_q0E) hcont hΨ (by
      filter_upwards [] with τ
      exact (lerayProjected_complexify_eq_actual_ae hΦ τ).symm)

#print axioms memLp_actualProjectedCurl_cell_dual_q0

end UnforcedLeray.Cons.C03.Concrete

end
