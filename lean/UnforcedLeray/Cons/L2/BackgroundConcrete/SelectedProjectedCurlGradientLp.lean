import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedCurlProjectionLp
import UnforcedLeray.Lib.CZL2.TestOffSupport
import UnforcedLeray.Lib.LerayLp.Cutoff
import UnforcedLeray.Loc.L14Realization.PressureDiv

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp
open NavierStokesR3.ComparisonCutoffs
open scoped ContDiff

local instance qgrad_ge_one : Fact (1 ≤ ENNReal.ofReal (11 / 3 : ℝ)) := ⟨by norm_num⟩

private theorem spatialTestDerivative_rieszPairTest {f : Space → ℝ}
    (hf : IsSpatialTest f) (i k j : Fin 3) :
    spatialTestDerivative j (rieszPairTest i k f) =
      rieszPairTest i k (spatialTestDerivative j f) := by
  rw [rieszPairTest_eq_newtonConv hf,
    spatialTestDerivative_newtonConv ((hf.derivative k).derivative i) j,
    rieszPairTest_eq_newtonConv (hf.derivative j)]
  congr 1
  have h1 := SobolevGraph.spatialTestDerivative_comm (hf.derivative k) j i
  have h2 := SobolevGraph.spatialTestDerivative_comm hf j k
  calc
    spatialTestDerivative j (spatialTestDerivative i (spatialTestDerivative k f)) =
        spatialTestDerivative i (spatialTestDerivative j (spatialTestDerivative k f)) := h1
    _ = spatialTestDerivative i (spatialTestDerivative k (spatialTestDerivative j f)) :=
      congrArg (spatialTestDerivative i) h2

private theorem exists_powWeight3_rieszPairTest {f : Space → ℝ}
    (hf : IsSpatialTest f) (i k : Fin 3) :
    ∃ M, ∀ y, |rieszPairTest i k f y| ≤ M * powWeight 3 y := by
  obtain ⟨C, R, hfar⟩ := rieszPairTest_decay hf i k
  have hr : 1 ≤ max 1 R := le_max_left _ _
  refine exists_decay_bound_three
    (rieszPairTest_contDiff hf i k).continuous (r := max 1 R) (A := C) hr ?_
  intro y hy
  exact hfar y (le_trans (le_max_right _ _) hy)

private theorem exists_hessian_lerayPotential_powWeight3
    {f : Fin 3 → Space → ℝ} (hf : ∀ i, IsSpatialTest (f i)) :
    ∃ M, 0 ≤ M ∧ ∀ i j y,
      |spatialTestDerivative i (spatialTestDerivative j (lerayPotential f)) y| ≤
        M * powWeight 3 y := by
  have hRiesz : ∀ i j k : Fin 3, ∃ M, ∀ y,
      |rieszPairTest i k (spatialTestDerivative j (f k)) y| ≤ M * powWeight 3 y := by
    intro i j k
    exact exists_powWeight3_rieszPairTest ((hf k).derivative j) i k
  choose M hM using hRiesz
  let C : ℝ := ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, |M i j k|
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro i j y
  have hM0 : ∀ k : Fin 3, 0 ≤ M i j k := by
    intro k
    have h := hM i j k (0 : Space)
    have hp := powWeight_pos 3 (0 : Space)
    have hleft : 0 ≤ |rieszPairTest i k (spatialTestDerivative j (f k)) 0| := abs_nonneg _
    nlinarith
  have hderiv : spatialTestDerivative i (lerayPotential f) =
      fun x => ∑ k : Fin 3, rieszPairTest i k (f k) x := by
    funext x
    exact spatialTestDerivative_lerayPotential_eq_sum hf i x
  have hstep := congrArg (fun g : Space → ℝ => spatialTestDerivative j g y) hderiv.symm
  rw [UnforcedLeray.Blueprint.L14.spatialTestDerivative_comm_of_contDiff
    (lerayPotential_contDiff hf) i j y]
  rw [hstep.symm]
  rw [spatialTestDerivative_sum' Finset.univ
    (fun k => rieszPairTest_contDiff (hf k) i k) j y]
  rw [show (∑ k : Fin 3, spatialTestDerivative j (rieszPairTest i k (f k)) y) =
      ∑ k : Fin 3, rieszPairTest i k (spatialTestDerivative j (f k)) y from by
        apply Finset.sum_congr rfl
        intro k hk
        exact congrFun (spatialTestDerivative_rieszPairTest (hf k) i k j) y]
  calc
    |∑ k : Fin 3, rieszPairTest i k (spatialTestDerivative j (f k)) y|
        ≤ ∑ k : Fin 3,
          |rieszPairTest i k (spatialTestDerivative j (f k)) y| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ k : Fin 3, |M i j k|) * powWeight 3 y := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun k hk =>
        (hM i j k y).trans (mul_le_mul_of_nonneg_right (le_abs_self (M i j k))
          (powWeight_nonneg 3 y))
    _ ≤ C * powWeight 3 y := by
      apply mul_le_mul_of_nonneg_right _ (powWeight_nonneg 3 y)
      dsimp [C]
      have hj : (∑ k' : Fin 3, |M i j k'|) ≤
          ∑ j' : Fin 3, ∑ k' : Fin 3, |M i j' k'| :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun j' : Fin 3 => ∑ k' : Fin 3, |M i j' k'|)
          (fun j' _ => Finset.sum_nonneg fun k' _ => abs_nonneg _)
          (Finset.mem_univ j)
      have hi : (∑ j' : Fin 3, ∑ k' : Fin 3, |M i j' k'|) ≤
          ∑ i' : Fin 3, ∑ j' : Fin 3, ∑ k' : Fin 3, |M i' j' k'| :=
        Finset.single_le_sum (s := Finset.univ)
          (f := fun i' : Fin 3 => ∑ j' : Fin 3, ∑ k' : Fin 3, |M i' j' k'|)
          (fun i' _ => Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun k' _ => abs_nonneg _)
          (Finset.mem_univ i)
      exact le_trans hj hi

/-- The spatial derivative of the actual projected Newton-curl test belongs to the quadratic
dual exponent. Its Hessian tail is obtained by differentiating the compact source in the Riesz
pair representation, not by adding regularity assumptions on the projected test. -/
theorem memLp_projectedTestNewtonCurl_spatialDerivative_q11third
    {P : ℝ} {Φ : SpaceTime → Space} (hΦ : IsPhaseTest P Φ) (τ : ℝ)
    (i j : Fin 3) :
    MemLp (fun y : Space => spatialTestDerivative j
      (fun y => (spatialCurlST
        (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z) (τ, y)) i) y)
      (ENNReal.ofReal (11 / 3 : ℝ)) volume := by
  let f : Fin 3 → Space → ℝ := fun k y => Φ (τ, y) k
  have hf : ∀ k, IsSpatialTest (f k) := fun k => by
    refine ⟨(EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp
      (hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)), ?_⟩
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact UnforcedLeray.B0005.hasCompactSupport_of_bound (R := R) fun y hy => by
      simp [f, hR τ y hy]
  have hΦsmooth : ContDiff ℝ ∞ (fun y : Space => Φ (τ, y)) :=
    hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hψsmooth : ContDiff ℝ ∞ (lerayPotential f) := lerayPotential_contDiff hf
  have hproj : (fun y : Space =>
      spatialCurlST (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z)
        (τ, y)) = vecField f + gradField (lerayPotential f) := by
    funext y
    simpa [f] using projectedTestNewtonCurl_eq_projectionFormula hΦ τ y
  have hcomponent : (fun y : Space =>
      (spatialCurlST (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z)
        (τ, y)) i) = fun y => f i y + spatialTestDerivative i (lerayPotential f) y := by
    funext y
    rw [congrFun hproj y]
    simp [vecField_apply, gradField_apply, f]
  have hderiv : (fun y : Space => spatialTestDerivative j
      (fun y => (spatialCurlST
        (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z) (τ, y)) i) y) =
      fun y => spatialTestDerivative j (f i) y +
        spatialTestDerivative j (spatialTestDerivative i (lerayPotential f)) y := by
    funext y
    rw [hcomponent]
    exact spatialTestDerivative_add (hf i).smooth
      (UnforcedLeray.PressureAnalysis.contDiff_spatialTestDerivative hψsmooth i) j y
  have hess := exists_hessian_lerayPotential_powWeight3 hf
  obtain ⟨M, hM0, hM⟩ := hess
  have hp1 : 1 < ENNReal.ofReal (11 / 3 : ℝ) := by norm_num
  have hpTop : ENNReal.ofReal (11 / 3 : ℝ) ≠ ⊤ := by simp
  have hpW : MemLp (powWeight 3) (ENNReal.ofReal (11 / 3 : ℝ)) volume :=
    memLp_powWeight (by norm_num) (by norm_num) (Or.inr (by norm_num))
  have hHess : MemLp (fun y : Space =>
      spatialTestDerivative j (spatialTestDerivative i (lerayPotential f)) y)
      (ENNReal.ofReal (11 / 3 : ℝ)) volume := by
    have hmajor : MemLp (M • powWeight 3) (ENNReal.ofReal (11 / 3 : ℝ)) volume :=
      hpW.const_smul M
    have hmeas : AEStronglyMeasurable
        (fun y : Space => spatialTestDerivative j
          (spatialTestDerivative i (lerayPotential f)) y) volume :=
      ((UnforcedLeray.PressureAnalysis.contDiff_spatialTestDerivative
        (UnforcedLeray.PressureAnalysis.contDiff_spatialTestDerivative hψsmooth i) j).continuous
        ).aestronglyMeasurable
    refine hmajor.of_le hmeas ?_
    filter_upwards [] with y
    have hcomm := UnforcedLeray.Blueprint.L14.spatialTestDerivative_comm_of_contDiff
      hψsmooth i j y
    rw [Real.norm_eq_abs]
    calc
      |spatialTestDerivative j (spatialTestDerivative i (lerayPotential f)) y| =
        |spatialTestDerivative i (spatialTestDerivative j (lerayPotential f)) y| := by
          exact congrArg abs hcomm.symm
      _ ≤
        M * powWeight 3 y := hM i j y
      _ = ‖M • powWeight 3 y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hM0,
          Real.norm_of_nonneg (powWeight_nonneg 3 y)]
  have hDf : MemLp (spatialTestDerivative j (f i))
      (ENNReal.ofReal (11 / 3 : ℝ)) volume := (hf i).derivative j |>.memLp _
  rw [hderiv]
  exact hDf.add hHess

#print axioms memLp_projectedTestNewtonCurl_spatialDerivative_q11third

end UnforcedLeray.Cons.C03.Concrete

end
