import UnforcedLeray.Lib.HeatCylinder.HeatVecL2

/-!
# The actual zero-order vector heat semigroup

The vector family is the B0284 Gaussian heat conjugated by Train's genuine coordinate
isomorphism. This leaf records its identity convention and its semigroup law.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.HeatCylinder

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

/-- At nonpositive ages the actual normalized-cell Plane heat operator is the identity. -/
theorem heatL2CLM_eq_id_of_nonpos {c θ : ℝ} (hc : 0 < c) (hθ : θ ≤ 0) :
    heatL2CLM hc θ = ContinuousLinearMap.id ℝ (Lp Plane 2 (cellMeasure c)) := by
  ext x
  rw [heatL2CLM_apply, heatL2_eq_id_of_nonpos hc hθ]
  rfl

private theorem compLpL_comp {E F G : Type*} [MeasurableSpace E] {μ : Measure E}
    {p : ℝ≥0∞} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [Fact (1 ≤ p)]
    (L : G →L[ℝ] H) (N : F →L[ℝ] G) (x : Lp F p μ) :
    (L.comp N).compLpL p μ x = L.compLpL p μ (N.compLpL p μ x) := by
  apply Lp.ext
  have h1 := (L.comp N).coeFn_compLpL (p := p) (μ := μ) x
  have h2 := L.coeFn_compLpL (p := p) (μ := μ) (N.compLpL p μ x)
  have h3 := N.coeFn_compLpL (p := p) (μ := μ) x
  filter_upwards [h1, h2, h3] with z h1 h2 h3
  rw [h1, h2, h3]
  rfl

private theorem compLpL_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Plane} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (ContinuousLinearMap.id ℝ E).compLpL p μ =
      ContinuousLinearMap.id ℝ (Lp E p μ) := by
  ext x
  have h := (ContinuousLinearMap.id ℝ E).coeFn_compLpL (p := p) (μ := μ) x
  filter_upwards [h] with z hz
  simpa using hz

private theorem heatVecCoordinateMaps_left_inv {c : ℝ} :
    ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)).comp
      ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c)) =
        ContinuousLinearMap.id ℝ (Lp Vec 2 (cellMeasure c)) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, ← compLpL_comp
    (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec)
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane) x]
  have hcoord : (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).comp
      ((UnforcedLeray.Train.toVecL.symm : Vec ≃L[ℝ] Plane).toContinuousLinearMap) =
        ContinuousLinearMap.id ℝ Vec :=
    ContinuousLinearMap.ext (fun z => UnforcedLeray.Train.toVecL.apply_symm_apply z)
  rw [hcoord, compLpL_id]

private theorem heatVecCoordinateMaps_right_inv {c : ℝ} :
    ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c)).comp
      ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)) =
        ContinuousLinearMap.id ℝ (Lp Plane 2 (cellMeasure c)) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, ← compLpL_comp
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane)
    (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec) x]
  have hcoord : ((UnforcedLeray.Train.toVecL.symm : Vec ≃L[ℝ] Plane).toContinuousLinearMap).comp
      (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec) = ContinuousLinearMap.id ℝ Plane :=
    ContinuousLinearMap.ext (fun z => UnforcedLeray.Train.toVecL.symm_apply_apply z)
  rw [hcoord, compLpL_id]

/-- At every nonpositive age the actual vector heat operator is the identity. -/
theorem heatVecL2CLM_eq_id_of_nonpos {c θ : ℝ} (hc : 0 < c) (hθ : θ ≤ 0) :
    heatVecL2CLM hc θ = ContinuousLinearMap.id ℝ (Lp Vec 2 (cellMeasure c)) := by
  unfold heatVecL2CLM
  rw [heatL2CLM_eq_id_of_nonpos hc hθ, ContinuousLinearMap.id_comp]
  exact heatVecCoordinateMaps_left_inv

/-- The actual zero-order vector heat has the semigroup law at nonnegative ages. -/
theorem heatVecL2CLM_comp_of_nonneg {c α β : ℝ} (hc : 0 < c)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (heatVecL2CLM hc α).comp (heatVecL2CLM hc β) = heatVecL2CLM hc (α + β) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let A : Lp Plane 2 (cellMeasure c) →L[ℝ] Lp Vec 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)
  let C : Lp Vec 2 (cellMeasure c) →L[ℝ] Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c)
  have hCA : C.comp A = ContinuousLinearMap.id ℝ _ := by
    simpa [A, C] using heatVecCoordinateMaps_right_inv (c := c)
  have hH := heatL2CLM_comp_of_nonneg hc hα hβ
  change (A.comp ((heatL2CLM hc α).comp C)).comp
      (A.comp ((heatL2CLM hc β).comp C)) =
    A.comp ((heatL2CLM hc (α + β)).comp C)
  calc
    _ = A.comp (((heatL2CLM hc α).comp (C.comp A)).comp
          ((heatL2CLM hc β).comp C)) := by
        ext x
        rfl
    _ = A.comp (((heatL2CLM hc α).comp (heatL2CLM hc β)).comp C) := by
        ext x
        simp only [ContinuousLinearMap.comp_apply, hCA, ContinuousLinearMap.id_apply]
        rfl
    _ = A.comp ((heatL2CLM hc (α + β)).comp C) := by rw [hH]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatL2CLM_eq_id_of_nonpos
#print axioms UnforcedLeray.HeatCylinder.heatVecL2CLM_eq_id_of_nonpos
#print axioms UnforcedLeray.HeatCylinder.heatVecL2CLM_comp_of_nonneg
