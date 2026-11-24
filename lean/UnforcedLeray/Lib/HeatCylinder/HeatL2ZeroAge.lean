import UnforcedLeray.Lib.HeatCylinder.HeatVecL2ZeroAge

/-!
# Strong continuity at zero for the actual normalized-cell Plane heat

The Euclidean-vector orbit is transferred back through Train's genuine Plane/vector coordinate
isomorphism. The normalized-cell quotient operators are related by the actual `compLpL` maps.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

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

private theorem compLpL_id_heat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Plane} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (ContinuousLinearMap.id ℝ E).compLpL p μ =
      ContinuousLinearMap.id ℝ (Lp E p μ) := by
  ext x
  have h := (ContinuousLinearMap.id ℝ E).coeFn_compLpL (p := p) (μ := μ) x
  filter_upwards [h] with z hz
  simpa using hz

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
  rw [hcoord, compLpL_id_heat]

/-- The actual normalized-cell Plane heat quotient orbit converges strongly to the input at
age zero through positive ages. -/
theorem tendsto_heatL2CLM_apply_zero {c : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (cellMeasure c)) :
    Tendsto (fun θ : ℝ => heatL2CLM hc θ x) (𝓝[>] 0) (𝓝 x) := by
  let A : Lp Plane 2 (cellMeasure c) →L[ℝ] Lp Vec 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)
  let C : Lp Vec 2 (cellMeasure c) →L[ℝ] Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c)
  have hCA : C.comp A = ContinuousLinearMap.id ℝ _ := by
    simpa [A, C] using heatVecCoordinateMaps_right_inv (c := c)
  have hCA_apply (z : Lp Plane 2 (cellMeasure c)) : C (A z) = z := by
    change (C.comp A) z = z
    rw [hCA]
    rfl
  have hVec := tendsto_heatVecL2CLM_apply_zero hc (A x)
  have hCont := (C.continuous.tendsto (A x)).comp hVec
  have hlimit : C (A x) = x := hCA_apply x
  have hCont' : Tendsto (fun θ : ℝ => C (heatVecL2CLM hc θ (A x))) (𝓝[>] 0) (𝓝 x) := by
    change Tendsto (fun θ : ℝ => C (heatVecL2CLM hc θ (A x))) (𝓝[>] 0)
      (𝓝 (C (A x))) at hCont
    simpa only [hlimit] using hCont
  have hOrbit : (fun θ : ℝ => C (heatVecL2CLM hc θ (A x))) =
      fun θ => heatL2CLM hc θ x := by
    funext θ
    have hheat : heatVecL2CLM hc θ (A x) = A (heatL2CLM hc θ x) := by
      rw [heatVecL2CLM_apply]
      change A (heatL2CLM hc θ (C (A x))) = A (heatL2CLM hc θ x)
      rw [hCA_apply]
    rw [hheat]
    exact hCA_apply (heatL2CLM hc θ x)
  rw [← hOrbit]
  exact hCont'

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.tendsto_heatL2CLM_apply_zero
