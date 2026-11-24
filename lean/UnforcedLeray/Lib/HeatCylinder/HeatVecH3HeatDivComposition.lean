import UnforcedLeray.Lib.HeatCylinder.HeatDivCompositionL2
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator

/-!
# Ordinary H³ heat after the actual positive-age heat-divergence response

The H³ identity is determined by its actual normalized L² value. The scalar heat / tensor
heat-divergence covariance is the concrete Gaussian result in `HeatDivCompositionL2`; vector
coordinates are changed only through the genuine Train `Plane` equivalence.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

private theorem compLpL_comp_local {E F G H : Type*} [MeasurableSpace E] {μ : Measure E}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : G →L[ℝ] H) (N : F →L[ℝ] G) (x : Lp F p μ) :
    (L.comp N).compLpL p μ x = L.compLpL p μ (N.compLpL p μ x) := by
  apply Lp.ext
  have h1 := (L.comp N).coeFn_compLpL (p := p) (μ := μ) x
  have h2 := L.coeFn_compLpL (p := p) (μ := μ) (N.compLpL p μ x)
  have h3 := N.coeFn_compLpL (p := p) (μ := μ) x
  filter_upwards [h1, h2, h3] with z h1 h2 h3
  rw [h1, h2, h3]
  rfl

private theorem compLpL_id_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Plane} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    (ContinuousLinearMap.id ℝ E).compLpL p μ =
      ContinuousLinearMap.id ℝ (Lp E p μ) := by
  ext x
  have h := (ContinuousLinearMap.id ℝ E).coeFn_compLpL (p := p) (μ := μ) x
  filter_upwards [h] with z hz
  simpa using hz

private theorem heatVecL2CLM_comp_heatDivVecL2CLM {c α β : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hβ : 0 < β)
    (x : Lp (Plane × Plane) 2 (cellMeasure c)) :
    heatVecL2CLM hc α (heatDivVecL2CLM hc hβ x) =
      heatDivVecL2CLM hc (add_pos hα hβ) x := by
  let A : Lp Plane 2 (cellMeasure c) →L[ℝ] Lp Vec 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)
  let C : Lp Vec 2 (cellMeasure c) →L[ℝ] Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c)
  have hCA : C.comp A = ContinuousLinearMap.id ℝ (Lp Plane 2 (cellMeasure c)) := by
    change ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2
        (cellMeasure c)).comp
      ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec).compLpL 2 (cellMeasure c)) = _
    letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    apply ContinuousLinearMap.ext
    intro y
    rw [ContinuousLinearMap.comp_apply, ← compLpL_comp_local
      (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane)
      (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec) y]
    have hcoord : ((UnforcedLeray.Train.toVecL.symm : Vec ≃L[ℝ] Plane).toContinuousLinearMap).comp
        (UnforcedLeray.Train.toVecL : Plane →L[ℝ] Vec) =
          ContinuousLinearMap.id ℝ Plane :=
      ContinuousLinearMap.ext (fun z => UnforcedLeray.Train.toVecL.symm_apply_apply z)
    rw [hcoord, compLpL_id_local]
  calc
    heatVecL2CLM hc α (heatDivVecL2CLM hc hβ x) =
        A (heatL2CLM hc α (C (A (heatDivL2CLM hc hβ x)))) := by
          rw [heatVecL2CLM_apply, heatDivVecL2CLM_apply]
    _ = A (heatL2CLM hc α (heatDivL2CLM hc hβ x)) := by
          have hcancel : C (A (heatDivL2CLM hc hβ x)) =
              heatDivL2CLM hc hβ x := by
            have h := congrArg (fun L : Lp Plane 2 (cellMeasure c) →L[ℝ]
                Lp Plane 2 (cellMeasure c) => L (heatDivL2CLM hc hβ x)) hCA
            simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
          exact congrArg (fun y => A (heatL2CLM hc α y)) hcancel
    _ = A (heatDivL2CLM hc (add_pos hα hβ) x) := by
          exact congrArg A (heatL2CLM_comp_heatDivL2CLM hc hα hβ x)
    _ = heatDivVecL2CLM hc (add_pos hα hβ) x := rfl

/-- Actual ordinary H³ heat after the actual positive-divergence H³ response is the same actual
positive-divergence response at the summed heat age. The proof uses the normalized L² value
characterization and its proved injectivity, so the identity is for the genuine H³ classes. -/
theorem actualHeatVecH3_comp_actualHeatDivH3 {c α β : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hβ : 0 < β)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    actualHeatVecH3 hc hα (actualHeatDivH3 hc hβ x) =
      actualHeatDivH3 hc (add_pos hα hβ) x := by
  apply vectorH3NormalizedValue_injective hc
  rw [vectorH3NormalizedValue_actualHeatVecH3 hc hα,
    vectorH3NormalizedValue_actualHeatDivH3 hc hβ,
    vectorH3NormalizedValue_actualHeatDivH3 hc (add_pos hα hβ)]
  change heatVecL2CLM hc α
      (heatDivVecL2CLM hc hβ (tensorH3KernelInput hc x)) =
    heatDivVecL2CLM hc (add_pos hα hβ) (tensorH3KernelInput hc x)
  exact heatVecL2CLM_comp_heatDivVecL2CLM hc hα hβ (tensorH3KernelInput hc x)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.actualHeatVecH3_comp_actualHeatDivH3
