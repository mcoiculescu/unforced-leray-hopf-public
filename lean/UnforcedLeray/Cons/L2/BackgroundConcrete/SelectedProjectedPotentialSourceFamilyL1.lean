import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialSourceCellL1
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialSource
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductBounds

set_option autoImplicit false

noncomputable section

open MeasureTheory
open Set
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp

private theorem fderiv_scalarSlice_eq {F : SpaceTime → ℝ} (hF : ContDiff ℝ ∞ F)
    (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun x : Space => F (τ, x)) y v =
      fderiv ℝ F (τ, y) (0, v) := by
  have hFdiff : Differentiable ℝ F := hF.differentiable (by simp)
  have hmap : HasFDerivAt (fun x : Space => (τ, x))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hFdiff (τ, y)).hasFDerivAt.comp y hmap
  have h := congrArg (fun A : Space →L[ℝ] ℝ => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using h

/-- The spatial derivative of an actual real component source has a uniform phase-cell L¹ bound. -/
theorem exists_uniform_spatialL1_projectedPotentialReDerivative {P : ℝ} [Fact (0 < P)]
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) (i j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P,
      ∫ y, |spatialTestDerivative j (fun x => projectedPotentialReTest Φ τ i x) y| ≤ C := by
  let F : SpaceTime → ℝ := projectedPotentialReCoord Φ i
  let D : SpaceTime → ℝ := fun z => fderiv ℝ F z (0, coordinateVector j)
  have hF : IsPhaseTest P F := hΦ.clm_comp (projectedPotentialReCoordCLM i)
  have hD : IsPhaseTest P D := hF.fderiv_apply (0, coordinateVector j)
  obtain ⟨C, hC0, hC⟩ := exists_uniform_spatialL1_of_isPhaseTest hD
  refine ⟨C, hC0, ?_⟩
  intro τ hτ
  have heq (y : Space) : D (τ, y) =
      spatialTestDerivative j (fun x => projectedPotentialReTest Φ τ i x) y := by
    change fderiv ℝ F (τ, y) (0, coordinateVector j) =
      fderiv ℝ (fun x => F (τ, x)) y (coordinateVector j)
    exact (fderiv_scalarSlice_eq hF.smooth τ y (coordinateVector j)).symm
  have hInt := hC τ hτ
  rw [show (fun y => |D (τ, y)|) =
      (fun y => |spatialTestDerivative j
        (fun x => projectedPotentialReTest Φ τ i x) y|) by
        funext y
        rw [heq]] at hInt
  exact hInt

/-- Imaginary component derivative source bound, with the same actual phase support. -/
theorem exists_uniform_spatialL1_projectedPotentialImDerivative {P : ℝ} [Fact (0 < P)]
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) (i j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P,
      ∫ y, |spatialTestDerivative j (fun x => projectedPotentialImTest Φ τ i x) y| ≤ C := by
  let F : SpaceTime → ℝ := projectedPotentialImCoord Φ i
  let D : SpaceTime → ℝ := fun z => fderiv ℝ F z (0, coordinateVector j)
  have hF : IsPhaseTest P F := hΦ.clm_comp (projectedPotentialImCoordCLM i)
  have hD : IsPhaseTest P D := hF.fderiv_apply (0, coordinateVector j)
  obtain ⟨C, hC0, hC⟩ := exists_uniform_spatialL1_of_isPhaseTest hD
  refine ⟨C, hC0, ?_⟩
  intro τ hτ
  have heq (y : Space) : D (τ, y) =
      spatialTestDerivative j (fun x => projectedPotentialImTest Φ τ i x) y := by
    change fderiv ℝ F (τ, y) (0, coordinateVector j) =
      fderiv ℝ (fun x => F (τ, x)) y (coordinateVector j)
    exact (fderiv_scalarSlice_eq hF.smooth τ y (coordinateVector j)).symm
  have hInt := hC τ hτ
  rw [show (fun y => |D (τ, y)|) =
      (fun y => |spatialTestDerivative j
        (fun x => projectedPotentialImTest Φ τ i x) y|) by
        funext y
        rw [heq]] at hInt
  exact hInt

/-- The actual real divergence source has a uniform spatial L¹ bound on a compact phase cell. -/
theorem exists_uniform_spatialL1_projectedPotentialReDiv {P : ℝ} [Fact (0 < P)]
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P,
      ∫ y, |projectedPotentialReDiv Φ (τ, y)| ≤ C :=
  exists_uniform_spatialL1_of_isPhaseTest (isPhaseTest_projectedPotentialReDiv hΦ)

/-- The actual imaginary divergence source has a uniform spatial L¹ bound on a compact phase
cell. -/
theorem exists_uniform_spatialL1_projectedPotentialImDiv {P : ℝ} [Fact (0 < P)]
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P,
      ∫ y, |projectedPotentialImDiv Φ (τ, y)| ≤ C :=
  exists_uniform_spatialL1_of_isPhaseTest (isPhaseTest_projectedPotentialImDiv hΦ)

#print axioms exists_uniform_spatialL1_projectedPotentialReDerivative
#print axioms exists_uniform_spatialL1_projectedPotentialImDerivative
#print axioms exists_uniform_spatialL1_projectedPotentialReDiv
#print axioms exists_uniform_spatialL1_projectedPotentialImDiv

end UnforcedLeray.Cons.C03.Concrete

end
