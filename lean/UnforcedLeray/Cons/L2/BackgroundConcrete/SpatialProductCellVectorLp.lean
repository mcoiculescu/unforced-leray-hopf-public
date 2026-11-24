import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellLpBridge
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellHolder

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace

/-- The actual squared-cutoff slice gradient of `Φ·U` has the dual phase-cell Lp norm needed to
pair it with the correction. The scalar components are transported through the genuine coordinate
continuous-linear maps into `CVec3`. -/
theorem memLp_cutoffSquared_scalarSliceGrad_cell {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (n : ℕ) :
    MemLp (fun z : SpaceTime =>
      (phaseInteriorCutoff P n z.1) ^ 2 • scalarSliceGrad (scalarTestBackground Φ U) z)
      p (volume.restrict (phaseCell P)) := by
  let g : Fin 3 → SpaceTime → ℂ := fun j z =>
    (phaseInteriorCutoff P n z.1) ^ 2 •
      fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
        (EuclideanSpace.single j (1 : ℝ))
  have hterm (j : Fin 3) : MemLp (fun z : SpaceTime =>
      g j z • EuclideanSpace.single j (1 : ℂ))
      p (volume.restrict (phaseCell P)) := by
    let A : ℂ →L[ℝ] CVec3 :=
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℝ] ℂ)
        (EuclideanSpace.single j (1 : ℂ))
    have hg := memLp_cutoffSquared_scalarTestBackground_spatialDerivative_cell
      hΦ hU hp n j
    have hA := hg.continuousLinearMap_comp A
    have heq : (fun z : SpaceTime => g j z • EuclideanSpace.single j (1 : ℂ)) =ᵐ[
        volume.restrict (phaseCell P)] (fun z => A (g j z)) :=
      Eventually.of_forall fun _ => rfl
    exact (memLp_congr_ae heq).mpr hA
  have hsum := memLp_finsetSum' Finset.univ (fun j _ => hterm j)
  have heq : (fun z : SpaceTime =>
      (phaseInteriorCutoff P n z.1) ^ 2 • scalarSliceGrad (scalarTestBackground Φ U) z) =ᵐ[
        volume.restrict (phaseCell P)]
      (fun z => ∑ j : Fin 3, g j z • EuclideanSpace.single j (1 : ℂ)) := by
    filter_upwards with z
    change (phaseInteriorCutoff P n z.1) ^ 2 •
      (∑ j : Fin 3,
        (fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))) • EuclideanSpace.single j (1 : ℂ)) = _
    rw [Finset.smul_sum]
    simp only [g]
    apply Finset.sum_congr rfl
    intro j hj
    ext i
    simp [Complex.real_smul, smul_eq_mul]
  exact (memLp_congr_ae heq).mpr hsum

#print axioms memLp_cutoffSquared_scalarSliceGrad_cell

end UnforcedLeray.Cons.C03.Concrete
