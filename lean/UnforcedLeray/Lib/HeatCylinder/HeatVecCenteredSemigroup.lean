import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianAverageIdentification
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2Semigroup
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2NormalizedCenteredInverse

/-!
# Semigroup law for the actual centered-cell vector heat

The centered-cell semigroup is the conjugate of the already-proved actual B0284 normalized-cell
semigroup under the inverse periodic quotient maps. The factor `sqrt c` cancels because these
maps are genuine inverses, not isometries.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (L2v)
open UnforcedLeray.B0284 (cellMeasure)

private theorem normalizedToCentered_comp_centeredToNormalized_local {c : ℝ}
    (hc : 0 < c) :
    (normalizedVecToCenteredCLM hc).comp (centeredVecToNormalizedCLM hc) =
      ContinuousLinearMap.id ℝ (L2v c) := by
  apply ContinuousLinearMap.ext
  intro x
  change normalizedVecToCenteredLinear hc (centeredVecToNormalizedLinear hc x) = x
  exact normalizedVecToCenteredLinear_centeredVecToNormalizedLinear hc x

private theorem centeredToNormalized_comp_normalizedToCentered_local {c : ℝ}
    (hc : 0 < c) :
    (centeredVecToNormalizedCLM hc).comp (normalizedVecToCenteredCLM hc) =
      ContinuousLinearMap.id ℝ (Lp Vec 2 (cellMeasure c)) := by
  apply ContinuousLinearMap.ext
  intro x
  change centeredVecToNormalizedLinear hc (centeredVecOfNormalizedVec hc x) = x
  exact centeredVecToNormalizedLinear_centeredVecOfNormalizedVec hc x

private theorem normalizedToCentered_centeredToNormalized_apply_local {c : ℝ}
    (hc : 0 < c) (x : L2v c) :
    normalizedVecToCenteredCLM hc (centeredVecToNormalizedCLM hc x) = x := by
  have h := congrArg (fun A => A x)
    (normalizedToCentered_comp_centeredToNormalized_local hc)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

private theorem centeredToNormalized_normalizedToCentered_apply_local {c : ℝ}
    (hc : 0 < c) (x : Lp Vec 2 (cellMeasure c)) :
    centeredVecToNormalizedCLM hc (normalizedVecToCenteredCLM hc x) = x := by
  have h := congrArg (fun A => A x)
    (centeredToNormalized_comp_normalizedToCentered_local hc)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

/-- At nonpositive ages the actual centered-cell vector heat is the identity. -/
theorem centeredHeatVecL2CLM_eq_id_of_nonpos {c θ : ℝ} (hc : 0 < c)
    (hθ : θ ≤ 0) :
    centeredHeatVecL2CLM hc θ = ContinuousLinearMap.id ℝ (L2v c) := by
  apply ContinuousLinearMap.ext
  intro x
  change normalizedVecToCenteredCLM hc
    (heatVecL2CLM hc θ (centeredVecToNormalizedCLM hc x)) = x
  rw [heatVecL2CLM_eq_id_of_nonpos hc hθ]
  exact normalizedToCentered_centeredToNormalized_apply_local hc x

/-- The actual centered-cell vector heat has the semigroup law at nonnegative ages. -/
theorem centeredHeatVecL2CLM_comp_of_nonneg {c α β : ℝ} (hc : 0 < c)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (centeredHeatVecL2CLM hc α).comp (centeredHeatVecL2CLM hc β) =
      centeredHeatVecL2CLM hc (α + β) := by
  apply ContinuousLinearMap.ext
  intro x
  change normalizedVecToCenteredCLM hc
      (heatVecL2CLM hc α (centeredVecToNormalizedCLM hc
        (normalizedVecToCenteredCLM hc
          (heatVecL2CLM hc β (centeredVecToNormalizedCLM hc x))))) =
    normalizedVecToCenteredCLM hc
      (heatVecL2CLM hc (α + β) (centeredVecToNormalizedCLM hc x))
  rw [centeredToNormalized_normalizedToCentered_apply_local hc]
  have hsemigroup := congrArg (fun A => A (centeredVecToNormalizedCLM hc x))
    (heatVecL2CLM_comp_of_nonneg hc hα hβ)
  simpa only [ContinuousLinearMap.comp_apply] using congrArg (normalizedVecToCenteredCLM hc) hsemigroup

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.centeredHeatVecL2CLM_eq_id_of_nonpos
#print axioms UnforcedLeray.HeatCylinder.centeredHeatVecL2CLM_comp_of_nonneg
