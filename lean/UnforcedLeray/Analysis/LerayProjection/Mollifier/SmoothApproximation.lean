import UnforcedLeray.Analysis.LerayProjection.Mollifier.H1
import UnforcedLeray.Analysis.LerayProjection.Mollifier.Representative

/-!
# Actual smooth approximation in the weak H¹ graph

The H¹-valued averages are represented by the ordinary smooth compact-kernel
convolution of the field, with each weak derivative represented by convolution
of that derivative. The resulting concrete sequence converges in the full H¹
norm. The smooth approximants are not claimed to have compact spatial support.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
open UnforcedLeray.SobolevGraph

namespace UnforcedLeray.Leray

/-- The field component of H¹ averaging is represented by actual smooth convolution. -/
theorem coeFn_value_h1MollifierAverage (φ : ContDiffBump (0 : Space)) (F : H1) :
    ((h1MollifierAverage φ F).value : SpatialField) =ᵐ[volume]
      SobolevEmbedding.mollification φ (F.value : SpatialField) := by
  rw [value_h1MollifierAverage]
  exact coeFn_mollifierAverage φ F.value

/-- All three weak derivatives are represented by the corresponding actual convolutions. -/
theorem coeFn_derivative_h1MollifierAverage (φ : ContDiffBump (0 : Space))
    (F : H1) (i : Fin 3) :
    ((h1MollifierAverage φ F).derivative i : SpatialField) =ᵐ[volume]
      SobolevEmbedding.mollification φ (F.derivative i : SpatialField) := by
  rw [derivative_h1MollifierAverage]
  exact coeFn_mollifierAverage φ (F.derivative i)

/-- Every one of these H¹ graph elements has a genuine infinitely smooth representative. -/
theorem h1MollifierAverage_has_smooth_representative
    (φ : ContDiffBump (0 : Space)) (F : H1) :
    ∃ f : SpatialField, ContDiff ℝ ∞ f ∧
      ((h1MollifierAverage φ F).value : SpatialField) =ᵐ[volume] f :=
  ⟨SobolevEmbedding.mollification φ (F.value : SpatialField),
    SobolevEmbedding.mollification_smooth φ (F.value : SpatialField) (Lp.memLp F.value),
    coeFn_value_h1MollifierAverage φ F⟩

/-- Actual smooth fields are dense in the concrete full H¹ graph norm. -/
theorem exists_smooth_H1_approximation (F : H1) :
    ∃ A : ℕ → H1, Tendsto A atTop (𝓝 F) ∧
      ∀ n, ∃ f : SpatialField, ContDiff ℝ ∞ f ∧ (A n).value =ᵐ[volume] f := by
  refine ⟨fun n => h1MollifierAverage (SobolevEmbedding.shrinkingMollifier n) F,
    h1MollifierAverage_tendsto F, ?_⟩
  intro n
  exact h1MollifierAverage_has_smooth_representative _ F

end UnforcedLeray.Leray
