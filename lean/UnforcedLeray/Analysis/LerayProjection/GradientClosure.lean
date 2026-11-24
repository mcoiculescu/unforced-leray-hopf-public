import UnforcedLeray.Analysis.LerayProjection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The closed gradient subspace complementary to solenoidal L² fields

The orthogonal complement of the actual distributionally solenoidal L² subspace
is exactly the L² closure of the linear span of compact smooth scalar-test
gradients. Consequently the Leray projection vanishes precisely on that closed
subspace, and its removed component belongs to it.

This is a Hilbert-space closure characterization. No approximation statement for
an independently specified pressure field or Fourier multiplier is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Leray

/-- The linear span in vector-valued L² of actual compact smooth scalar-test gradients. -/
def gradientSpan : Submodule ℝ L2Space :=
  Submodule.span ℝ (Set.range fun φ : SpatialTest => testGradient φ.1 φ.2)

/-- The strong L² closure of the compact-test gradient span. -/
def gradientClosure : Submodule ℝ L2Space := gradientSpan.topologicalClosure

theorem testGradient_mem_gradientSpan (φ : Space → ℝ) (hφ : IsSpatialTest φ) :
    testGradient φ hφ ∈ gradientSpan :=
  Submodule.subset_span ⟨⟨φ, hφ⟩, rfl⟩

theorem gradientSpan_le_orthogonal : gradientSpan ≤ solenoidalSubspaceᗮ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨φ, rfl⟩
  exact testGradient_mem_orthogonal φ.1 φ.2

/-- Orthogonality to the gradient span is exactly the concrete weak divergence constraint. -/
theorem gradientSpan_orthogonal_eq_solenoidalSubspace :
    gradientSpanᗮ = solenoidalSubspace := by
  apply le_antisymm
  · intro F hF
    apply (mem_solenoidalSubspace_iff F).mpr
    refine ⟨fun φ hφ => gradient_pairing_integrable φ hφ F, ?_⟩
    intro φ hφ
    rw [← testGradient_inner φ hφ F]
    exact hF (testGradient φ hφ) (testGradient_mem_gradientSpan φ hφ)
  · intro F hF G hG
    exact Submodule.inner_left_of_mem_orthogonal hF (gradientSpan_le_orthogonal hG)

/-- The complete-space double-orthogonal theorem identifies the entire complement. -/
theorem solenoidalSubspace_orthogonal_eq_gradientClosure :
    solenoidalSubspaceᗮ = gradientClosure := by
  rw [← gradientSpan_orthogonal_eq_solenoidalSubspace,
    Submodule.orthogonal_orthogonal_eq_closure]
  rfl

theorem gradientClosure_orthogonal_eq_solenoidalSubspace :
    gradientClosureᗮ = solenoidalSubspace := by
  rw [gradientClosure, Submodule.orthogonal_closure,
    gradientSpan_orthogonal_eq_solenoidalSubspace]

theorem isClosed_gradientClosure : IsClosed (gradientClosure : Set L2Space) :=
  gradientSpan.isClosed_topologicalClosure

theorem testGradient_mem_gradientClosure (φ : Space → ℝ) (hφ : IsSpatialTest φ) :
    testGradient φ hφ ∈ gradientClosure :=
  gradientSpan.le_topologicalClosure (testGradient_mem_gradientSpan φ hφ)

/-- The kernel of the Leray projection is exactly the closed compact-test gradient span. -/
theorem projection_eq_zero_iff_mem_gradientClosure (F : L2Space) :
    projection F = 0 ↔ F ∈ gradientClosure := by
  change solenoidalSubspace.starProjection F = 0 ↔ F ∈ gradientClosure
  rw [Submodule.starProjection_apply_eq_zero_iff,
    solenoidalSubspace_orthogonal_eq_gradientClosure]

/-- The Leray projection annihilates every L² limit of vectors in the gradient span. -/
theorem projection_of_mem_gradientClosure {F : L2Space} (hF : F ∈ gradientClosure) :
    projection F = 0 := (projection_eq_zero_iff_mem_gradientClosure F).mpr hF

/-- The part removed by the Leray projection belongs to the closed gradient span. -/
theorem residual_mem_gradientClosure (F : L2Space) :
    F - projection F ∈ gradientClosure := by
  rw [← solenoidalSubspace_orthogonal_eq_gradientClosure]
  exact residual_mem_orthogonal F

end UnforcedLeray.Leray
