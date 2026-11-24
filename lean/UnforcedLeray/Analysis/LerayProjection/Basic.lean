import UnforcedLeray.Analysis.LerayProjection.Tests
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# The L² Leray projection on actual solenoidal fields on R³

The divergence-free subspace is the intersection of kernels of the continuous
pairings against compact smooth test gradients. Membership is equivalent to
`IsSolenoidal` from the target statement, including its integrability guards.
The Hilbert orthogonal projection therefore gives a genuine contractive L²
Leray projection. It annihilates each compact smooth gradient. Identification
with a Fourier multiplier, bounds on other Sobolev spaces, and pressure
reconstruction are separate results, not hypotheses or conclusions here.
-/

set_option autoImplicit false

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace UnforcedLeray.Leray

abbrev SpatialTest := {φ : Space → ℝ // IsSpatialTest φ}

/-- The continuous divergence test functional on vector-valued L²(R³). -/
def divergenceFunctional (φ : SpatialTest) : L2Space →L[ℝ] ℝ :=
  innerSL ℝ (testGradient φ.1 φ.2)

theorem divergenceFunctional_apply (φ : SpatialTest) (F : L2Space) :
    divergenceFunctional φ F =
      ∫ x : Space, ∑ i : Fin 3, (F x) i * spatialTestDerivative i φ.1 x := by
  exact testGradient_inner φ.1 φ.2 F

/-- Distributionally solenoidal L² classes, defined by the actual test kernels. -/
def solenoidalSubspace : Submodule ℝ L2Space :=
  ⨅ φ : SpatialTest, LinearMap.ker (divergenceFunctional φ : L2Space →ₗ[ℝ] ℝ)

/-- Kernel membership is precisely the target statement's solenoidal predicate. -/
theorem mem_solenoidalSubspace_iff (F : L2Space) :
    F ∈ solenoidalSubspace ↔ IsSolenoidal (F : SpatialField) := by
  simp only [solenoidalSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, divergenceFunctional_apply]
  constructor
  · intro h
    exact ⟨fun φ hφ => gradient_pairing_integrable φ hφ F, fun φ hφ => h ⟨φ, hφ⟩⟩
  · intro h φ
    exact h.identity φ.1 φ.2

/-- The actual weak divergence constraint is closed in strong L². -/
theorem isClosed_solenoidalSubspace : IsClosed (solenoidalSubspace : Set L2Space) := by
  rw [solenoidalSubspace, Submodule.coe_iInf]
  exact isClosed_iInter fun φ => (divergenceFunctional φ).isClosed_ker

/-- The divergence-free L² subspace is itself a complete Hilbert space. -/
instance solenoidalSubspace_completeSpace : CompleteSpace solenoidalSubspace :=
  isClosed_solenoidalSubspace.completeSpace_coe

abbrev SolenoidalL2 := solenoidalSubspace

/-- The weak divergence condition is invariant under a.e. modification. -/
theorem solenoidal_congr_ae {f g : SpatialField}
    (h : IsSolenoidal f) (hfg : f =ᵐ[volume] g) : IsSolenoidal g := by
  have he (φ : Space → ℝ) :
      (fun x => ∑ i : Fin 3, (f x) i * spatialTestDerivative i φ x) =ᵐ[volume]
      (fun x => ∑ i : Fin 3, (g x) i * spatialTestDerivative i φ x) := by
    filter_upwards [hfg] with x hx
    rw [hx]
  refine ⟨fun φ hφ => (h.integrable φ hφ).congr (he φ), ?_⟩
  intro φ hφ
  rw [← integral_congr_ae (he φ)]
  exact h.identity φ hφ

/-- The L² quotient construction preserves exactly the concrete constraint. -/
theorem mem_solenoidalSubspace_toL2_iff {f : SpatialField} (hf : MemLp f 2 volume) :
    toL2 f ∈ solenoidalSubspace ↔ IsSolenoidal f := by
  rw [mem_solenoidalSubspace_iff]
  exact ⟨fun h => solenoidal_congr_ae h (coeFn_toL2 hf),
    fun h => solenoidal_congr_ae h (coeFn_toL2 hf).symm⟩

/-- Solenoidality passes to strong L² limits without a separate closure assumption. -/
theorem solenoidal_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → L2Space} {F₀ : L2Space}
    (h : ∀ j, IsSolenoidal (F j : SpatialField)) (hF : Tendsto F l (𝓝 F₀)) :
    IsSolenoidal (F₀ : SpatialField) := by
  exact (mem_solenoidalSubspace_iff F₀).mp
    (isClosed_solenoidalSubspace.mem_of_tendsto hF
      (Eventually.of_forall fun j => (mem_solenoidalSubspace_iff (F j)).mpr (h j)))

/-- The orthogonal Leray projection on L²(R³;R³). -/
def projection : L2Space →L[ℝ] L2Space := solenoidalSubspace.starProjection

theorem projection_mem (F : L2Space) : projection F ∈ solenoidalSubspace :=
  solenoidalSubspace.starProjection_apply_mem F

theorem projection_solenoidal (F : L2Space) : IsSolenoidal (projection F : SpatialField) :=
  (mem_solenoidalSubspace_iff _).mp (projection_mem F)

theorem norm_projection_le : ‖projection‖ ≤ 1 := solenoidalSubspace.starProjection_norm_le

theorem norm_projection_apply_le (F : L2Space) : ‖projection F‖ ≤ ‖F‖ :=
  solenoidalSubspace.norm_starProjection_apply_le F

theorem projection_eq_self_iff (F : L2Space) :
    projection F = F ↔ IsSolenoidal (F : SpatialField) := by
  exact solenoidalSubspace.starProjection_eq_self_iff.trans (mem_solenoidalSubspace_iff F)

theorem projection_eq_self {F : L2Space} (h : IsSolenoidal (F : SpatialField)) :
    projection F = F := (projection_eq_self_iff F).mpr h

@[simp] theorem projection_idempotent (F : L2Space) : projection (projection F) = projection F :=
  projection_eq_self (projection_solenoidal F)

theorem projection_toL2_eq_self {f : SpatialField} (hf : MemLp f 2 volume)
    (h : IsSolenoidal f) : projection (toL2 f) = toL2 f :=
  solenoidalSubspace.starProjection_eq_self_iff.mpr
    ((mem_solenoidalSubspace_toL2_iff hf).mpr h)

/-- The removed component is orthogonal to every actual solenoidal L² field. -/
theorem residual_mem_orthogonal (F : L2Space) :
    F - projection F ∈ solenoidalSubspaceᗮ :=
  Submodule.sub_starProjection_mem_orthogonal F

theorem projection_selfadjoint (F G : L2Space) :
    inner ℝ (projection F) G = inner ℝ F (projection G) :=
  solenoidalSubspace.inner_starProjection_left_eq_right F G

/-- A solenoidal component with orthogonal residual must be this projection. -/
theorem projection_eq_of_orthogonal {F G : L2Space}
    (hG : IsSolenoidal (G : SpatialField))
    (horth : F - G ∈ solenoidalSubspaceᗮ) : projection F = G :=
  Submodule.eq_starProjection_of_mem_orthogonal
    ((mem_solenoidalSubspace_iff G).mpr hG) horth

/-- Compact smooth gradients are genuinely orthogonal to every solenoidal L² field. -/
theorem testGradient_mem_orthogonal (φ : Space → ℝ) (hφ : IsSpatialTest φ) :
    testGradient φ hφ ∈ solenoidalSubspaceᗮ := by
  intro F hF
  rw [real_inner_comm, testGradient_inner]
  exact ((mem_solenoidalSubspace_iff F).mp hF).identity φ hφ

/-- The L² Leray projection annihilates each actual compact smooth gradient. -/
@[simp] theorem projection_testGradient (φ : Space → ℝ) (hφ : IsSpatialTest φ) :
    projection (testGradient φ hφ) = 0 := by
  have h := Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
    (testGradient_mem_orthogonal φ hφ)
  exact congrArg (fun v : solenoidalSubspace => (v : L2Space)) h

end UnforcedLeray.Leray
