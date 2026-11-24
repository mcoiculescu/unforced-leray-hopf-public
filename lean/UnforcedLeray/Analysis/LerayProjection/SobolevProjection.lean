import UnforcedLeray.Analysis.LerayProjection.TranslationGenerator
import UnforcedLeray.Analysis.SobolevGraph.H1
import UnforcedLeray.Analysis.SobolevGraph.H2

/-!
# Contractive Leray projection on the actual H¹ and H² Hilbert graphs

The L² projection commutes with concrete distributional derivatives, as proved
from its translation symmetry. It therefore acts on the existing complete
weak-Sobolev graphs by projecting every component. Their exact square-sum norms
give contraction with constant one, including all first and second derivatives.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace UnforcedLeray.Leray
open SobolevGraph

/-- The actual H¹ field whose value and weak derivatives are projected. -/
def h1Project (F : H1) : H1 :=
  H1.ofWeakDerivatives (projection F.value) (fun i => projection (F.derivative i))
    (fun i => weakDerivative_projection F.value (F.derivative i) i (F.hasWeakDerivative i))

@[simp] theorem value_h1Project (F : H1) : (h1Project F).value = projection F.value := rfl
@[simp] theorem derivative_h1Project (F : H1) (i : Fin 3) :
    (h1Project F).derivative i = projection (F.derivative i) := rfl

/-- The genuine H¹ graph norm contracts under Leray projection. -/
theorem norm_h1Project_le (F : H1) : ‖h1Project F‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [H1.norm_sq, value_h1Project, derivative_h1Project]
  gcongr <;> exact norm_projection_apply_le _

private def h1ProjectionLinear : H1 →ₗ[ℝ] H1 where
  toFun := h1Project
  map_add' F G := by
    apply H1.ext
    change projection (H1.valueCLM (F + G)) = H1.valueCLM (h1Project F + h1Project G)
    simp only [map_add, H1.valueCLM_apply, value_h1Project]
  map_smul' c F := by
    apply H1.ext
    change projection (H1.valueCLM (c • F)) = H1.valueCLM (c • h1Project F)
    simp only [map_smul, H1.valueCLM_apply, value_h1Project]

/-- The bounded Leray operator on actual weak H¹(R³;R³). -/
def h1Projection : H1 →L[ℝ] H1 :=
  h1ProjectionLinear.mkContinuous 1 (fun F => by
    change ‖h1Project F‖ ≤ (1 : ℝ) * ‖F‖
    simpa only [one_mul] using norm_h1Project_le F)

@[simp] theorem h1Projection_apply (F : H1) : h1Projection F = h1Project F := rfl
@[simp] theorem value_h1Projection (F : H1) :
    (h1Projection F).value = projection F.value := rfl
@[simp] theorem derivative_h1Projection (F : H1) (i : Fin 3) :
    (h1Projection F).derivative i = projection (F.derivative i) := rfl

theorem norm_h1Projection_le : ‖h1Projection‖ ≤ 1 := by
  apply h1Projection.opNorm_le_bound zero_le_one
  intro F
  simpa using norm_h1Project_le F

@[simp] theorem h1Projection_idempotent (F : H1) :
    h1Projection (h1Projection F) = h1Projection F := by
  apply H1.ext
  simp only [value_h1Projection, projection_idempotent]

theorem h1Projection_solenoidal (F : H1) :
    IsSolenoidal ((h1Projection F).value : SpatialField) :=
  projection_solenoidal F.value

theorem h1Projection_eq_self_iff (F : H1) :
    h1Projection F = F ↔ IsSolenoidal (F.value : SpatialField) := by
  constructor
  · intro h
    exact (projection_eq_self_iff F.value).mp (congrArg H1.value h)
  · intro h
    apply H1.ext
    exact projection_eq_self h

/-- Selfadjointness holds for the full first-order Hilbert graph inner product. -/
theorem h1Projection_selfadjoint (F G : H1) :
    inner ℝ (h1Projection F) G = inner ℝ F (h1Projection G) := by
  simp only [H1.inner_eq, value_h1Projection, derivative_h1Projection, projection_selfadjoint]

/-- The actual H² field, projecting all ordered weak derivatives. -/
def h2Project (F : H2) : H2 :=
  H2.ofWeakDerivatives (projection F.value) (fun i => projection (F.first i))
    (fun i j => projection (F.second i j))
    (fun i => weakDerivative_projection F.value (F.first i) i (F.hasWeakFirst i))
    (fun i j => weakDerivative_projection (F.first i) (F.second i j) j (F.hasWeakSecond i j))

@[simp] theorem value_h2Project (F : H2) : (h2Project F).value = projection F.value := rfl
@[simp] theorem first_h2Project (F : H2) (i : Fin 3) :
    (h2Project F).first i = projection (F.first i) := rfl
@[simp] theorem second_h2Project (F : H2) (i j : Fin 3) :
    (h2Project F).second i j = projection (F.second i j) := rfl

/-- The full concrete H² graph norm contracts with the same constant one. -/
theorem norm_h2Project_le (F : H2) : ‖h2Project F‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [H2.norm_sq, value_h2Project, first_h2Project, second_h2Project]
  gcongr <;> exact norm_projection_apply_le _

private def h2ProjectionLinear : H2 →ₗ[ℝ] H2 where
  toFun := h2Project
  map_add' F G := by
    apply H2.ext
    change projection (H2.valueCLM (F + G)) = H2.valueCLM (h2Project F + h2Project G)
    simp only [map_add, H2.valueCLM_apply, value_h2Project]
  map_smul' c F := by
    apply H2.ext
    change projection (H2.valueCLM (c • F)) = H2.valueCLM (c • h2Project F)
    simp only [map_smul, H2.valueCLM_apply, value_h2Project]

/-- The bounded Leray operator on actual weak H²(R³;R³). -/
def h2Projection : H2 →L[ℝ] H2 :=
  h2ProjectionLinear.mkContinuous 1 (fun F => by
    change ‖h2Project F‖ ≤ (1 : ℝ) * ‖F‖
    simpa only [one_mul] using norm_h2Project_le F)

@[simp] theorem h2Projection_apply (F : H2) : h2Projection F = h2Project F := rfl
@[simp] theorem value_h2Projection (F : H2) :
    (h2Projection F).value = projection F.value := rfl
@[simp] theorem first_h2Projection (F : H2) (i : Fin 3) :
    (h2Projection F).first i = projection (F.first i) := rfl
@[simp] theorem second_h2Projection (F : H2) (i j : Fin 3) :
    (h2Projection F).second i j = projection (F.second i j) := rfl

theorem norm_h2Projection_le : ‖h2Projection‖ ≤ 1 := by
  apply h2Projection.opNorm_le_bound zero_le_one
  intro F
  simpa using norm_h2Project_le F

@[simp] theorem h2Projection_idempotent (F : H2) :
    h2Projection (h2Projection F) = h2Projection F := by
  apply H2.ext
  simp only [value_h2Projection, projection_idempotent]

theorem h2Projection_solenoidal (F : H2) :
    IsSolenoidal ((h2Projection F).value : SpatialField) :=
  projection_solenoidal F.value

theorem h2Projection_eq_self_iff (F : H2) :
    h2Projection F = F ↔ IsSolenoidal (F.value : SpatialField) := by
  constructor
  · intro h
    exact (projection_eq_self_iff F.value).mp (congrArg H2.value h)
  · intro h
    apply H2.ext
    exact projection_eq_self h

/-- Selfadjointness includes every ordered second derivative. -/
theorem h2Projection_selfadjoint (F G : H2) :
    inner ℝ (h2Projection F) G = inner ℝ F (h2Projection G) := by
  simp only [H2.inner_eq, value_h2Projection, first_h2Projection,
    second_h2Projection, projection_selfadjoint]

end UnforcedLeray.Leray
