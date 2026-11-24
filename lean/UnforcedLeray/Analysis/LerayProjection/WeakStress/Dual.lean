import UnforcedLeray.Analysis.LerayProjection.SobolevProjection
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Actual tensor divergence as a bounded functional on weak H¹(R³)

A tensor has three vector-valued L² flux rows. Its divergence acts by the
negative contraction of these rows with the actual weak coordinate derivatives
of the test field. Every scalar integral is justified by L² Hölder. The norm is
the Hilbert square sum of the three row norms, so the dual bound has constant one.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace UnforcedLeray.Leray.WeakStress
open SobolevGraph

/-- Three actual vector-valued L² tensor flux rows, with the Hilbert product norm. -/
abbrev TensorL2 := PiLp 2 (fun _ : Fin 3 => L2Space)

/-- The three actual weak derivatives, bundled with their Hilbert square-sum norm. -/
def gradientCLM : H1 →L[ℝ] TensorL2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => L2Space)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => H1.derivativeCLM i)

@[simp] theorem gradientCLM_apply (F : H1) (i : Fin 3) :
    (gradientCLM F).ofLp i = F.derivative i := rfl

theorem norm_gradient_sq (F : H1) :
    ‖gradientCLM F‖ ^ 2 = ∑ i : Fin 3, ‖F.derivative i‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem norm_gradient_le (F : H1) : ‖gradientCLM F‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_gradient_sq, H1.norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem norm_gradientCLM_le : ‖gradientCLM‖ ≤ 1 := by
  apply gradientCLM.opNorm_le_bound zero_le_one
  intro F
  simpa only [one_mul] using norm_gradient_le F

/-- The actual distributional tensor divergence, evaluated on a weak H¹ field. -/
def divergence (S : TensorL2) : H1 →L[ℝ] ℝ :=
  -((innerSL ℝ S).comp gradientCLM)

@[simp] theorem divergence_apply (S : TensorL2) (F : H1) :
    divergence S F = -inner ℝ S (gradientCLM F) := rfl

/-- Each physical stress-gradient pairing is an honest integrable scalar function. -/
theorem row_pairing_integrable (S : TensorL2) (F : H1) (i : Fin 3) :
    Integrable (fun x : Space => inner ℝ (S.ofLp i x) (F.derivative i x)) volume :=
  L2.integrable_inner (𝕜 := ℝ) (S.ofLp i) (F.derivative i)

/-- The dual action is the actual sum of the three distributional divergence integrals. -/
theorem divergence_eq_sum_integral (S : TensorL2) (F : H1) :
    divergence S F =
      -(∑ i : Fin 3, ∫ x : Space, inner ℝ (S.ofLp i x) (F.derivative i x)) := by
  rw [divergence_apply, PiLp.inner_apply]
  rfl

theorem divergence_eq_integral (S : TensorL2) (F : H1) :
    divergence S F =
      -(∫ x : Space, ∑ i : Fin 3, inner ℝ (S.ofLp i x) (F.derivative i x)) := by
  rw [divergence_eq_sum_integral, integral_finsetSum]
  intro i _
  exact row_pairing_integrable S F i

/-- Cauchy–Schwarz gives the sharp basic H⁻¹ estimate with no PDE premise. -/
theorem norm_divergence_apply_le (S : TensorL2) (F : H1) :
    ‖divergence S F‖ ≤ ‖S‖ * ‖F‖ := by
  rw [divergence_apply, norm_neg]
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (norm_gradient_le F) (norm_nonneg S))

theorem norm_divergence_le (S : TensorL2) : ‖divergence S‖ ≤ ‖S‖ :=
  (divergence S).opNorm_le_bound (norm_nonneg S) (norm_divergence_apply_le S)

/-- The same forcing tested after the genuine H¹ Leray projection. -/
def projectedDivergence (S : TensorL2) : H1 →L[ℝ] ℝ :=
  (divergence S).comp h1Projection

theorem projectedDivergence_apply (S : TensorL2) (F : H1) :
    projectedDivergence S F = divergence S (h1Projection F) := rfl

theorem norm_projectedDivergence_le (S : TensorL2) :
    ‖projectedDivergence S‖ ≤ ‖S‖ := by
  apply (projectedDivergence S).opNorm_le_bound (norm_nonneg S)
  intro F
  exact (norm_divergence_apply_le S (h1Projection F)).trans
    (mul_le_mul_of_nonneg_left (norm_h1Project_le F) (norm_nonneg S))

/-- For solenoidal tests the projected forcing is precisely the ordinary weak divergence. -/
theorem projectedDivergence_eq_of_solenoidal (S : TensorL2) (F : H1)
    (hF : IsSolenoidal (F.value : SpatialField)) :
    projectedDivergence S F = divergence S F := by
  rw [projectedDivergence_apply, (h1Projection_eq_self_iff F).mpr hF]

end UnforcedLeray.Leray.WeakStress
