import UnforcedLeray.TestFunctions
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic

/-! Actual weak derivative uniqueness, invariance and integration by parts on R³. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace UnforcedLeray
namespace HasWeakSpatialDerivative
variable {i : Fin 3} {f g f' g' : SpatialField}

/-- The derivative predicate depends only on almost-everywhere classes. -/
theorem congr (h : HasWeakSpatialDerivative i f g)
    (hf : f =ᵐ[volume] f') (hg : g =ᵐ[volume] g') :
    HasWeakSpatialDerivative i f' g' := by
  have hl (φ : Space → ℝ) :
      (fun x => spatialTestDerivative i φ x • f x) =ᵐ[volume]
      (fun x => spatialTestDerivative i φ x • f' x) := by
    filter_upwards [hf] with x hx
    rw [hx]
  have hr (φ : Space → ℝ) : (fun x => φ x • g x) =ᵐ[volume] (fun x => φ x • g' x) := by
    filter_upwards [hg] with x hx
    rw [hx]
  refine ⟨fun φ hφ => (h.left_integrable φ hφ).congr (hl φ),
    fun φ hφ => (h.right_integrable φ hφ).congr (hr φ), ?_⟩
  intro φ hφ
  rw [← integral_congr_ae (hl φ), ← integral_congr_ae (hr φ)]
  exact h.identity φ hφ

/-- Two L² weak derivatives of the same field agree almost everywhere. -/
theorem ae_eq {g₁ g₂ : SpatialField}
    (h₁ : HasWeakSpatialDerivative i f g₁) (h₂ : HasWeakSpatialDerivative i f g₂)
    (hg₁ : MemLp g₁ 2 volume) (hg₂ : MemLp g₂ 2 volume) : g₁ =ᵐ[volume] g₂ := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (hg₁.locallyIntegrable (by norm_num)) (hg₂.locallyIntegrable (by norm_num))
  intro φ hs hc
  have hφ : IsSpatialTest φ := ⟨hs,hc⟩
  apply neg_injective
  exact (h₁.identity φ hφ).symm.trans (h₂.identity φ hφ)

/-- The zero field has zero weak derivative. -/
theorem zero (i : Fin 3) : HasWeakSpatialDerivative i (0 : SpatialField) 0 := by
  constructor <;> intros <;> simp

/-- Distributional coordinate derivatives are additive. -/
theorem add {f₁ f₂ g₁ g₂ : SpatialField}
    (h₁ : HasWeakSpatialDerivative i f₁ g₁) (h₂ : HasWeakSpatialDerivative i f₂ g₂) :
    HasWeakSpatialDerivative i (f₁ + f₂) (g₁ + g₂) := by
  constructor
  · intro φ hφ
    simpa only [Pi.add_apply, smul_add] using
      (h₁.left_integrable φ hφ).fun_add (h₂.left_integrable φ hφ)
  · intro φ hφ
    simpa only [Pi.add_apply, smul_add] using
      (h₁.right_integrable φ hφ).fun_add (h₂.right_integrable φ hφ)
  · intro φ hφ
    simp only [Pi.add_apply, smul_add]
    rw [integral_add (h₁.left_integrable φ hφ) (h₂.left_integrable φ hφ),
      integral_add (h₁.right_integrable φ hφ) (h₂.right_integrable φ hφ),
      h₁.identity φ hφ, h₂.identity φ hφ, neg_add]

/-- Scalar multiplication commutes with the weak derivative. -/
theorem smul (h : HasWeakSpatialDerivative i f g) (c : ℝ) :
    HasWeakSpatialDerivative i (c • f) (c • g) := by
  constructor
  · intro φ hφ
    simpa only [Pi.smul_apply, smul_comm (spatialTestDerivative i φ _) c] using
      (h.left_integrable φ hφ).fun_smul c
  · intro φ hφ
    simpa only [Pi.smul_apply, smul_comm (φ _) c] using (h.right_integrable φ hφ).fun_smul c
  · intro φ hφ
    simp only [Pi.smul_apply, smul_comm (spatialTestDerivative i φ _) c,
      smul_comm (φ _) c, integral_smul, h.identity φ hφ, smul_neg]
end HasWeakSpatialDerivative

/-- Compact smooth scalar tests times continuous vector fields are integrable. -/
theorem IsSpatialTest.integrable_smul {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    {f : SpatialField} (hf : Continuous f) : Integrable (fun x => φ x • f x) := by
  exact (hφ.continuous.smul hf).integrable_of_hasCompactSupport hφ.compact.smul_right

/-- A C¹ field has its classical directional derivative as a weak derivative.
All compact-test integrability obligations are proved, without global decay assumptions. -/
theorem hasWeakSpatialDerivative_of_contDiff {f : SpatialField}
    (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    HasWeakSpatialDerivative i f (fun x => fderiv ℝ f x (coordinateVector i)) := by
  have hfd : Continuous (fun x => fderiv ℝ f x (coordinateVector i)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  constructor
  · intro φ hφ
    exact (hφ.derivative i).integrable_smul hf.continuous
  · intro φ hφ
    exact hφ.integrable_smul hfd
  · intro φ hφ
    have hparts := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      ((hφ.derivative i).integrable_smul hf.continuous)
      (hφ.integrable_smul hfd) (hφ.integrable_smul hf.continuous)
      (fun x _ => (hφ.smooth.differentiable (by simp)).differentiableAt)
      (fun x _ => (hf.differentiable (by norm_num)).differentiableAt)
    exact neg_eq_iff_eq_neg.mp hparts.symm
end UnforcedLeray
