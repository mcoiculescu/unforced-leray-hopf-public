import UnforcedLeray.Units.B0289.Semigroup
import UnforcedLeray.Units.B0296.Kernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Convolution of the actual Gaussian derivative kernel

This scalar identity is the kernel algebra needed to commute heat past the literal B0296
gradient-kernel response.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open Set
open Filter
open UnforcedLeray.B0289
open UnforcedLeray.B0296

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

private theorem integrable_id_heatKernel1 {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun x : ℝ => x * B0191.heatKernel 1 θ x) := by
  have h := integrable_mul_exp_neg_mul_sq (b := (4 * θ)⁻¹) (by positivity)
  have hc := h.const_mul ((Real.sqrt (4 * Real.pi * 1 * θ))⁻¹)
  refine hc.congr ?_
  filter_upwards [] with x
  change (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ * (x * Real.exp (-(4 * θ)⁻¹ * x ^ 2)) =
    x * B0191.heatKernel 1 θ x
  rw [B0191.heatKernel]
  have hexp : -(x ^ 2) / (4 * 1 * θ) = -(4 * θ)⁻¹ * x ^ 2 := by
    field_simp
  rw [hexp]
  ring

/-- The first moment of a centered one-dimensional Gaussian is zero. -/
private theorem integral_id_heatKernel1_eq_zero {θ : ℝ} (hθ : 0 < θ) :
    ∫ x : ℝ, x * B0191.heatKernel 1 θ x = 0 := by
  let f : ℝ → ℝ := fun x => x * B0191.heatKernel 1 θ x
  have hf : Integrable f := integrable_id_heatKernel1 hθ
  have hflip : ∫ x : ℝ, f (-x) = ∫ x : ℝ, f x := by
    simpa only [f] using (integral_neg_eq_self (f := f) (μ := volume))
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    simp [f, B0191.heatKernel, neg_mul]
  have hoddInt : ∫ x : ℝ, f (-x) = -∫ x : ℝ, f x := by
    rw [integral_congr_ae (Eventually.of_forall hodd), integral_neg]
  have h : (∫ x : ℝ, f x) = -∫ x : ℝ, f x := hflip.symm.trans hoddInt
  linarith

private theorem integral_id_heatKernel1_shift {θ q : ℝ} (hθ : 0 < θ) :
    ∫ x : ℝ, x * B0191.heatKernel 1 θ (x - q) = q := by
  have hI₁ : Integrable (fun x : ℝ => (x - q) * B0191.heatKernel 1 θ (x - q)) :=
    (integrable_id_heatKernel1 hθ).comp_sub_right q
  have hI₂ : Integrable (fun x : ℝ => q * B0191.heatKernel 1 θ (x - q)) :=
    ((UnforcedLeray.B0289.integrable_heatKernel1 hθ).comp_sub_right q).const_mul _
  have hsplit : ∀ x : ℝ,
      x * B0191.heatKernel 1 θ (x - q) =
        (x - q) * B0191.heatKernel 1 θ (x - q) +
          q * B0191.heatKernel 1 θ (x - q) := by
    intro x
    calc
      x * B0191.heatKernel 1 θ (x - q) =
          ((x - q) + q) * B0191.heatKernel 1 θ (x - q) := by congr 1; ring
      _ = _ := by ring
  calc
    ∫ x : ℝ, x * B0191.heatKernel 1 θ (x - q) =
        ∫ x : ℝ, ((x - q) * B0191.heatKernel 1 θ (x - q) +
          q * B0191.heatKernel 1 θ (x - q)) := by
            refine integral_congr_ae (Eventually.of_forall hsplit)
    _ = (∫ x : ℝ, (x - q) * B0191.heatKernel 1 θ (x - q)) +
          ∫ x : ℝ, q * B0191.heatKernel 1 θ (x - q) := integral_add hI₁ hI₂
    _ = 0 + q * 1 := by
          rw [integral_sub_right_eq_self (fun x : ℝ => x * B0191.heatKernel 1 θ x) q,
            integral_id_heatKernel1_eq_zero hθ, integral_const_mul,
            integral_sub_right_eq_self, UnforcedLeray.B0284.integral_heatKernel_one hθ]
    _ = q := by ring

/-- One-dimensional Gaussian heat followed by the derivative kernel is the derivative Gaussian
at the summed age. -/
theorem integral_heatKernel1_dHeatKernel_conv {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (y : ℝ) :
    ∫ x : ℝ, B0191.heatKernel 1 α (y - x) * dHeatKernel β x =
      dHeatKernel (α + β) y := by
  let γ : ℝ := α * β / (α + β)
  let q : ℝ := β / (α + β) * y
  have hsum : 0 < α + β := by positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hprod (x : ℝ) :
      B0191.heatKernel 1 α (y - x) * B0191.heatKernel 1 β x =
        B0191.heatKernel 1 (α + β) y * B0191.heatKernel 1 γ (x - q) := by
    simpa [γ, q] using heatKernel1_product hα hβ y x
  have hmean : ∫ x : ℝ, x * B0191.heatKernel 1 γ (x - q) = q := by
    simpa [γ] using integral_id_heatKernel1_shift (θ := γ) hγ
  have hX : Integrable (fun x : ℝ => x * B0191.heatKernel 1 γ (x - q)) := by
    have hA := (integrable_id_heatKernel1 hγ).comp_sub_right q
    have hB := ((UnforcedLeray.B0289.integrable_heatKernel1 hγ).comp_sub_right q).const_mul q
    have hsum (x : ℝ) : x * B0191.heatKernel 1 γ (x - q) =
        (x - q) * B0191.heatKernel 1 γ (x - q) + q * B0191.heatKernel 1 γ (x - q) := by
      ring
    exact (hA.add hB).congr (Eventually.of_forall fun x => (hsum x).symm)
  have hconv : Integrable (fun x : ℝ =>
      B0191.heatKernel 1 (α + β) y * (-(x / (2 * β)) *
        B0191.heatKernel 1 γ (x - q))) := by
    have hj : Integrable (fun x : ℝ => -(1 / (2 * β)) *
        (x * B0191.heatKernel 1 γ (x - q))) := hX.const_mul _
    have heq : (fun x : ℝ => -(x / (2 * β)) * B0191.heatKernel 1 γ (x - q)) =
        fun x => -(1 / (2 * β)) * (x * B0191.heatKernel 1 γ (x - q)) := by
      funext x
      ring
    have hk : Integrable (fun x : ℝ => -(x / (2 * β)) *
        B0191.heatKernel 1 γ (x - q)) :=
      hj.congr (Eventually.of_forall fun x => (congrFun heq x).symm)
    exact hk.const_mul _
  calc
    ∫ x : ℝ, B0191.heatKernel 1 α (y - x) * dHeatKernel β x =
        ∫ x : ℝ, B0191.heatKernel 1 (α + β) y *
          (-(x / (2 * β)) * B0191.heatKernel 1 γ (x - q)) := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            change B0191.heatKernel 1 α (y - x) *
              (-(x / (2 * β)) * B0191.heatKernel 1 β x) =
                B0191.heatKernel 1 (α + β) y *
                  (-(x / (2 * β)) * B0191.heatKernel 1 γ (x - q))
            calc
              _ = (B0191.heatKernel 1 α (y - x) * B0191.heatKernel 1 β x) *
                  (-(x / (2 * β)) : ℝ) := by ring
              _ = (B0191.heatKernel 1 (α + β) y * B0191.heatKernel 1 γ (x - q)) *
                  (-(x / (2 * β) : ℝ)) := by rw [hprod x]
              _ = _ := by ring
    _ = B0191.heatKernel 1 (α + β) y * (-(q / (2 * β))) := by
          rw [integral_const_mul]
          have hfactor : (fun x : ℝ => -(x / (2 * β)) *
              B0191.heatKernel 1 γ (x - q)) =
              (fun x => -(1 / (2 * β)) * (x * B0191.heatKernel 1 γ (x - q))) := by
            funext x
            ring
          rw [hfactor, integral_const_mul, hmean]
          ring
    _ = dHeatKernel (α + β) y := by
          dsimp [q, UnforcedLeray.B0296.dHeatKernel]
          field_simp [ne_of_gt hβ, ne_of_gt hsum]

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.integral_heatKernel1_dHeatKernel_conv
