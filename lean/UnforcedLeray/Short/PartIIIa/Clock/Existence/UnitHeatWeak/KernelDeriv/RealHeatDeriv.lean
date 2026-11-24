import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Basic
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_2_2
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeMajorant
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeIntegrable
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeDerivative
import UnforcedLeray.Lib.Cylinder.IBP
import UnforcedLeray.Lib.Train.Ops

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2/3`: positive-period version of `RealHeatDeriv` (lemma B)

Source of record: `the November 2 reference manuscript`, lines 2819-2836.

The prop `RealHeatDeriv` carries the hypothesis `0 < c` (organizer correction of
`PartIII-a:T21/3/2/1/2/3/org`): without it the statement is false at `c = 0`, since `IsCylTest 0 φ`
allows `φ(q,η) = exp(q²) χ(η)`, whose heat flow blows up as `τ ↑ 1/4`. This file proves
`realHeatDeriv : RealHeatDeriv` via `realHeatDeriv_of_pos`, using the Gaussian age derivative,
dominated differentiation on `(θ/2, 2θ)`, and whole-plane integration by parts
(`Short.PartI.IBPLeaf.integral_heatKernel2AgeDerivative_mul_comp_sub`, from
`Short/PartI/Sub/T02_1_4_6_4_2_2.lean`, which compiles without placeholders).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

private theorem opNorm_le_two_coord (L : ℝ × ℝ →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (1, 0)| + |L (0, 1)| := by
  apply ContinuousLinearMap.opNorm_le_bound L (by positivity)
  intro v
  have hv : L v = v.1 * L (1, 0) + v.2 * L (0, 1) := by
    have h1 : ((v.1, (0:ℝ)) : ℝ × ℝ) = v.1 • ((1:ℝ), (0:ℝ)) := by ext <;> simp
    have h2 : (((0:ℝ), v.2) : ℝ × ℝ) = v.2 • ((0:ℝ), (1:ℝ)) := by ext <;> simp
    have hv' : v = ((v.1, (0:ℝ)) : ℝ × ℝ) + (((0:ℝ), v.2) : ℝ × ℝ) := by ext <;> simp
    conv_lhs => rw [hv']
    rw [map_add, h1, h2, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [Real.norm_eq_abs, hv]
  have h1 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le v
  calc |v.1 * L (1, 0) + v.2 * L (0, 1)|
      ≤ |v.1 * L (1, 0)| + |v.2 * L (0, 1)| := abs_add_le _ _
    _ = |v.1| * |L (1, 0)| + |v.2| * |L (0, 1)| := by rw [abs_mul, abs_mul]
    _ ≤ ‖v‖ * |L (1, 0)| + ‖v‖ * |L (0, 1)| := by gcongr
    _ = (|L (1, 0)| + |L (0, 1)|) * ‖v‖ := by ring

private theorem exists_norm_bound_of_abs {g : ℝ × ℝ → ℝ} {M : ℝ} (h : ∀ x, |g x| ≤ M) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ x, ‖g x‖ ≤ M' :=
  ⟨max M 0, le_max_right _ _, fun x => by
    rw [Real.norm_eq_abs]; exact (h x).trans (le_max_left _ _)⟩

private theorem fderiv_norm_bound_of_coords {g : ℝ × ℝ → ℝ} {M1 M2 : ℝ}
    (h1 : ∀ x, |fderiv ℝ g x (1, 0)| ≤ M1) (h2 : ∀ x, |fderiv ℝ g x (0, 1)| ≤ M2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ g x‖ ≤ M :=
  ⟨max (M1 + M2) 0, le_max_right _ _, fun x => by
    refine (opNorm_le_two_coord _).trans ?_
    linarith [h1 x, h2 x, le_max_left (M1 + M2) 0]⟩

private theorem continuous_heatKernel2_age (τ : ℝ) :
    Continuous (UnforcedLeray.B0284.heatKernel2 τ) := by
  unfold UnforcedLeray.B0284.heatKernel2
  exact (((UnforcedLeray.B0191.contDiff_heatKernel 1 τ).continuous).comp continuous_fst).mul
    (((UnforcedLeray.B0191.contDiff_heatKernel 1 τ).continuous).comp continuous_snd)

private theorem lapS_eq_lapP_of_cyl {c : ℝ} {φ : ℝ × ℝ → ℝ}
    (hφ : UnforcedLeray.B0579.IsCylTest c φ) (z : ℝ × ℝ) :
    UnforcedLeray.Train.lapS φ z = lapP φ z := by
  have hdq : ∀ g : ℝ × ℝ → ℝ, Differentiable ℝ g → ∀ z : ℝ × ℝ,
      UnforcedLeray.Cyl.partialQ g z = UnforcedLeray.B0579.pd 0 g z :=
    fun g hg z => UnforcedLeray.Cyl.partialQ_eq_fderiv hg z
  have hde : ∀ g : ℝ × ℝ → ℝ, Differentiable ℝ g → ∀ z : ℝ × ℝ,
      UnforcedLeray.Cyl.partialEta g z = UnforcedLeray.B0579.pd 1 g z :=
    fun g hg z => UnforcedLeray.Cyl.partialEta_eq_fderiv hg z
  have hφd : Differentiable ℝ φ := hφ.differentiable
  have e1 : UnforcedLeray.Cyl.partialQ φ = UnforcedLeray.B0579.pd 0 φ := funext (hdq φ hφd)
  have e2 : UnforcedLeray.Cyl.partialEta φ = UnforcedLeray.B0579.pd 1 φ := funext (hde φ hφd)
  unfold UnforcedLeray.Train.lapS
  rw [e1, e2, hdq (UnforcedLeray.B0579.pd 0 φ) (hφ.pd 0).differentiable,
    hde (UnforcedLeray.B0579.pd 1 φ) (hφ.pd 1).differentiable]
  rfl

/-- The real heat derivative for a cylinder test on a cylinder of positive period. -/
theorem realHeatDeriv_of_pos : ∀ (c : ℝ) (φ : ℝ × ℝ → ℝ), 0 < c →
    UnforcedLeray.B0579.IsCylTest c φ →
    ∀ θ : ℝ, 0 < θ → ∀ y : ℝ × ℝ,
      HasDerivAt (fun τ => realHeat τ φ y) (realHeat θ (lapP φ) y) θ := by
  intro c φ hc hφ θ hθ y
  have hS := UnforcedLeray.Short.IIIa.Exist.IsCylTest.isCylSmoothBdd hc hφ
  obtain ⟨M0, hM0⟩ := hS.bdd []
  obtain ⟨M1, hM1⟩ := hS.bdd [0]
  obtain ⟨M2, hM2⟩ := hS.bdd [1]
  obtain ⟨M00, hM00⟩ := hS.bdd [0, 0]
  obtain ⟨M10, hM10⟩ := hS.bdd [1, 0]
  obtain ⟨M01, hM01⟩ := hS.bdd [0, 1]
  obtain ⟨M11, hM11⟩ := hS.bdd [1, 1]
  obtain ⟨K, hK0, hK⟩ := exists_norm_bound_of_abs (g := φ) hM0
  have hfB : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖φ x‖ ≤ M := ⟨K, hK0, hK⟩
  have hf1 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ φ x‖ ≤ M :=
    fderiv_norm_bound_of_coords (g := φ) hM1 hM2
  have hf2 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x,
      ‖fderiv ℝ (fun y => fderiv ℝ φ y (1, 0)) x‖ ≤ M :=
    fderiv_norm_bound_of_coords (g := fun y => fderiv ℝ φ y (1, 0)) hM00 hM10
  have hf3 : ∃ M : ℝ, 0 ≤ M ∧ ∀ x,
      ‖fderiv ℝ (fun y => fderiv ℝ φ y (0, 1)) x‖ ≤ M :=
    fderiv_norm_bound_of_coords (g := fun y => fderiv ℝ φ y (0, 1)) hM01 hM11
  have hIBP := UnforcedLeray.Short.PartI.IBPLeaf.integral_heatKernel2AgeDerivative_mul_comp_sub hθ
    hφ.smooth hfB hf1 hf2 hf3 y
  have hcomp : Continuous (fun w : ℝ × ℝ => φ (y - w)) :=
    hφ.continuous.comp (continuous_const.sub continuous_id)
  have hmeas : ∀ τ : ℝ, AEStronglyMeasurable
      (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 τ w * φ (y - w)) volume :=
    fun τ => ((continuous_heatKernel2_age τ).mul hcomp).aestronglyMeasurable
  have hI0 : Integrable (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 θ w * φ (y - w)) := by
    have h := (UnforcedLeray.B0284.integrable_heatKernel2 hθ).bdd_mul
      hcomp.aestronglyMeasurable (Filter.Eventually.of_forall fun w => hK (y - w))
    exact h.congr (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hF'meas : AEStronglyMeasurable
      (fun w : ℝ × ℝ => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * φ (y - w))
      volume :=
    ((UnforcedLeray.HeatCylinder.integrable_heatKernel2AgeDerivative hθ).aestronglyMeasurable).mul
      hcomp.aestronglyMeasurable
  have hint_bound : Integrable (fun w : ℝ × ℝ =>
      (4 * (θ⁻¹ ^ 2 + 2 / θ) * K) *
        ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w)) :=
    (UnforcedLeray.HeatCylinder.integrable_one_add_sq_mul_heatKernel2
      (by linarith : (0 : ℝ) < 2 * θ)).const_mul _
  have hbnd : ∀ᵐ w : ℝ × ℝ ∂volume, ∀ τ ∈ Set.Ioo (θ / 2) (2 * θ),
      ‖UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative τ w * φ (y - w)‖ ≤
        (4 * (θ⁻¹ ^ 2 + 2 / θ) * K) *
          ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w) := by
    refine Filter.Eventually.of_forall fun w τ hτ => ?_
    have hA : |UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative τ w| ≤
        4 * (θ⁻¹ ^ 2 + 2 / θ) *
          ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w) :=
      UnforcedLeray.HeatCylinder.abs_heatKernel2AgeDerivative_le_local hθ hτ.1 hτ.2 w
    have hA' : ‖UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative τ w‖ ≤
        4 * (θ⁻¹ ^ 2 + 2 / θ) *
          ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w) := by
      rw [Real.norm_eq_abs]; exact hA
    have hnn : 0 ≤ 4 * (θ⁻¹ ^ 2 + 2 / θ) *
        ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w) :=
      le_trans (norm_nonneg _) hA'
    rw [norm_mul]
    calc ‖UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative τ w‖ * ‖φ (y - w)‖
        ≤ (4 * (θ⁻¹ ^ 2 + 2 / θ) *
            ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w)) * K :=
          mul_le_mul hA' (hK (y - w)) (norm_nonneg _) hnn
      _ = (4 * (θ⁻¹ ^ 2 + 2 / θ) * K) *
          ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w) := by ring
  have hdiff : ∀ᵐ w : ℝ × ℝ ∂volume, ∀ τ ∈ Set.Ioo (θ / 2) (2 * θ),
      HasDerivAt (fun τ => UnforcedLeray.B0284.heatKernel2 τ w * φ (y - w))
        (UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative τ w * φ (y - w)) τ := by
    refine Filter.Eventually.of_forall fun w τ hτ => ?_
    have hτ0 : 0 < τ := by linarith [hτ.1]
    exact (UnforcedLeray.HeatCylinder.hasDerivAt_heatKernel2_age hτ0 w).mul_const (φ (y - w))
  have hD := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun τ (w : ℝ × ℝ) => UnforcedLeray.B0284.heatKernel2 τ w * φ (y - w))
    (F' := fun τ (w : ℝ × ℝ) => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative τ w * φ (y - w))
    (x₀ := θ)
    (bound := fun w : ℝ × ℝ => (4 * (θ⁻¹ ^ 2 + 2 / θ) * K) *
      ((1 + w.1 ^ 2 + w.2 ^ 2) * UnforcedLeray.B0284.heatKernel2 (2 * θ) w))
    (s := Set.Ioo (θ / 2) (2 * θ)) (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun τ => hmeas τ) hI0 hF'meas hbnd hint_bound hdiff
  have key : realHeat θ (lapP φ) y =
      ∫ w : ℝ × ℝ, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * φ (y - w) := by
    rw [hIBP]
    simp only [realHeat, lapS_eq_lapP_of_cyl hφ]
  rw [key]
  exact hD.2

/-- Lemma B: the age derivative of the real heat flow of a cylinder test of positive period. -/
theorem realHeatDeriv : UnforcedLeray.Short.IIIa.Exist.RealHeatDeriv :=
  fun c hc φ hφ => realHeatDeriv_of_pos c φ hc hφ

end UnforcedLeray.Short.IIIa.Exist
