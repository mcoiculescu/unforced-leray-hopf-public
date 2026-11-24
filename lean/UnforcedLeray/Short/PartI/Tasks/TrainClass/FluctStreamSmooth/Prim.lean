import Mathlib.Analysis.Calculus.ContDiff.Operations
import UnforcedLeray.Lib.Kernels.ParamIntegral

/-!
# Helper for `PartI:TC/7` (`FluctStreamSmooth`): smoothness of a parametric primitive

Helper module of `Short/PartI/Tasks/TrainClass/FluctStreamSmooth.lean`.  For a jointly smooth
`H : ℝ × E → ℝ`, the map `y ↦ ∫_0^1 H(τ, y) dτ` is smooth on `E`.  This is the parametric
integral of `Lib/Kernels/ParamIntegral.lean` (`Kernels.contDiffOn_integral`) with the finite
measure `volume.restrict (Ioc 0 1)`; the slice derivatives are handled as in
`Tasks/TrainMeanEquations/HmeanContDiff.lean` (there they are private).

Used with `E = ℝ × (ℝ × ℝ)` (parameters `(t, (q, η))`, `t` the log of the age).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.FluctPrim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Slice formula: the `n`-th derivative of `y ↦ H(τ, y)` is the `n`-th derivative of `H` at
`(τ, y)` composed with the linear map `y ↦ (0, y)`. -/
theorem slice_iteratedFDeriv {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (τ : ℝ) (n : ℕ) (y : E) :
    iteratedFDeriv ℝ n (fun y' : E => H (τ, y')) y =
      (iteratedFDeriv ℝ n H (τ, y)).compContinuousLinearMap
        (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ E) := by
  have hτ : ContDiff ℝ ∞ (fun z : ℝ × E => z + (τ, (0 : E))) :=
    contDiff_id.add contDiff_const
  have hsmooth : ContDiff ℝ ∞ (fun z : ℝ × E => H (z + (τ, (0 : E)))) :=
    hH.comp hτ
  have hfun : (fun y' : E => H (τ, y')) =
      (fun z : ℝ × E => H (z + (τ, (0 : E)))) ∘ (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext y'
    simp
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (i := n)
    (ContinuousLinearMap.inr ℝ ℝ E) hsmooth y (mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  have hy : ContinuousLinearMap.inr ℝ ℝ E y + (τ, (0 : E)) = (τ, y) := by
    simp
  rw [hy]

/-- Continuity in `τ` of the `n`-th derivative of the slice `y ↦ H(τ, y)` at a fixed `y`. -/
theorem slice_continuous {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (n : ℕ) (y : E) :
    Continuous (fun τ : ℝ => iteratedFDeriv ℝ n (fun y' : E => H (τ, y')) y) := by
  have hcont : Continuous (fun τ : ℝ => iteratedFDeriv ℝ n H (τ, y)) :=
    (hH.continuous_iteratedFDeriv (m := n) (mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × E) ℝ =>
      A.compContinuousLinearMap (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ E)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ E)).continuous
  refine (hT.comp hcont).congr fun τ => ?_
  exact (slice_iteratedFDeriv hH τ n y).symm

/-- Measurability in `τ` of the `n`-th derivative of the slice, for every measure. -/
theorem slice_hmeas {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (μ : Measure ℝ) :
    ∀ (n : ℕ) (y : E),
      AEStronglyMeasurable (fun τ : ℝ => iteratedFDeriv ℝ n (fun y' : E => H (τ, y')) y) μ :=
  fun n y => (slice_continuous hH n y).aestronglyMeasurable

/-- Local domination of all iterated slice derivatives, uniformly in `τ ∈ (0, 1]`. -/
theorem slice_locDominated [ProperSpace E] {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) :
    UnforcedLeray.Kernels.LocDominated (volume.restrict (Ioc (0 : ℝ) 1))
      (fun (τ : ℝ) (y : E) => H (τ, y)) univ := by
  intro n x _
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x 1) :=
    isCompact_Icc.prod (isCompact_closedBall x 1)
  have hcont : ContinuousOn (iteratedFDeriv ℝ n H) (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x 1) :=
    (hH.continuous_iteratedFDeriv (m := n) (mod_cast le_top)).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ E‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos,
    fun _ => C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ E‖,
    integrable_const _, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))]
    with τ hτ y hy
  have hbound : ‖iteratedFDeriv ℝ n H (τ, y)‖ ≤ C :=
    hC (τ, y) ⟨Ioc_subset_Icc_self hτ, hy⟩
  show ‖iteratedFDeriv ℝ n (fun y' : E => H (τ, y')) y‖ ≤
    C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ E‖
  rw [slice_iteratedFDeriv hH τ n y]
  calc ‖(iteratedFDeriv ℝ n H (τ, y)).compContinuousLinearMap
          (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ E)‖
      ≤ ‖iteratedFDeriv ℝ n H (τ, y)‖ *
          ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ E‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ E‖ :=
        mul_le_mul_of_nonneg_right hbound hM0

/-- **Parametric primitive over `[0,1]`.** If `H : ℝ × E → ℝ` is `C^∞`, then
`y ↦ ∫_0^1 H(τ, y) dτ` is `C^∞` on `E`. -/
theorem contDiff_primitive01 [ProperSpace E] {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun y : E => ∫ τ in (0 : ℝ)..1, H (τ, y)) := by
  have hsmooth : ∀ τ : ℝ, ContDiff ℝ ∞ (fun y : E => H (τ, y)) := fun τ =>
    hH.comp (contDiff_const.prodMk contDiff_id)
  have key := UnforcedLeray.Kernels.contDiffOn_integral
    (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := fun (τ : ℝ) (y : E) => H (τ, y))
    (U := univ) isOpen_univ (ae_of_all _ hsmooth)
    (slice_hmeas hH _) (slice_locDominated hH)
  rw [contDiffOn_univ] at key
  have heq : (fun y : E => ∫ τ in (0 : ℝ)..1, H (τ, y)) =
      (fun y : E => ∫ a, H (a, y) ∂(volume.restrict (Ioc (0 : ℝ) 1))) := by
    funext y
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [heq]
  exact key

end UnforcedLeray.Short.PartI.FluctPrim
