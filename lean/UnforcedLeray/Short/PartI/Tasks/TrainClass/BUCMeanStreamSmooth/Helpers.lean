import UnforcedLeray.Short.PartI.Tasks.TrainClass.MeanStreamIncrement
import UnforcedLeray.Lib.Kernels.ParamIntegral

/-!
# Helpers for `PartI:TC/8` (`BUCMeanStreamSmooth`)

* `bucSm_kernel`: for `H` globally `C^∞` on `ℝ × (ℝ × ℝ)`, the parametric integral
  `y ↦ ∫_{τ ∈ (0,1]} H(τ, y)` is `C^∞` on `ℝ × ℝ`.  This is the proof of `HmeanContDiff`
  (`Tasks/TrainMeanEquations/HmeanContDiff.lean`) with the cell `(-c/2, c/2]` replaced by `(0, 1]`.
* `bucSm_deriv_eq`: `∂_η \bar v₁(r, 0) = ∂_y [(s,η) ↦ \bar v₁(s,η)](r, 0) (0,1)` for `r > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- Slice formula: the `n`-th derivative of `y ↦ H(q, y)` at `y`. -/
theorem bucSm_slice_iteratedFDeriv {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    (q : ℝ) (n : ℕ) (y : ℝ × ℝ) :
    iteratedFDeriv ℝ n (fun y' : ℝ × ℝ => H (q, y')) y =
      (iteratedFDeriv ℝ n H (q, y)).compContinuousLinearMap
        (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
  have hτ : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => z + (q, (0 : ℝ × ℝ))) :=
    contDiff_id.add contDiff_const
  have hsmooth : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => H (z + (q, (0 : ℝ × ℝ)))) :=
    hH.comp hτ
  have hfun : (fun y' : ℝ × ℝ => H (q, y')) =
      (fun z : ℝ × (ℝ × ℝ) => H (z + (q, (0 : ℝ × ℝ)))) ∘
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) := by
    funext y'
    simp
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (i := n)
    (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) hsmooth y (mod_cast le_top),
    iteratedFDeriv_comp_add_right]
  have hy : ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ) y + (q, (0 : ℝ × ℝ)) = (q, y) := by
    simp
  rw [hy]

/-- Continuity in `q` of the `n`-th derivative of the slice `y ↦ H(q, y)` at a fixed `y`. -/
theorem bucSm_slice_continuous {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
    (n : ℕ) (y : ℝ × ℝ) :
    Continuous (fun q : ℝ => iteratedFDeriv ℝ n (fun y' : ℝ × ℝ => H (q, y')) y) := by
  have hcont : Continuous (fun q : ℝ => iteratedFDeriv ℝ n H (q, y)) :=
    (hH.continuous_iteratedFDeriv (m := n) (mod_cast le_top)).comp
      (continuous_id.prodMk continuous_const)
  have hT : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × (ℝ × ℝ)) ℝ =>
      A.compContinuousLinearMap (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))).continuous
  refine (hT.comp hcont).congr fun q => ?_
  exact (bucSm_slice_iteratedFDeriv hH q n y).symm

/-- Measurability in `q` of the `n`-th derivative of the slice, for every measure. -/
theorem bucSm_hmeas {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (μ : Measure ℝ) :
    ∀ (n : ℕ) (y : ℝ × ℝ),
      AEStronglyMeasurable (fun q : ℝ => iteratedFDeriv ℝ n (fun y' : ℝ × ℝ => H (q, y')) y) μ :=
  fun n y => (bucSm_slice_continuous hH n y).aestronglyMeasurable

/-- Local domination of all iterated slice derivatives, uniformly in `q ∈ (0, 1]`. -/
theorem bucSm_locDominated {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) :
    UnforcedLeray.Kernels.LocDominated (volume.restrict (Ioc (0 : ℝ) 1))
      (fun (q : ℝ) (y : ℝ × ℝ) => H (q, y)) univ := by
  intro n x _
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x 1) :=
    isCompact_Icc.prod (isCompact_closedBall x 1)
  have hcont : ContinuousOn (iteratedFDeriv ℝ n H)
      (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall x 1) :=
    (hH.continuous_iteratedFDeriv (m := n) (mod_cast le_top)).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos,
    fun _ => C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖,
    integrable_const _, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))]
    with q hq y hy
  have hbound : ‖iteratedFDeriv ℝ n H (q, y)‖ ≤ C :=
    hC (q, y) ⟨Ioc_subset_Icc_self hq, hy⟩
  show ‖iteratedFDeriv ℝ n (fun y' : ℝ × ℝ => H (q, y')) y‖ ≤
    C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖
  rw [bucSm_slice_iteratedFDeriv hH q n y]
  calc ‖(iteratedFDeriv ℝ n H (q, y)).compContinuousLinearMap
          (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))‖
      ≤ ‖iteratedFDeriv ℝ n H (q, y)‖ *
          ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ :=
        mul_le_mul_of_nonneg_right hbound hM0

/-- The parametric integral over `τ ∈ (0,1]` of a globally `C^∞` family is `C^∞` in `y`. -/
theorem bucSm_kernel {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => ∫ τ, H (τ, y) ∂(volume.restrict (Ioc (0 : ℝ) 1))) univ := by
  have hsmooth : ∀ τ : ℝ, ContDiff ℝ ∞ (fun y : ℝ × ℝ => H (τ, y)) := fun τ =>
    hH.comp (contDiff_const.prodMk contDiff_id)
  exact UnforcedLeray.Kernels.contDiffOn_integral (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (F := fun (τ : ℝ) (y : ℝ × ℝ) => H (τ, y)) (U := univ) isOpen_univ (ae_of_all _ hsmooth)
    (bucSm_hmeas hH _) (bucSm_locDominated hH)

/-- For `r > 0`, the `η`-derivative of `\bar v₁` at `(r, 0)` is the derivative of the joint
function along the direction `(0, 1)`. -/
theorem bucSm_deriv_eq {ν c : ℝ} (tr : B0140.TrainSol ν c)
    (hU : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (Ioi 0 ×ˢ univ))
    (r : ℝ) (hr : 0 < r) :
    deriv (meanVel1 tr r) 0 =
      fderiv ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (r, 0) (0, 1) := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hmem : ((r, (0 : ℝ)) : ℝ × ℝ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) := ⟨hr, mem_univ _⟩
  have hdiff : DifferentiableAt ℝ (fun x : ℝ × ℝ => meanVel1 tr x.1 x.2) (r, 0) :=
    (hU.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
  have hline : HasDerivAt (fun e : ℝ => ((r, e) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) r).prodMk (hasDerivAt_id (0 : ℝ))
  have h := hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  exact h.deriv

end UnforcedLeray.Short.PartI
