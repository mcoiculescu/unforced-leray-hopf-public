import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Lib.Kernels.ParamIntegral

/-!
# Part I, task `PartI:T01/HmeanContDiff`: horizontal averaging preserves smoothness

Source of record: `the November 2 reference manuscript`, lines 397-404 (`sct:mean`).
The statement `HmeanContDiff` is defined in `Short/PartI/Sub/T01.lean`.

Route. For `f` jointly `C^∞` on `(0, ∞) × Plane`, put `H(q, t, η) = f(e^t, q, η)`. This is a
globally `C^∞` function on `ℝ × (ℝ × ℝ)`, because `e^t > 0`. The parametric integral
`Kernels.contDiffOn_integral` (Lib/Kernels/ParamIntegral.lean) on `U = univ` with the finite
measure `μ = volume.restrict (Ioc (-c/2) (c/2))` and parameter `y = (t, η)` gives that
`(t, η) ↦ c⁻¹ ∫ H(q, t, η) dμ(q) = hmean c (f (e^t)) η` is `C^∞`. Composing with
`(s, η) ↦ (log s, η)`, which is `C^∞` on `(0, ∞) × ℝ`, gives the claim, since `e^(log s) = s`.

The two hypotheses of the kernel lemma are proved here.
* The `q`-slice `y ↦ H(q, y)` is `C^∞`, and its `n`-th derivative at `y` is the `n`-th derivative
  of `H` at `(q, y)` composed with the linear map `y ↦ (0, y)` (`hmeanCD_slice_iteratedFDeriv`).
* Hence `q ↦ ∂^n H_q(y)` is continuous (`hmeanCD_slice_continuous`), so it is measurable.
* On the compact box `Icc (-c/2) (c/2) ×ˢ closedBall x 1` the continuous function `∂^n H` is
  bounded, so `∂^n H_q(y)` is bounded uniformly for `q ∈ Ioc (-c/2) (c/2)` and `y` near `x`
  (`hmeanCD_locDominated`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The joint integrand `(q, t, η) ↦ f(e^t, q, η)` is `C^∞` on all of `ℝ × (ℝ × ℝ)`,
since `e^t` always lies in `(0, ∞)`. -/
private theorem hmeanCD_joint_contDiff {f : ℝ → Plane → ℝ}
    (hf : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => f x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => f (Real.exp x.2.1) (x.1, x.2.2)) := by
  have hmap : ContDiff ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => ((Real.exp x.2.1, (x.1, x.2.2)) : ℝ × Plane)) := by
    fun_prop
  exact hf.comp_contDiff hmap (fun x => ⟨Set.mem_Ioi.2 (Real.exp_pos _), Set.mem_univ _⟩)

/-- Slice formula: the `n`-th derivative of `y ↦ H(q, y)` at `y` is the `n`-th derivative of `H`
at `(q, y)` composed with the linear map `y ↦ (0, y)`. -/
private theorem hmeanCD_slice_iteratedFDeriv {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
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
private theorem hmeanCD_slice_continuous {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H)
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
  exact (hmeanCD_slice_iteratedFDeriv hH q n y).symm

/-- Measurability in `q` of the `n`-th derivative of the slice, for every finite measure. -/
private theorem hmeanCD_hmeas {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (μ : Measure ℝ) :
    ∀ (n : ℕ) (y : ℝ × ℝ),
      AEStronglyMeasurable (fun q : ℝ => iteratedFDeriv ℝ n (fun y' : ℝ × ℝ => H (q, y')) y) μ :=
  fun n y => (hmeanCD_slice_continuous hH n y).aestronglyMeasurable

/-- Local domination of all iterated slice derivatives, uniformly in `q ∈ Ioc (-c/2) (c/2)`. -/
private theorem hmeanCD_locDominated {H : ℝ × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ ∞ H) (c : ℝ) :
    UnforcedLeray.Kernels.LocDominated (volume.restrict (Ioc (-c / 2) (c / 2)))
      (fun (q : ℝ) (y : ℝ × ℝ) => H (q, y)) univ := by
  intro n x _
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    isCompact_Icc.prod (isCompact_closedBall x 1)
  have hcont : ContinuousOn (iteratedFDeriv ℝ n H)
      (Icc (-c / 2) (c / 2) ×ˢ Metric.closedBall x 1) :=
    (hH.continuous_iteratedFDeriv (m := n) (mod_cast le_top)).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ :=
    Finset.prod_nonneg fun _ _ => norm_nonneg _
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos,
    fun _ => C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖,
    integrable_const _, ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (-c / 2) (c / 2)))]
    with q hq y hy
  have hbound : ‖iteratedFDeriv ℝ n H (q, y)‖ ≤ C :=
    hC (q, y) ⟨Ioc_subset_Icc_self hq, hy⟩
  show ‖iteratedFDeriv ℝ n (fun y' : ℝ × ℝ => H (q, y')) y‖ ≤
    C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖
  rw [hmeanCD_slice_iteratedFDeriv hH q n y]
  calc ‖(iteratedFDeriv ℝ n H (q, y)).compContinuousLinearMap
          (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))‖
      ≤ ‖iteratedFDeriv ℝ n H (q, y)‖ *
          ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)‖ :=
        mul_le_mul_of_nonneg_right hbound hM0

/-- **Horizontal averaging preserves smoothness** (`HmeanContDiff`, source lines 397-404): for
`f` jointly `C^∞` on `(0, ∞) × Plane`, the map `(s, η) ↦ hmean c (f s) η` is `C^∞` on
`(0, ∞) × ℝ`. -/
theorem hmeanContDiff : HmeanContDiff := by
  unfold HmeanContDiff
  intro c _ f hf
  have hH := hmeanCD_joint_contDiff hf
  have hsmooth : ∀ q : ℝ, ContDiff ℝ ∞ (fun y : ℝ × ℝ => f (Real.exp y.1) (q, y.2)) := by
    intro q
    have hq : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((q, y) : ℝ × (ℝ × ℝ))) :=
      contDiff_const.prodMk contDiff_id
    exact hH.comp hq
  have key := UnforcedLeray.Kernels.contDiffOn_integral
    (μ := volume.restrict (Ioc (-c / 2) (c / 2)))
    (F := fun (q : ℝ) (y : ℝ × ℝ) => f (Real.exp y.1) (q, y.2))
    (U := univ) isOpen_univ (ae_of_all _ hsmooth)
    (hmeanCD_hmeas hH _) (hmeanCD_locDominated hH c)
  have hΨ : ContDiffOn ℝ ∞ (fun y : ℝ × ℝ => hmean c (f (Real.exp y.1)) y.2) univ :=
    key.const_smul c⁻¹
  have hlog : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => (Real.log x.1, x.2)) (Ioi 0 ×ˢ univ) := by
    refine ContDiffOn.prodMk ?_ contDiffOn_snd
    exact Real.contDiffOn_log.comp contDiffOn_fst (fun x hx => (Set.mem_Ioi.1 hx.1).ne')
  have hcomp := hΨ.comp hlog (fun x _ => mem_univ _)
  refine hcomp.congr fun x hx => ?_
  show hmean c (f x.1) x.2 = hmean c (f (Real.exp (Real.log x.1))) x.2
  rw [Real.exp_log (Set.mem_Ioi.1 hx.1)]

end UnforcedLeray.Short.PartI
