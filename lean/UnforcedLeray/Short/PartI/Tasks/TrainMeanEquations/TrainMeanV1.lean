import UnforcedLeray.Short.PartI.Sub.T01

/-!
# Part I, task `PartI:T01/1`: the mean velocity is minus the mean stream derivative

Source of record: `the November 2 reference manuscript`, line 399 (mean
velocity `\bar v₁ = -S_η`, from `v = ∇^⊥ψ`, i.e. `v₁ = -∂_ηψ`).

Route. For `s > 0` the stream `ψ s` is differentiable (`IsTrain.stream_differentiable`) and
`v s z = toVec (perpendicularGradient (ψ s) z)` (`IsTrain.stream`), so the first component of
the velocity is `-∂_ηψ`. Its continuity follows from the smoothness of `v` on `[0,∞) × ℝ²`
(`IsTrain.smooth_v`). Differentiation of the horizontal average under the integral over the
compact cell `(-c/2, c/2]` (dominated convergence on a compact `q`-interval times a
neighbourhood of `η`) gives `S_η = \overline{∂_ηψ} = -\bar v₁`.

The unconditional statement is `TrainMeanV1` (in `Sub/T01.lean`); no hypotheses are added.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (toVec toVec_zero)

/-! ### Differentiation of a horizontal average under the integral sign -/

/-- If `f` is continuous and its `η`-partial derivative is the continuous function `g`, then the
horizontal average `η ↦ \bar f(η)` has derivative `\bar g(η)`. -/
theorem trainMeanV1_hasDerivAt_hmean {c : ℝ} {f g : Plane → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hpart : ∀ q e : ℝ, HasDerivAt (fun y : ℝ => f (q, y)) (g (q, e)) e) (η : ℝ) :
    HasDerivAt (fun e : ℝ => hmean c f e) (hmean c g η) η := by
  unfold hmean
  refine HasDerivAt.const_smul c⁻¹ ?_
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (η - 1) (η + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have hline : ∀ e : ℝ, Continuous (fun q : ℝ => ((q, e) : Plane)) :=
    fun e => continuous_id.prodMk continuous_const
  have hc1 : ∀ e : ℝ, Continuous (fun q : ℝ => f (q, e)) :=
    fun e => hf.comp (hline e)
  have hc2 : ∀ e : ℝ, Continuous (fun q : ℝ => g (q, e)) :=
    fun e => hg.comp (hline e)
  have hbound : ∀ᵐ q ∂(volume.restrict (Ioc (-c / 2) (c / 2))),
      ∀ x ∈ Metric.ball η 1, ‖g (q, x)‖ ≤ M := by
    refine (ae_restrict_mem measurableSet_Ioc).mono fun q hq x hx => ?_
    rw [Real.ball_eq_Ioo] at hx
    exact hM (q, x) ⟨Ioc_subset_Icc_self hq, Ioo_subset_Icc_self hx⟩
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (-c / 2) (c / 2)))
    (F := fun e q => f (q, e)) (F' := fun e q => g (q, e))
    (x₀ := η) (bound := fun _ => M) (s := Metric.ball η 1)
    (Metric.ball_mem_nhds η one_pos)
    (Filter.Eventually.of_forall fun e => (hc1 e).aestronglyMeasurable)
    (hc1 η).integrableOn_Ioc
    (hc2 η).aestronglyMeasurable
    hbound
    (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) enorm_ne_top)
    (Filter.Eventually.of_forall fun q x _ => hpart q x)).2

/-- Linearity of the horizontal average under a sign change. -/
theorem trainMeanV1_hmean_neg (c : ℝ) (F : Plane → ℝ) (η : ℝ) :
    hmean c (fun z => -F z) η = -hmean c F η := by
  simp only [hmean, integral_neg, smul_neg]

/-! ### The statement `TrainMeanV1` -/

/-- **`PartI:T01/1`, `TrainMeanV1`** (source line 399): for `s > 0`, the horizontal average of the
first velocity component is `\bar v₁ = -S_η`, where `S = \bar ψ` is the mean stream. -/
theorem trainMeanV1 : TrainMeanV1 := by
  intro ν c _ _ tr s hs η
  have hψd : Differentiable ℝ (tr.ψ s) := tr.isTrain.stream_differentiable s hs.le
  -- continuity of the velocity on the slice `s > 0`
  have hvc : Continuous (fun z : Plane => tr.v s z) := by
    have hcont : ContinuousOn (fun x : ℝ × Plane => tr.v x.1 x.2) (Ici 0 ×ˢ univ) :=
      tr.isTrain.smooth_v.continuousOn
    have hmap : Continuous (fun z : Plane => ((s, z) : ℝ × Plane)) :=
      continuous_const.prodMk continuous_id
    exact hcont.comp_continuous hmap (fun z => ⟨hs.le, mem_univ z⟩)
  have hv0 : Continuous (fun z : Plane => tr.v s z 0) :=
    (PiLp.continuous_apply _ _ 0).comp hvc
  -- the `η`-partial derivative of the stream is `-v₁`
  have hpart : ∀ q e : ℝ,
      HasDerivAt (fun y : ℝ => tr.ψ s (q, y)) (-(tr.v s (q, e) 0)) e := by
    intro q e
    have hpath : HasDerivAt (fun y : ℝ => ((q, y) : Plane)) ((0 : ℝ), (1 : ℝ)) e :=
      (hasDerivAt_const e q).prodMk (hasDerivAt_id e)
    have hdiffAt : DifferentiableAt ℝ (fun y : ℝ => tr.ψ s (q, y)) e :=
      (hψd (q, e)).comp e hpath.differentiableAt
    have hval : tr.v s (q, e) 0 = -deriv (fun y : ℝ => tr.ψ s (q, y)) e := by
      rw [tr.isTrain.stream s hs.le (q, e), toVec_zero]
      rfl
    rw [hval, neg_neg]
    exact hdiffAt.hasDerivAt
  have key := trainMeanV1_hasDerivAt_hmean (c := c) (f := tr.ψ s)
    (g := fun z : Plane => -(tr.v s z 0)) hψd.continuous hv0.neg hpart η
  have hder : deriv (fun e => meanStream tr s e) η =
      hmean c (fun z : Plane => -(tr.v s z 0)) η :=
    key.deriv
  have hneg : hmean c (fun z : Plane => -(tr.v s z 0)) η =
      -hmean c (fun z : Plane => tr.v s z 0) η :=
    trainMeanV1_hmean_neg c (fun z : Plane => tr.v s z 0) η
  rw [hder, hneg, neg_neg]

end UnforcedLeray.Short.PartI
