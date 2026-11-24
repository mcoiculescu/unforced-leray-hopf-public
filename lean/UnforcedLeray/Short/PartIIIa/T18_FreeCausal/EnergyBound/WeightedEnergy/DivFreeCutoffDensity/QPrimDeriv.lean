import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.DivFreeCutoffDensity.QPrimSmooth

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/2`: derivatives of `q`-primitives and `q`-integrals

Target (`Sub/T18_3_1_1.lean`): `DfcQPrimDeriv`. Source of record:
`the November 2 reference manuscript`, lines 3541-3552.

## Mathematics

For `g` differentiable at `(q, η)`, the partial derivatives are one-variable derivatives of slices
(`pd0_eq`, `pd1_eq`), via the chain rule with `s ↦ (s, η)` and `t ↦ (q, t)`.

* `∂_q dfcQPrim c f = f`: the slice `s ↦ ∫_{-c/2}^{s} f(t, η) dt` has derivative `f(q, η)` at `q`
  (fundamental theorem of calculus, continuous integrand).
* `∂_η dfcQPrim c f (q, η) = ∫_{-c/2}^{q} ∂_η f(t, η) dt` and
  `d/dη dfcQInt c f = ∫_{-c/2}^{c/2} ∂_η f(t, η) dt`: both are instances of `hasDerivAt_param`,
  differentiation of `η ↦ ∫_a^b f(t, η) dt` under the integral sign over a compact interval.
  The domination bound is the sup of `|∂_η f|` over `[a,b] × closedBall η₀ 1`.

The hypothesis `0 < c` is used only through `dfcQPrimSmooth` (smoothness of `dfcQPrim c f`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace DfcQPrimDerivAux

/-- A `∂_q` partial derivative is the derivative of the slice `s ↦ g (s, η)`. -/
theorem pd0_eq (g : ℝ × ℝ → ℝ) (q η : ℝ) (hg : DifferentiableAt ℝ g (q, η)) :
    B0579.pd 0 g (q, η) = deriv (fun s : ℝ => g (s, η)) q := by
  have hd : HasDerivAt (fun s : ℝ => g (s, η)) (fderiv ℝ g (q, η) (1, 0)) q :=
    hg.hasFDerivAt.comp_hasDerivAt q ((hasDerivAt_id q).prodMk (hasDerivAt_const q η))
  rw [hd.deriv]
  simp [B0579.pd, B0579.dir]

/-- A `∂_η` partial derivative is the derivative of the slice `t ↦ g (q, t)`. -/
theorem pd1_eq (g : ℝ × ℝ → ℝ) (q η : ℝ) (hg : DifferentiableAt ℝ g (q, η)) :
    B0579.pd 1 g (q, η) = deriv (fun t : ℝ => g (q, t)) η := by
  have hd : HasDerivAt (fun t : ℝ => g (q, t)) (fderiv ℝ g (q, η) (0, 1)) η :=
    hg.hasFDerivAt.comp_hasDerivAt η ((hasDerivAt_const η q).prodMk (hasDerivAt_id η))
  rw [hd.deriv]
  simp [B0579.pd, B0579.dir]

/-- Differentiation of a parametric integral over a fixed interval in the parameter `η`. -/
theorem hasDerivAt_param (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (a b η₀ : ℝ) :
    HasDerivAt (fun η : ℝ => ∫ t in a..b, f (t, η))
      (∫ t in a..b, B0579.pd 1 f (t, η₀)) η₀ := by
  have hfc : Continuous f := hf.continuous
  have hpd : Continuous (fun z : ℝ × ℝ => B0579.pd 1 f z) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨C, hC⟩ := ((isCompact_uIcc (a := a) (b := b)).prod
    (isCompact_closedBall η₀ 1)).exists_bound_of_continuousOn hpd.continuousOn
  have hFc : ∀ η : ℝ, Continuous fun t : ℝ => f (t, η) := fun η =>
    hfc.comp (continuous_id.prodMk continuous_const)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun η t => f (t, η)) (F' := fun η t => B0579.pd 1 f (t, η))
    (x₀ := η₀) (s := Metric.ball η₀ 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds η₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun η => (hFc η).aestronglyMeasurable
  · exact (hFc η₀).intervalIntegrable a b
  · exact (hpd.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht η hη => ?_
    exact hC (t, η) ⟨Set.uIoc_subset_uIcc ht, Metric.ball_subset_closedBall hη⟩
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t _ η _ => ?_
    have hd : HasDerivAt (fun η : ℝ => f (t, η)) (fderiv ℝ f (t, η) (0, 1)) η :=
      ((hf.differentiable (by simp)) (t, η)).hasFDerivAt.comp_hasDerivAt η
        ((hasDerivAt_const η t).prodMk (hasDerivAt_id η))
    have h2 : B0579.pd 1 f (t, η) = fderiv ℝ f (t, η) (0, 1) := by
      simp [B0579.pd, B0579.dir]
    rw [h2]
    exact hd

end DfcQPrimDerivAux

open DfcQPrimDerivAux in
/-- Target: `DfcQPrimDeriv` (`Sub/T18_3_1_1.lean`, `PartIII-a:T18/3/1/1/2`). -/
theorem dfcQPrimDeriv : UnforcedLeray.Short.IIIa.DfcQPrimDeriv := by
  unfold DfcQPrimDeriv
  intro c hc f hf
  obtain ⟨hG, _⟩ := dfcQPrimSmooth c hc f hf
  have hGd : Differentiable ℝ (dfcQPrim c f) := hG.differentiable (by simp)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨q, η⟩ := x
    rw [pd0_eq _ q η (hGd _)]
    have hfc : Continuous fun t : ℝ => f (t, η) :=
      hf.continuous.comp (continuous_id.prodMk continuous_const)
    have hfun : (fun s : ℝ => dfcQPrim c f (s, η)) = fun s : ℝ => ∫ t in (-(c / 2))..s, f (t, η) :=
      rfl
    rw [hfun]
    exact (intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable _ _)
      (hfc.stronglyMeasurableAtFilter _ _) hfc.continuousAt).deriv
  · intro x
    obtain ⟨q, η⟩ := x
    rw [pd1_eq _ q η (hGd _)]
    exact (hasDerivAt_param f hf (-(c / 2)) q η).deriv
  · intro η
    exact (hasDerivAt_param f hf (-(c / 2)) (c / 2) η).deriv

end UnforcedLeray.Short.IIIa
