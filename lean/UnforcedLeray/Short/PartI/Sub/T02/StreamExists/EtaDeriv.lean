import UnforcedLeray.Short.PartI.Sub.T02_5
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Part I, task `PartI:T02/5`: `HasDerivAtEtaIntervalIntegral` (differentiation under the integral)

Source of record: `the November 2 reference manuscript`, lines 261-288 (calculus
step). The statement is `HasDerivAtEtaIntervalIntegral` from `Short/PartI/Sub/T02_5.lean`.

Route. For `f : Plane → ℝ` of class `C¹`, put `F x q = f (q, x)` and
`F' x q = fderiv ℝ f (q, x) (0, 1)`. Each slice `x ↦ f (q, x)` has derivative `F' x q`, the
derivative `F' x q` is bounded for `x` in a neighbourhood of `η` and `q` in `uIcc a b` (continuity of
`fderiv ℝ f` on a compact box), and `q ↦ F' η q` is continuous. Then
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` gives the derivative of the
integral. Finally `Cyl.partialEta f (q, η) = fderiv ℝ f (q, η) (0, 1)`.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **Lemma `HasDerivAtEtaIntervalIntegral`** (differentiation under the integral sign): for a `C¹`
function `f` on the plane, `η ↦ ∫_a^b f(q, η) dq` has derivative `∫_a^b ∂_η f(q, η) dq`
(source lines 261-288). -/
theorem hasDerivAtEtaIntervalIntegral : HasDerivAtEtaIntervalIntegral := by
  intro f hf a b η
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcont : Continuous (fun z : Plane => fderiv ℝ f z (0, 1)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- the slice derivative: `x ↦ f (q, x)` has derivative `fderiv ℝ f (q, x) (0, 1)` at `x`
  have hslice : ∀ q x : ℝ, HasDerivAt (fun y : ℝ => f (q, y)) (fderiv ℝ f (q, x) (0, 1)) x := by
    intro q x
    have h0 : HasDerivAt (fun y : ℝ => ((q, y) : Plane)) ((0 : ℝ), (1 : ℝ)) x :=
      (hasDerivAt_const x q).prodMk (hasDerivAt_id x)
    exact (hd (q, x)).hasFDerivAt.comp_hasDerivAt x h0
  -- uniform bound on the slice derivative over `uIcc a b × [η - 1, η + 1]`
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ uIcc a b ×ˢ Icc (η - 1) (η + 1), ‖fderiv ℝ f z (0, 1)‖ ≤ C :=
    (isCompact_uIcc.prod isCompact_Icc).exists_bound_of_continuousOn hcont.continuousOn
  have hcontq : ∀ x : ℝ, Continuous (fun q : ℝ => f (q, x)) := fun x =>
    hf.continuous.comp (continuous_id.prodMk continuous_const)
  have hcontd : Continuous (fun q : ℝ => fderiv ℝ f (q, η) (0, 1)) :=
    hcont.comp (continuous_id.prodMk continuous_const)
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ Ioo (η - 1) (η + 1),
      ‖fderiv ℝ f (t, x) (0, 1)‖ ≤ C := by
    refine Filter.Eventually.of_forall fun t ht x hx => hC (t, x) ⟨?_, ?_⟩
    · exact Set.uIoc_subset_uIcc ht
    · exact Ioo_subset_Icc_self hx
  have hdiff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc a b → ∀ x ∈ Ioo (η - 1) (η + 1),
      HasDerivAt (fun y => f (t, y)) (fderiv ℝ f (t, x) (0, 1)) x :=
    Filter.Eventually.of_forall fun t _ x _ => hslice t x
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun x q => f (q, x)) (F' := fun x q => fderiv ℝ f (q, x) (0, 1))
    (x₀ := η) (s := Ioo (η - 1) (η + 1)) (bound := fun _ => C) (a := a) (b := b)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun x => (hcontq x).aestronglyMeasurable)
    ((hcontq η).intervalIntegrable a b)
    hcontd.aestronglyMeasurable
    hbound intervalIntegrable_const hdiff
  -- `Cyl.partialEta f (q, η)` is by definition the η-derivative of the slice `x ↦ f (q, x)`
  have hpe : ∀ q : ℝ, Cyl.partialEta f (q, η) = fderiv ℝ f (q, η) (0, 1) :=
    fun q => (hslice q η).deriv
  simp only [hpe]
  exact key.2

end UnforcedLeray.Short.PartI
