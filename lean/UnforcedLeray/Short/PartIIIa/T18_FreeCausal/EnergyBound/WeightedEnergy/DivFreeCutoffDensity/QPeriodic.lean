import UnforcedLeray.Short.PartIIIa.Sub.T18_3_1_1

/-!
# Part III-a, task `PartIII-a:T18/3/1/1/3`: periodicity of `q`-integrals and `q`-primitives

Target: `DfcQPeriodic` (`Sub/T18_3_1_1.lean`). Source of record:
`the November 2 reference manuscript`, lines 3541-3552 (density of the `H¹`
divergence-free test fields; the stream-function argument recorded in the docstring of
`Sub/T18_3_1_1.lean`).

## Mathematics

Let `c > 0` (the positivity is not needed), and let `f` be smooth and `c`-periodic in `q`.

(a) For fixed `η`, the slice `t ↦ f(t, η)` has derivative `∂_q f(t, η)` at `t`. By the
fundamental theorem of calculus,
`∫_{-c/2}^{c/2} ∂_q f(t, η) dt = f(c/2, η) - f(-c/2, η)`, and this is `0` because
`c/2 = -c/2 + c` and `f` is `c`-periodic.

(b) Suppose `∫_{-c/2}^{c/2} f(t, η) dt = 0` for every `η`. Fix `x`. The slice `g = f(·, x.2)` is
`c`-periodic and continuous, so
`∫_{-c/2}^{x.1 + c} g = ∫_{-c/2}^{x.1} g + ∫_{-c/2}^{-c/2 + c} g`
(`Function.Periodic.intervalIntegral_add_eq_add`), and `-c/2 + c = c/2`. The last integral is the
one-period integral, which vanishes by hypothesis. Hence the primitive is `c`-periodic in `q`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem dfcQPeriodic : UnforcedLeray.Short.IIIa.DfcQPeriodic := by
  unfold UnforcedLeray.Short.IIIa.DfcQPeriodic
  intro c _hc f hf hper
  have hcf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hcont : Continuous f := hf.continuous
  -- the `q`-slice of `f` has derivative `∂_q f`
  have hslope : ∀ η t : ℝ, HasDerivAt (fun s : ℝ => f (s, η)) (B0579.pd 0 f (t, η)) t := by
    intro η t
    have h1 : HasFDerivAt f (fderiv ℝ f (t, η)) ((fun s : ℝ => (s, η)) t) :=
      ((hf.differentiable (by simp)) (t, η)).hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => (s, η)) ((1 : ℝ), (0 : ℝ)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t η)
    exact h1.comp_hasDerivAt t h2
  have hpdcont : Continuous (fun x => B0579.pd 0 f x) := hcf.clm_apply continuous_const
  have hpdslice : ∀ η : ℝ, Continuous (fun t : ℝ => B0579.pd 0 f (t, η)) := fun η =>
    hpdcont.comp (continuous_id.prodMk continuous_const)
  refine ⟨fun η => ?_, fun hint x => ?_⟩
  · -- (a) the one-period integral of `∂_q f` vanishes
    have hFTC : ∫ t in (-(c / 2))..(c / 2), B0579.pd 0 f (t, η) =
        f (c / 2, η) - f (-(c / 2), η) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hslope η t)
        ((hpdslice η).intervalIntegrable _ _)
    have hper' : f (-(c / 2) + c, η) = f (-(c / 2), η) := hper (-(c / 2), η)
    have e : -(c / 2) + c = c / 2 := by ring
    rw [e] at hper'
    unfold dfcQInt
    rw [hFTC, hper', sub_self]
  · -- (b) the primitive is `c`-periodic in `q` when the one-period integral vanishes
    have hslice : Continuous (fun t : ℝ => f (t, x.2)) :=
      hcont.comp (continuous_id.prodMk continuous_const)
    have hperslice : Function.Periodic (fun t : ℝ => f (t, x.2)) c := fun t => hper (t, x.2)
    have hsplit : ∫ t in (-(c / 2))..(x.1 + c), f (t, x.2) =
        (∫ t in (-(c / 2))..x.1, f (t, x.2)) + ∫ t in (-(c / 2))..(-(c / 2) + c), f (t, x.2) :=
      hperslice.intervalIntegral_add_eq_add (-(c / 2)) x.1
        (fun a b => hslice.intervalIntegrable a b)
    have e : -(c / 2) + c = c / 2 := by ring
    rw [e] at hsplit
    have h0 : ∫ t in (-(c / 2))..(c / 2), f (t, x.2) = 0 := hint x.2
    show (∫ t in (-(c / 2))..(x.1 + c), f (t, x.2)) = ∫ t in (-(c / 2))..x.1, f (t, x.2)
    rw [hsplit, h0, add_zero]

end UnforcedLeray.Short.IIIa
