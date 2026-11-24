import UnforcedLeray.Short.PartI.Sub.C02
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution.Exists
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution.SharpBoundContinuous
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution.Stability
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution.ContinuousApproximation

/-!
# Part I, task `PartI:C02`: the free diffusion-transport evolution (unconditional)

Source of record: `the November 2 reference manuscript`, lines 1014-1030
(proof of Lemma `lem:short-diffusion-complement`).

The four sub-lemmas of `Sub/C02.lean` are proved in the helper files
`Tasks/FreeDiffusionEvolution/{Exists,SharpBoundContinuous,Stability,ContinuousApproximation}.lean`:
`freeDiffusionEvolutionExists`, `freeDiffusionSharpBoundContinuous`, `freeDiffusionStability`,
`continuousApproximation`.  `exists_freeDiffusionEvolution_of` then gives the target, which is
the statement below.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Target `PartI:C02`** (well-formed reading; source lines 1014-1030): for every measurable
`0 ≤ β ≤ β_*` there is a free evolution `F` of `T - λ - βκ + βD` (`IsFreeDiffusionEvolution`)
whose norm satisfies `‖F(t,s)‖ ≤ exp(-Re λ (t-s) + |Re κ| β_* (t-s))` for `s ≤ t`. -/
theorem exists_freeDiffusionEvolution (lam kappa : ℂ) (βs : ℝ) {β : ℝ → ℝ} (hβm : Measurable β)
    (hβ : ∀ t, 0 ≤ β t ∧ β t ≤ βs) :
    ∃ F : ℝ → ℝ → B0010.XG →L[ℂ] B0010.XG, IsFreeDiffusionEvolution lam kappa β F ∧
      ∀ s t : ℝ, s ≤ t →
        ‖F t s‖ ≤ Real.exp (-(lam.re * (t - s)) + |kappa.re| * βs * (t - s)) :=
  exists_freeDiffusionEvolution_of freeDiffusionEvolutionExists freeDiffusionSharpBoundContinuous
    freeDiffusionStability continuousApproximation lam kappa βs β hβm hβ

end UnforcedLeray.Short.PartI
