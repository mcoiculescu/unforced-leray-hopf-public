import UnforcedLeray.Short.PartI.Sub.C03
import UnforcedLeray.Cons.L2.CanonicalBranch.DysonStability
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution.Exists
import UnforcedLeray.Short.PartI.Tasks.ComplementBlockLimit.StrongSmall.Blocks

/-!
# Target `PartI:C03/2`: `freeStrongSmall`

Source of record: `the November 2 reference manuscript`, lines 1031-1034
("`exp(D int_s^t beta) -> I` strongly as `beta_* -> 0`, uniformly over all admissible
coefficients; the Dyson series give the direct strong limits of the free evolutions").

Method. Fix `lam, kappa, B, x, eps`. The helper
`exists_delta_canonicalTransportDysonFamily_uniform_strong_small_blocks` (`StrongSmall/Blocks.lean`,
a copy of `Cons` `DysonStability.lean:966` with the block quantified after `∃ δ`) gives one `δ`
for all blocks `[s, s+B]`. For a measurable `0 ≤ β ≤ δ` and a free evolution `F`, `F` agrees on
`[s, s+B]` with the Dyson family of the block `[s, s+B]` (`dyson_unique`, as in
`Tasks/FreeDiffusionEvolution/SharpBoundContinuous.lean`), and the limit family evaluates to
`exp((t-s)(T-λ))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Target `PartI:C03/2`** (source lines 1031-1034): uniform strong convergence of the free
evolutions to `exp((t-s)(T-λ))` on blocks of length `B`, with a threshold `δ` independent of `s`,
`β` and `F`. -/
theorem freeStrongSmall : FreeStrongSmall := by
  intro lam kappa B x ε hB hε
  obtain ⟨δ, hδ, hsmall⟩ :=
    UnforcedLeray.Cons.G3b.exists_delta_canonicalTransportDysonFamily_uniform_strong_small_blocks
      hB lam kappa x hε
  refine ⟨δ, hδ, ?_⟩
  intro β hβm hβ F hF s t hst hts
  have hβ0 : ∀ r, 0 ≤ β r := fun r => (hβ r).1
  have hβM : ∀ r, |β r| ≤ δ := fun r => by
    rw [abs_of_nonneg (hβ r).1]
    exact (hβ r).2
  have hβi : ∀ u v, IntervalIntegrable β volume u v :=
    fun u v => fdeAux_intervalIntegrable hβm hβ u v
  have hβsm : AEStronglyMeasurable β (volume.restrict (Set.Icc s (s + B))) :=
    hβm.aestronglyMeasurable
  have hβblock : ∃ C₀ : ℝ, ∀ r ∈ Set.Icc s (s + B), |β r| ≤ C₀ := ⟨δ, fun r _ => hβM r⟩
  have hid : F t s = (UnforcedLeray.Cons.G3b.canonicalTransportDysonFamily lam kappa β hβi hβ0
      δ hβM hβsm hβblock).U t s := by
    refine UnforcedLeray.Evolution.dyson_unique
      (UnforcedLeray.Cons.G3b.freeDiffusionFamily (a := s) (b := s + B) β hβi hβ0 δ hβM)
      (UnforcedLeray.Cons.G3b.transportDysonPert ((-2 * Complex.I) • UnforcedLeray.B0012.omegaOp)
        lam kappa β s (s + B) hβsm hβblock)
      F ?_ ?_ s t le_rfl hst hts
    · intro s' _ _ y
      exact (hF.cont y s').mono Set.Icc_subset_Ici_self
    · intro s' τ _ hs'τ _ y
      exact hF.duhamel s' τ hs'τ y
  have hlim : (UnforcedLeray.Cons.G3b.canonicalTransportLimitFamily (a := s) (b := s + B) lam).U
      t s x = NormedSpace.exp (((t - s : ℝ) : ℂ) • freeLimitGen lam) x := by
    simp [UnforcedLeray.Cons.G3b.canonicalTransportLimitFamily,
      UnforcedLeray.Evolution.EvolutionFamily.ofExpSemigroup_U,
      UnforcedLeray.Infra.ExpSemigroup.ofExp_T, freeLimitGen, complementT,
      UnforcedLeray.Cons.G3b.canonicalTransportLimitGenerator]
  have key := hsmall s (s + B) β hβi hβ0 hβsm hβM s t le_rfl hst hts (by linarith)
  rw [hid, ← hlim]
  exact key

end UnforcedLeray.Short.PartI
