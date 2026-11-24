import UnforcedLeray.Short.PartI.Sub.C02
import UnforcedLeray.Cons.L2.CanonicalBranch.DysonLimit

/-!
# Part I, task `PartI:C02`, sub-lemma 2: the sharp bound for continuous `β`

Source of record: `the November 2 reference manuscript`, lines 1024-1028.
For continuous `0 ≤ β ≤ β_*`, every free evolution `F` of `IsFreeDiffusionEvolution` satisfies
`‖F(t,s)‖ ≤ exp(-Re λ (t-s) + |Re κ| β_* (t-s))`.

Proof: on the block `[s,t]` the evolution `F` is the Dyson family (`dyson_unique`, using
`hF.cont` and `hF.duhamel`), and the energy estimate
`canonicalTransportDysonFamily_sharp_norm_le` (`δ := β_*`) bounds it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

theorem freeDiffusionSharpBoundContinuous : FreeDiffusionSharpBoundContinuous := by
  unfold FreeDiffusionSharpBoundContinuous
  intro lam kappa βs β hβc hβ F hF s t hst
  have hβ0 : ∀ r, 0 ≤ β r := fun r => (hβ r).1
  have hβs0 : 0 ≤ βs := (hβ 0).1.trans (hβ 0).2
  have hβM : ∀ r, |β r| ≤ βs := fun r => by
    rw [abs_of_nonneg (hβ r).1]
    exact (hβ r).2
  have hβi : ∀ r u, IntervalIntegrable β volume r u :=
    fun r u => hβc.intervalIntegrable r u
  have hβsm : AEStronglyMeasurable β (volume.restrict (Icc s t)) :=
    hβc.aestronglyMeasurable
  have hβblock : ∃ C : ℝ, ∀ r ∈ Icc s t, |β r| ≤ C := ⟨βs, fun r _ => hβM r⟩
  have hid : F t s = (UnforcedLeray.Cons.G3b.canonicalTransportDysonFamily lam kappa β hβi hβ0
      βs hβM hβsm hβblock).U t s := by
    refine UnforcedLeray.Evolution.dyson_unique
      (UnforcedLeray.Cons.G3b.freeDiffusionFamily (a := s) (b := t) β hβi hβ0 βs hβM)
      (UnforcedLeray.Cons.G3b.transportDysonPert ((-2 * Complex.I) • UnforcedLeray.B0012.omegaOp)
        lam kappa β s t hβsm hβblock)
      F ?_ ?_ s t le_rfl hst le_rfl
    · intro s' _ _ x
      exact (hF.cont x s').mono Icc_subset_Ici_self
    · intro s' τ _ hs'τ _ x
      exact hF.duhamel s' τ hs'τ x
  have hsharp : ∀ x : UnforcedLeray.B0010.XG,
      ‖F t s x‖ ≤ Real.exp ((-lam.re + βs * |kappa.re|) * (t - s)) * ‖x‖ := by
    intro x
    rw [hid]
    exact UnforcedLeray.Cons.G3b.canonicalTransportDysonFamily_sharp_norm_le
      (a := s) (b := t) (s := s) (t := t) (δ := βs) lam kappa β hβc.continuousOn hβi hβ0 βs
      hβM hβsm hβblock (fun r _ => (hβ r).2) hβs0 le_rfl hst le_rfl x
  have hopn : ‖F t s‖ ≤ Real.exp ((-lam.re + βs * |kappa.re|) * (t - s)) :=
    ContinuousLinearMap.opNorm_le_bound (F t s) (Real.exp_pos _).le hsharp
  have harg : (-lam.re + βs * |kappa.re|) * (t - s)
      = -(lam.re * (t - s)) + |kappa.re| * βs * (t - s) := by
    ring
  rw [harg] at hopn
  exact hopn

end UnforcedLeray.Short.PartI
