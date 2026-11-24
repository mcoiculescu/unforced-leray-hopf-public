import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2.Defs

/-!
# Reduction of `R0SolenoidalInvariant` to the semigroup invariance `T0SolenoidalInvariant`

Source `the November 2 reference manuscript`
1650-1656.  `R0 μ u = ∫_{t>0} e^{-μt} T0(t) u dt` (`B0225.R0_apply`), so the resolvent preserves
the closed subspace `solenoidalHC 0 c` once each `T0(t)` does.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Lemma (semigroup invariance).** For `t > 0`, `T0(t) = B0225.T0` maps `solenoidalHC 0 c`
into itself (source 1650-1656: the flat heat semigroup `e^{tA0}`, `A0 = -S + ν s Δ_{q,η}`,
commutes with the flat Leray projection; the `(q,η)` heat factor is constant coefficient and
commutes with the divergence, the `s`-dilation `s ↦ s e^{-t}` preserves fibrewise orthogonality
to gradients). -/
def T0SolenoidalInvariant : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (t : ℝ), 0 < t →
    ∀ u : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      u ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c →
      UnforcedLeray.B0224.T0 hc ν t u ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c

theorem r0SolenoidalInvariant_of (hT : T0SolenoidalInvariant) : R0SolenoidalInvariant := by
  intro c ν hc μ hμ u hu
  have hint := UnforcedLeray.B0225.integrableOn_lapT0 hc ν hμ u
  rw [UnforcedLeray.B0225.R0_apply hc ν hμ]
  unfold UnforcedLeray.Short.PartIIa.solenoidalHC
  rw [Submodule.mem_orthogonal]
  intro g hg
  have hK : ∀ t : ℝ, 0 < t → inner ℂ g (UnforcedLeray.B0224.T0 hc ν t u) = 0 := fun t ht => by
    have := hT c ν hc t ht u hu
    unfold UnforcedLeray.Short.PartIIa.solenoidalHC at this
    exact Submodule.inner_right_of_mem_orthogonal hg this
  have h1 := integral_inner (𝕜 := ℂ) (μ := volume.restrict (Ioi (0:ℝ))) hint g
  change inner ℂ g (∫ t in Ioi (0:ℝ), UnforcedLeray.B0225.lapT0 hc ν μ u t) = 0
  rw [← h1]
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
  simp only [UnforcedLeray.B0225.lapT0]
  rw [inner_smul_right (𝕜 := ℂ), hK t ht, mul_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
