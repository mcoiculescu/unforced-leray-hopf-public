import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_of

/-!
# `R0SolenoidalInvariant` and reduction (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1/2`)

Source `the November 2 reference manuscript`
1650-1656: `T0flat = R0 ∘ P0`, where `P0 = PepsC 0 c` is the orthogonal projection onto
`solenoidalHC 0 c`.  The reduction below is proved here.  What remains open is the invariance
`R0SolenoidalInvariant` (the resolvent `B0225.R0` maps the exact solenoidal subspace into itself;
no lemma in `Units/B0225/*` or `Short/PartII-a` provides it).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Lemma.** `R0 = B0225.R0` maps `solenoidalHC 0 c` into itself (source
`the November 2 reference manuscript` 1650-1656:
the range of the flat Leray projection is invariant under `A0`, hence under its resolvent). -/
def R0SolenoidalInvariant : Prop :=
  ∀ (c ν : ℝ) (hc : 0 < c) (μ : ℂ), 0 < μ.re + 1 / 4 →
    ∀ u : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      u ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c →
      UnforcedLeray.B0225.R0 hc ν μ u ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c

/-- The reduction of `FlatResSol` to the open input (proved). -/
theorem flatResSol_of (hR : R0SolenoidalInvariant) : FlatResSol := by
  intro c ν hc μ _hν hμ f
  have hm : UnforcedLeray.Short.PartIIa.PepsC 0 c f ∈
      UnforcedLeray.Short.PartIIa.solenoidalHC 0 c := by
    unfold UnforcedLeray.Short.PartIIa.PepsC
    exact Submodule.starProjection_apply_mem _ f
  exact hR c ν hc μ hμ _ hm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
