import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelRegularityReg
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB1
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB34
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB5
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB6

/-!
# `PartIII-a:T21/c3/2/1/2/2`: leaf B (`RelBlockRegularityReg`) in the source regime

Source of record: `the November 2 reference manuscript` (SP), lines 2941-2970
(strong continuity of the periodized relative free evolution) and 2974-2982 (the interaction
`A_rel` is bounded for `b ≥ b_prop`, `ν ≤ ν_prop(b)`).

`relBlockRegularityReg` is assembled from the accepted leaves `relB1_leaf` (uniform bound of
`F_rel` on the block triangle), `relB4s_leaf` (strong continuity of a pinned, uniformly bounded
`F_rel`), `relB5_leaf` (`RelB5Reg`, the regime bound of `A_rel`) and `relB6_leaf` (strong
measurability of `A_rel` via the dense smooth class).  The continuity clause uses `RelB4s` (the
corrected leaf of `RelRegularityOrg2`), not the superseded `RelB34`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIIa

namespace RelRegularityFinal

open VariationOfConstantsMildSub

/-- Regime form of `RelRegularityOrg2.relBlockRegularity_of'`: leaf B from `RelB1`, `RelB4s`,
`RelB5Reg`, `RelB6`. -/
theorem relBlockRegularityReg_of_B4s (κ : PlanarFrameKernels)
    (h1 : RelRegularityOrg.RelB1 κ) (h4 : RelRegularityOrg2.RelB4s κ)
    (h5 : RelRegularityOrg.RelB5Reg κ) (h6 : RelRegularityOrg.RelB6 κ) :
    RelBlockRegularityReg κ := by
  intro hκ P hP m hm K B hB
  obtain ⟨b₀, hb₀⟩ := h5 hκ P hP m hm K B hB
  refine ⟨b₀, fun b hb hb1 => ?_⟩
  obtain ⟨ν₀, hν₀, h5'⟩ := hb₀ b hb hb1
  refine ⟨ν₀, hν₀, fun ν hν hνle hF tr htr t₁ t₂ ht₁ ht₁₂ hbt hBz F_rel A_rel hFp hAp => ?_⟩
  have ctx : RelRegularityOrg.RelCtx κ P m K B b ν tr t₁ t₂ :=
    ⟨hκ, hP, hm, hB, hb1, hν, hF, htr, ht₁, ht₁₂, hbt, hBz⟩
  refine ⟨fun x => ?_, fun x => ?_, h5' ν ⟨hν, hνle⟩ tr t₁ t₂ ctx A_rel hAp⟩
  · exact h4 P m K B b ν tr t₁ t₂ ctx F_rel hFp (h1 P m K B b ν tr t₁ t₂ ctx F_rel hFp) x
  · exact RelRegularityOrg.aestronglyMeasurable_of_dense _ A_rel
      (RelRegularityOrg.relSmoothClass m) (h6.2 m hm)
      (fun W hW => h6.1 P m K B b ν tr t₁ t₂ ctx A_rel hAp W hW) x

end RelRegularityFinal

end UnforcedLeray.Short.IIIa

/-- **Leaf B in the source regime (`PartIII-a:T21/c3/2/1/2/2`, SP 2941-2982).** -/
theorem relBlockRegularityReg (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.VariationOfConstantsMildSub.RelBlockRegularityReg κ :=
  UnforcedLeray.Short.IIIa.RelRegularityFinal.relBlockRegularityReg_of_B4s κ (relB1_leaf κ)
    (relB4s_leaf κ) (UnforcedLeray.Short.IIIa.RelRegularityOrg.relB5_leaf κ)
    (UnforcedLeray.Short.IIIa.RelRegularityOrg.relB6_leaf κ)
