import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.MildSplit
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.DuhamelAbstract.Core

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/2/1`: leaf A `DuhamelVoCAbstract`

Source of record: `the November 2 reference manuscript` (SP), lines 2962-2982
(variation of constants for the block Duhamel evolution).

`duhamelVoCAbstract` proves `VariationOfConstantsMildSub.DuhamelVoCAbstract`: for a
`B0104.IsDuhamelEvolution` `U` of `(F, A)` on one block, with `F` strongly continuous on the block
triangle and `A` strongly measurable and bounded on `[0, B]`, a bounded measurable mild solution
`Y(τ) = F(τ,0) Y(0) + ∫₀^τ F(τ,σ) (A(σ) Y(σ) + G(σ)) dσ` with integrable forcing `G` satisfies
`Y(B) = U(B,0) Y(0) + ∫₀^B U(B,σ) G(σ) dσ`.

The proof is `DuhamelAbstractSub.duhamelVoC_core` (`DuhamelAbstract/Core.lean`): Banach-Steinhaus
and Gronwall bounds and joint strong continuity of `U` (`Regularity.lean`, `Continuity.lean`),
Carathéodory composition (`Measurability.lean`), Fubini on the triangle, and Gronwall uniqueness for
`Y - Z`, `Z(τ) = U(τ,0) Y(0) + ∫₀^τ U(τ,σ) G(σ) dσ`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **Leaf A (`DuhamelVoCAbstract`)**, SP 2962-2982: inhomogeneous variation of constants for a
`B0104.IsDuhamelEvolution` on one block. -/
theorem duhamelVoCAbstract : UnforcedLeray.Short.IIIa.VariationOfConstantsMildSub.DuhamelVoCAbstract := by
  intro H _ _ _ B F A U hB hU hFc hAm hAb Y G hYm hYb hGi hY
  exact DuhamelAbstractSub.duhamelVoC_core B F A U hB hU hFc hAm hAb Y G hYm hYb hGi hY

end UnforcedLeray.Short.IIIa
