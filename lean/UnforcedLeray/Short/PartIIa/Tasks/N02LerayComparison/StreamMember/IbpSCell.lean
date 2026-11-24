import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestFderiv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.BandIntegrable
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IntegralDerivZero
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.PartialDerivSlice
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CellFubiniS

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.
Target: `IbpSCell` (`Sub/N02_2.lean`): for every complex band test `G`, `∫_{cell c} ∂_s G = 0`.

## Route

`pdS G` is a complex band test (`cTestFderiv`), hence integrable on the cell (`bandIntegrable`).
Fubini with `s` innermost (`cellFubiniS`) reduces the cell integral to
`∫_{q ∈ (0,c]} ∫_η ∫_{s ∈ (0,∞)} ∂_s G(s,q,η)`. For fixed `(q, η)`, the inner integral is
`∫_{(0,∞)} deriv (t ↦ G(t,q,η))` (`partialDerivSlice`), which vanishes by `integralDerivZero`
since `t ↦ G(t,q,η)` is supported in the band `[s₀, s₁]` with `0 < s₀`.

No helpers beyond the imported leaves are needed.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **Target `PartII-a:N02/2/13`**: `IbpSCell`, for every complex band test `G`, the cell integral
of `∂_s G` vanishes. -/
theorem ibpSCell : UnforcedLeray.Short.PartIIa.IbpSCell := by
  intro c G hG
  obtain ⟨s0, s1, L, hs0, hband⟩ := hG.band
  -- `∂_s G` is a complex band test, hence integrable on the cell
  have hH : IsCTest c (pdS G) := cTestFderiv c G hG (1, 0, 0)
  have hInt : IntegrableOn (pdS G) (cell c) := (bandIntegrable c (pdS G) hH).1
  refine (cellFubiniS c (pdS G) hInt).trans ?_
  -- for fixed `(q, η)`, the `s`-integral of `∂_s G` over `(0, ∞)` vanishes
  have hinner : ∀ q η : ℝ, ∫ s in Ioi (0 : ℝ), pdS G (s, q, η) = 0 := by
    intro q η
    have hf : ContDiff ℝ ∞ (fun t : ℝ => ((t, q, η) : Profile)) :=
      contDiff_id.prodMk (contDiff_const.prodMk contDiff_const)
    have hh : ContDiff ℝ ∞ (fun t : ℝ => G (t, q, η)) := hG.smooth.comp hf
    have hsupp : ∀ t : ℝ, G (t, q, η) ≠ 0 → t ∈ Icc s0 s1 :=
      fun t ht => (hband (t, q, η) ht).1
    have hS : ∀ s : ℝ, pdS G (s, q, η) = deriv (fun t : ℝ => G (t, q, η)) s :=
      fun s => (partialDerivSlice G hG.smooth s q η).1
    simp only [hS]
    exact (integralDerivZero _ hh s0 s1 hsupp).2 0 hs0.le
  simp only [hinner, integral_zero]

end UnforcedLeray.Short.PartIIa
