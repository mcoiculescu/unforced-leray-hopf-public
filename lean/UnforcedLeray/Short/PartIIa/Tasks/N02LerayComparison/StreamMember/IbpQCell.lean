import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestFderiv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.BandIntegrable
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IntegralDerivPeriodic
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.PartialDerivSlice
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CellFubiniQ

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.
Target: `IbpQCell` (`Sub/N02_2.lean`): for a complex band test `F`,
`∫_{cell} s^{-3/2} ∂_q F = 0`.

Route: `pdQ F` is a complex band test (`CTestFderiv`), so the weighted integrand is integrable on
the cell (`BandIntegrable`). `CellFubiniQ` writes the cell integral with `q` innermost. For fixed
`(s, η)` the weight is a constant factor of the `q`-integral (`integral_const_mul`), and
`∫_{(0,c]} ∂_q F(s, q, η) = 0` by `IntegralDerivPeriodic` applied to `t ↦ F(s, t, η)`, which is
smooth and `c`-periodic.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **`q`-integration by parts with the weight** (task `PartII-a:N02/2/15`): for a complex band
test `F`, `∫_{cell} s^{-3/2} ∂_q F = 0`. -/
theorem ibpQCell : UnforcedLeray.Short.PartIIa.IbpQCell := by
  intro c F hF
  -- the `q`-derivative of a complex band test is a complex band test, hence the weighted
  -- integrand is integrable on the cell
  have hPq : IsCTest c (pdQ F) := cTestFderiv c F hF (0, 1, 0)
  have hG : IntegrableOn (fun p : Profile => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ F p)
      (cell c) :=
    (bandIntegrable c (pdQ F) hPq).2
  -- the `q`-integral over one period of the derivative of a periodic function vanishes
  have hline : ∀ s η : ℝ, ∫ q in Ioc (0 : ℝ) c, pdQ F (s, q, η) = 0 := by
    intro s η
    have hmap : ContDiff ℝ ∞ (fun t : ℝ => ((s, t, η) : Profile)) :=
      contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
    have hh : ContDiff ℝ ∞ (fun t : ℝ => F (s, t, η)) := hF.smooth.comp hmap
    have hper : ∀ t : ℝ, F (s, t + c, η) = F (s, t, η) := fun t => hF.periodic (s, t, η)
    have hd : ∀ q : ℝ, pdQ F (s, q, η) = deriv (fun t : ℝ => F (s, t, η)) q :=
      fun q => (partialDerivSlice F hF.smooth s q η).2.1
    simp only [hd]
    exact integralDerivPeriodic c _ hh hper
  -- the weight is constant in `q`, so the inner integral vanishes for each `(s, η)`
  have hq : ∀ s η : ℝ, ∫ q in Ioc (0 : ℝ) c, ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ F (s, q, η) = 0 := by
    intro s η
    rw [integral_const_mul, hline s η, mul_zero]
  have hs : ∀ s : ℝ, ∫ η : ℝ, ∫ q in Ioc (0 : ℝ) c,
      ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ F (s, q, η) = 0 := by
    intro s
    simp only [hq s, integral_zero]
  -- Fubini on the cell with `q` innermost, then the vanishing slices
  refine (cellFubiniQ c _ hG).trans ?_
  show ∫ s in Ioi (0 : ℝ), ∫ η : ℝ, ∫ q in Ioc (0 : ℝ) c,
      ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdQ F (s, q, η) = 0
  simp only [hs, integral_zero]

end UnforcedLeray.Short.PartIIa
