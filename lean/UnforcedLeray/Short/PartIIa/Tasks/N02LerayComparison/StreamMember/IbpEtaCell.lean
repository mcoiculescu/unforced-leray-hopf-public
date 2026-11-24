import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CTestFderiv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.BandIntegrable
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.IntegralDerivZero
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.PartialDerivSlice
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CellFubiniEta

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.
Target: `IbpEtaCell` (`Sub/N02_2.lean`): for a complex band test `F`,
`∫_{cell} s^{-3/2} ∂_η F = 0`.

Route: `pdEta F` is a complex band test (`CTestFderiv`), so the weighted integrand is integrable on
the cell (`BandIntegrable`). `CellFubiniEta` writes the cell integral as an iterated integral with
`η` innermost. For fixed `(s, q)` the weight is a constant factor of the `η`-integral
(`integral_const_mul`), and `∫ η, ∂_η F(s, q, η) = 0` by `IntegralDerivZero` applied to
`t ↦ F(s, q, t)`, which is smooth and vanishes outside `[-L, L]`. The slice identity
`∂_η F(s,q,η) = d/dt F(s,q,t)|_{t = η}` is `PartialDerivSlice`.

Helpers (prefix `iec`): none needed beyond the leaves; the statement is proved directly.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **`η`-integration by parts with the weight** (task `PartII-a:N02/2/14`): for a complex band
test `F`, `∫_{cell} s^{-3/2} ∂_η F = 0`. -/
theorem ibpEtaCell : UnforcedLeray.Short.PartIIa.IbpEtaCell := by
  intro c F hF
  obtain ⟨_, _, L, _, hb⟩ := hF.band
  -- the `η`-derivative of a complex band test is a complex band test, hence the weighted
  -- integrand is integrable on the cell
  have hPe : IsCTest c (pdEta F) := cTestFderiv c F hF (0, 0, 1)
  have hG : IntegrableOn (fun p : Profile => ((p.1 ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdEta F p)
      (cell c) :=
    (bandIntegrable c (pdEta F) hPe).2
  -- the `η`-integral over a line vanishes: the derivative of a compactly supported smooth
  -- function integrates to zero
  have hline : ∀ s q : ℝ, ∫ η : ℝ, pdEta F (s, q, η) = 0 := by
    intro s q
    have hmap : ContDiff ℝ ∞ (fun t : ℝ => ((s, q, t) : Profile)) :=
      contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
    have hsm : ContDiff ℝ ∞ (fun t : ℝ => F (s, q, t)) := hF.smooth.comp hmap
    have hband : ∀ t : ℝ, F (s, q, t) ≠ 0 → t ∈ Icc (-L) L := fun t ht => by
      have h2 := (hb (s, q, t) ht).2
      exact mem_Icc.2 (abs_le.1 h2)
    have hpt : (fun η : ℝ => pdEta F (s, q, η)) =
        fun η : ℝ => deriv (fun t : ℝ => F (s, q, t)) η :=
      funext fun η => (partialDerivSlice F hF.smooth s q η).2.2
    rw [hpt]
    exact (integralDerivZero (fun t : ℝ => F (s, q, t)) hsm (-L) L hband).1
  -- the weight is constant in `η`, so the inner integral vanishes for each `(s, q)`
  have hq : ∀ s q : ℝ, ∫ η : ℝ, ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdEta F (s, q, η) = 0 := by
    intro s q
    rw [integral_const_mul, hline s q, mul_zero]
  have hs : ∀ s : ℝ, ∫ q in Ioc (0 : ℝ) c, ∫ η : ℝ,
      ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdEta F (s, q, η) = 0 := by
    intro s
    simp only [hq s, integral_zero]
  -- Fubini on the cell with `η` innermost, then the vanishing slices
  refine (cellFubiniEta c _ hG).trans ?_
  show ∫ s in Ioi (0 : ℝ), ∫ q in Ioc (0 : ℝ) c, ∫ η : ℝ,
      ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * pdEta F (s, q, η) = 0
  simp only [hs, integral_zero]

end UnforcedLeray.Short.PartIIa
