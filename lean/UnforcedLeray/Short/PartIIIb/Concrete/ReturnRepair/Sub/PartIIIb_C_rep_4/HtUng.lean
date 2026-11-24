import UnforcedLeray.Short.PartIIIb.Concrete.Spaces

/-!
# The ungained scaled repair-receiver norm `htUng`

Source `the November 2 reference manuscript` 2697-2700: the second summand of the
split stress norm, `ρ_b^{-1/2}‖T₂‖_{H_T} = (∫ |T₂|² ρ_b⁻¹ s^{-1/2} dς)^{1/2}`, without the gain
`g⁻¹`.

One definition shared by the `rep/4` files that used to declare their own copies
(`Org/FarThin/ThinRepKernel.lean`, `YRepStream/EarlyRepRep/Kernel/Ungained.lean`,
`YRepStream/TransTable/Gain.lean`, and `hTUng` of `YRepStream/LateRepRep/SepKernel/Transfer.lean`),
so that they can be imported together (organizer item `ORG:clash-pass`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The ungained scaled repair-receiver norm** `ρ_b^{-1/2}‖T₂‖_{H_T} =
(∫ |T₂|² ρ_b⁻¹ s^{-1/2} dς)^{1/2}` of a chart tensor (source 2697-2700; the repair part of the
split stress norm without the gain `g⁻¹`). -/
def htUng (c ρb : ℝ) (f : Chart → Ten3) : ℝ≥0∞ :=
  (∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂(htRhoMeasure c ρb)) ^ (1 / 2 : ℝ)

end UnforcedLeray.Short.PartIIIb.Concrete
