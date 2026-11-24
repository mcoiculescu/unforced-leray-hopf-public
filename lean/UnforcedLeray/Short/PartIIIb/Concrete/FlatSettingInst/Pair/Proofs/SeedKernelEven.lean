import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair.Defs
import UnforcedLeray.Short.PartIIIa.Clock.Frame
import UnforcedLeray.Short.PartI.StatementsSeed
import UnforcedLeray.Lib.PlanarSectors.NUE.AngularFourierDefs

/-!
# The planar growing vectors are centrally even (source 597: `q = h(r)e^{2iϑ}`, `e₁ = q̄`)

For the Part I seed `seedPlanar h z = h(|z|) (z/|z|)²`, the value at `-z` equals the value at `z`
(the square removes the sign), and `planeToC (-y) = -planeToC y`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair

/-- The Part I seed profile is even: `seedPlanar h (-z) = seedPlanar h z`. -/
theorem seedPlanar_neg (h : ℝ → ℂ) (z : ℂ) :
    UnforcedLeray.Short.PartI.seedPlanar h (-z) = UnforcedLeray.Short.PartI.seedPlanar h z := by
  simp only [UnforcedLeray.Short.PartI.seedPlanar, UnforcedLeray.Planar.NUE.Ang.ofProfile,
    UnforcedLeray.Planar.NUE.Ang.angPhase, norm_neg, neg_div, Even.neg_zpow even_two]

/-- **The planar growing vectors are centrally even** (source 597), in the form `SeedKernelEven`. -/
theorem seedKernelEven : SeedKernelEven := by
  intro κ hκ k y
  obtain ⟨_, h, _, _, _, h0, h1, _⟩ := hκ
  have hneg : IIIa.planeToC (-y) = -IIIa.planeToC y := by
    apply Complex.ext <;> simp [IIIa.planeToC]
  fin_cases k
  · show κ.e 0 (-y) = κ.e 0 y
    rw [h0 (-y), h0 y, hneg, seedPlanar_neg]
  · show κ.e 1 (-y) = κ.e 1 y
    rw [h1 (-y), h1 y, hneg, seedPlanar_neg]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Pair
