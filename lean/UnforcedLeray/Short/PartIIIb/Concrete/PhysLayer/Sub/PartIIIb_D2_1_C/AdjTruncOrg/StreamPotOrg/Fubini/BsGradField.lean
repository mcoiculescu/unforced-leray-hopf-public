import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsCutoff
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsGradFieldSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.BsGradFieldDecay

/-!
# Orthogonality of solenoidal slices to gradient fields (BSGradField)

Source `the November 2 reference manuscript` lines 1351-1362.

Let `g(z) = ∫ P(y-z) h(y) dy`. By `bsGradFieldSmooth`, `g` is smooth with `∇g = G`, where
`G(z) = ∫ h(y) K(y-z) dy`. By `bsGradFieldDecay` the two decay bounds hold with a common
constant `C`, so `bsCutoff` applies to the solenoidal slice `f` and gives `∫ f · ∇g = 0`.
Rewriting `∇g` as `G` gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bsGradField : BSGradField := by
  intro f hf hsol h hh hhs
  obtain ⟨hgsmooth, hgrad⟩ := bsGradFieldSmooth h hh hhs
  obtain ⟨C, hC⟩ := bsGradFieldDecay h hh hhs
  have key := bsCutoff f hf hsol
    (fun z : Space => ∫ y : Space, ((UnforcedLeray.PressureAnalysis.newtonPotential (y - z) : ℝ) : ℂ) * h y)
    hgsmooth C (fun z => (hC z).1) (fun z => by rw [hgrad z]; exact (hC z).2)
  simp only [hgrad] at key
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete
