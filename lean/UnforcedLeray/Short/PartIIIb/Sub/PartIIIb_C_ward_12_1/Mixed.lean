import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets

/-!
# `mixedToFull`: full derivative from the mixed age/space jets

Source `the November 2 reference manuscript` lines 5461-5464 (pure calculus).
This is exactly `UnforcedLeray.Short.PartI.JointFromAgeJets`, proved as
`UnforcedLeray.Short.PartI.jointFromAgeJets` (constant `3^l`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem mixedToFull : MixedToFull := by
  intro l
  obtain ⟨K, hK, h⟩ := UnforcedLeray.Short.PartI.jointFromAgeJets l
  exact ⟨K, hK, h⟩

end UnforcedLeray.Short.PartIIIb.Concrete
