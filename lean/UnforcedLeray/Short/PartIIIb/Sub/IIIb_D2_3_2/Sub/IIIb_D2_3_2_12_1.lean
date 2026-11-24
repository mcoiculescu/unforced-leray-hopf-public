import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_1.Generic

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Velocity pairing continuity** (source 2666-2700, 4284-4286): the pairing with the physical
velocity of a body velocity `v ∈ VelG` is continuous for a phase test. Proved from the generic
continuity `pairCont_of_le` with `ageμ c (-3/2) ≤ K • bodyMeasure c γ ν` (`ageμ_le_body`). -/
theorem velPairCont_proved (c γ ν ε : ℝ) : VelPairCont c γ ν ε := by
  intro hc hν hε H hH
  obtain ⟨K, hK, hK0, hle⟩ := ageμ_le_body c γ ν hν
  exact pairCont_of_le hc hε hK hK0 hle H hH

end UnforcedLeray.Short.PartIIIb.Concrete
