import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_A1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_A2

/-!
# `fwuSub`: sub-lemma A of the free weak uniqueness (source 1580-1583, 2666-2700)

`FWUSub` follows from `fwuSub_of`, applied to the a.e. linearity `fwuSubAE` of the lift
(`PartIIIb-D2_1_A1`) and the integrability `fwuSubInt` of the pairings of lifts with the test
fields (`PartIIIb-D2_1_A2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Sub-lemma A (source 1580-1583, 2666-2700): the weak formulation is subtractive along the lift
of `VelG` differences. -/
theorem fwuSub {c γ ν ε μ : ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε) : FWUSub c γ ν ε μ :=
  fwuSub_of hc hν hε (fwuSubAE c γ ν ε) (fwuSubInt c γ ν ε μ)

end UnforcedLeray.Short.PartIIIb.Concrete
