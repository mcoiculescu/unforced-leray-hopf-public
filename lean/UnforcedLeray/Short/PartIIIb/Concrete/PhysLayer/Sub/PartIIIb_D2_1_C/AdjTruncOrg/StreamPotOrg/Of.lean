import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Defs

/-!
# `StreamPotExists` from the Biot-Savart ingredients

Source `the November 2 reference manuscript` lines 1351-1362.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem streamPotExists_of (h1 : BSDefined) (h2 : BSGrad) (h3 : BSCurl) (h4 : BSSol)
    (h5 : HardyR3) (h6 : BSSlice) (h7 : BSHardyY2) : StreamPotExists := by
  intro P hP Φ hΦ hs
  obtain ⟨hm, hper⟩ := h1 P hP Φ hΦ hs
  obtain ⟨Dψ, hD⟩ := h2 P hP Φ hΦ hs
  exact ⟨bsPot Φ, Dψ, ⟨hm, hper, h3 P hP Φ hΦ hs, h4 P hP Φ hΦ hs, hD,
    h7 h5 P hP Φ hΦ hs hm hper Dψ hD (h6 P hP Φ hΦ hs Dψ hD)⟩⟩

end UnforcedLeray.Short.PartIIIb.Concrete
