import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5_5_3

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- `Δ (Nv R b t) = Nv R (lapReal R⁻¹ b) t` off the axis (SP 1639-1668, 1912-1916). -/
theorem lapNvReal : UnforcedLeray.Short.IIb.LapNvReal :=
  lapNvReal_of mpSmooth_proof mpDRho_proof mpDZ_proof sqrtQ_proof sqrtEta_proof

end UnforcedLeray.Short.IIb
