import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:Q2` (`QuadraticFamily`, SP 2497-2523, Proposition `prop:step3-quadratic-family`)**:
continuous bilinear quadratic family assembled from `QuadBound` (`Q1`). -/
theorem quadraticFamily_of (hQ1 : UnforcedLeray.Short.IIb.QuadBound) :
    UnforcedLeray.Short.IIb.QuadraticFamily :=
  quadraticFamily_of_core hQ1

end UnforcedLeray.Short.IIb

end
