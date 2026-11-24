import UnforcedLeray.Short.PartIIb.Sub.ComparisonAndStrongDesign

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:G5` (`GlobalOperatorComparison`, SP 2426-2474, Proposition `prop:step3-operator-comparison`)**:
global operator comparison on `H_p` assembled from `YoungLateOperatorBounds` (`G2`),
`WindowComparison` (`G3`), and `AffineInletFacts` (`G4`). -/
theorem globalOperatorComparison_of (h2 : UnforcedLeray.Short.IIb.YoungLateOperatorBounds)
    (h3 : UnforcedLeray.Short.IIb.WindowComparison)
    (h4 : UnforcedLeray.Short.IIb.AffineInletFacts) :
    UnforcedLeray.Short.IIb.GlobalOperatorComparison :=
  globalOperatorComparison_of_core h2 h3 h4

end UnforcedLeray.Short.IIb

end
