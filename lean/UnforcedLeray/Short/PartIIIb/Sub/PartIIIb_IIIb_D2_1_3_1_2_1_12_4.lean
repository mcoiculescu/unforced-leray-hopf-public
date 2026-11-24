import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_12
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.DriftPsi.Identity

/-!
# Corrected weak drift of the stream potential

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480 (`w = (μ + ½ - ∂_τ + ½ y·∇ - νΔ) ψ`).

The Prop `DriftPsi` of `PartIII-b_IIIb-D2_1_3_1_2_1_12.lean` has the constant `μ`; with the Lean
definitions (`driftT = -∂_τ + ½ radialT + 3/2`, `wOpT = T0 - νΔ + μ - 1`, the transpose of
`μ + ½ - ∂_τ + ½ y·∇ - νΔ`) the pointwise identity is
`driftT Θ = (μ + ½) Θ - ν lapT Θ - wOpT ν μ Θ` (`driftT_eq_wOpT_pointwise`), so the correct
constant is `μ + ½`; `DriftPsi` differs from the true pairing by `½ ⟪Θ, ψ⟫`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF)

/-- Corrected weak drift of the stream potential; now the statement of `DriftPsi`. -/
abbrev DriftPsiCorr : Prop := DriftPsi

end UnforcedLeray.Short.PartIIIb.Concrete
