import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# Pointwise identity behind `DriftPsi`

Checks the algebra `driftT Θ = (μ + ½) Θ - ν lapT Θ - wOpT ν μ Θ` with the Lean definitions
(`driftT` in `Lib/PhaseSpace/Ops.lean`, `T0`, `L0` in `Units/B0411/Operators.lean`, `wOpT` in
`AdjTruncOrg.lean`). The constant is `μ + ½`, not `μ` as in the target `DriftPsi`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem driftT_eq_wOpT_pointwise (ν μ : ℝ) (Θ : ℝ × Space → CVec3) (x : ℝ × Space) :
    driftT Θ x = (μ + 1 / 2 : ℝ) • Θ x - ν • lapT Θ x - wOpT ν μ Θ x := by
  simp only [driftT, wOpT, L0, T0, Complex.coe_smul]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
