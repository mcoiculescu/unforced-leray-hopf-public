import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_7
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Short.PartIIIa.Tasks16.Dominated
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `PartIII-b:C/rep/2/4/L4` : the outward primitive in phase supremum (`outPrimPhaseBound`)

Source `the November 2 reference manuscript` 4181-4192 (`Ψ_Z(r,z) = -∫_r^∞ ρ Z_z(ρ,0,z) dρ`).
Composition of the pointwise domination `outPrimPointwise_of` (from `IIIa.sepWDominated` and
`IIIa.sepKernelBounds`) with the analytic core `outMajAnnulus`, through `outPrimPhaseBound_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The outward primitive in phase supremum** (`OutPrimPhaseBound`, source 4181-4192). -/
theorem outPrimPhaseBound : OutPrimPhaseBound :=
  outPrimPhaseBound_of (outPrimPointwise_of IIIa.sepWDominated IIIa.sepKernelBounds) outMajAnnulus

end UnforcedLeray.Short.PartIIIb.Concrete

end
