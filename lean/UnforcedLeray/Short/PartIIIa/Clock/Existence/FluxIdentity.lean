import UnforcedLeray.Short.PartIIIa.Sub.T21_3_Horizon
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5.L1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5.L2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_5.L3
import UnforcedLeray.Short.PartIIIa.Clock.Existence.BiotSavartField

/-!
# Part III-a, `PartIII-a:T21/3/5/4`: the horizon flux identity on all parameters

Source of record: `the November 2 reference manuscript`, the flux identity
(T21/3/5), horizon form. The conditional theorem `fluxIdentityOn_of` (in `Sub/T21_3_Horizon.lean`)
is applied to the accepted inputs `ecSmoothPeriodic_all` (L1), `fluxIntOmega_all` (L2),
`fluxIntVel_all` (L3) and `biotSavartFieldAll` (Clock/Existence/BiotSavartField.lean).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

/-- `T21/3/5` (horizon form) holds for all parameters. -/
theorem fluxIdentityOnAll : UnforcedLeray.Short.IIIa.Exist.FluxIdentityOnAll :=
  fluxIdentityOn_of ecSmoothPeriodic_all fluxIntOmega_all fluxIntVel_all biotSavartFieldAll

end UnforcedLeray.Short.IIIa.Exist
