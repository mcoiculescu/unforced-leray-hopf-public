import UnforcedLeray.Short.PartIIb.Sub.T22_1_1_4
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.VcDeriv.IsoVGaussBound
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.TrainCoeff.VcDeriv.GaussRpow

/-!
# `PartII-b:T22/1/1/4`: `V_c` is differentiable with bounded derivative (assembly)

Source `the November 2 reference manuscript`, lines 2074-2105 and 2205-2211.
Assembles the two leaves `IsoVGaussBound` (`VcDeriv/IsoVGaussBound.lean`) and `GaussLeRpow`
(`VcDeriv/GaussRpow.lean`) through the decomposition `tcVcDeriv_of` (`Sub/T22_1_1_4.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

theorem tcVcDeriv : UnforcedLeray.Short.IIb.CylPDE.TcVcDeriv :=
  tcVcDeriv_of isoVGaussBound gaussLeRpow

end UnforcedLeray.Short.IIb.CylPDE
