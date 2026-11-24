import UnforcedLeray.Short.PartIIb.Sub.T22
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.RegularEnergyDeriv
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TransportIBP
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap

/-!
# Part II-b, task `PartII-b:T22`: assembly of the free cylinder energy estimate

Glue: `free_cyl_energy_of` (Sub/T22.lean) applied to the six leaf results.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem free_cyl_energy : FreeCylEnergy :=
  free_cyl_energy_of cylClassicalExists cylWeakEqClassical regularEnergyDeriv
    cylDiffusionBound cylTransportIBP cylTrainGap

end UnforcedLeray.Short.IIb
