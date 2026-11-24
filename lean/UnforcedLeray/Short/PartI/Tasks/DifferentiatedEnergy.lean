import UnforcedLeray.Short.PartI.Sub.T08Statement
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ViscousIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportWeights
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.StressBound
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.Closure

/-!
# Part I, task `PartI:T08`: the differentiated energy inequality (assembly)

Source of record: `the November 2 reference manuscript`, lines 341-359 (proof of
Lemma `sct:train`), with lines 326-339 and 261-288.

The target `differentiated_energy_inequality` is obtained from the conditional theorem
`differentiated_energy_inequality_of` (`Sub/T08Statement.lean`) by feeding it the eleven leaf
proofs, each proved in its own module of `Tasks/DifferentiatedEnergy/`:

* `trainErrBasic_proof` (`ErrBasic.lean`, leaf 1),
* `trainErrJetL2_proof` (`ErrJetL2.lean`, leaf 2),
* `trainPressureRegular_proof` (`PressureRegular.lean`, leaf 3),
* `trainJetEnergyBalance_proof` (`EnergyBalance.lean`, leaf 4),
* `jetViscousIBP_proof` (`ViscousIBP.lean`, leaf 5),
* `jetPressureOrth_proof` (`PressureOrth.lean`, leaf 6),
* `jetTransportBound_proof` (`TransportBound.lean`, leaf 7),
* `transportWeightSum_proof` (`TransportWeights.lean`, leaf 8),
* `jetForcingIBP_proof` (`ForcingIBP.lean`, leaf 9),
* `vcStressJetBound_proof` (`StressBound.lean`, leaf 10),
* `energyClosure_proof` (`Closure.lean`, leaf 11).

The statement `DifferentiatedEnergyInequality` is taken verbatim from `Sub/T08Statement.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T08`: the differentiated energy inequality.** Assembled from the eleven proved
leaves via `differentiated_energy_inequality_of`. -/
theorem differentiated_energy_inequality :
    UnforcedLeray.Short.PartI.DifferentiatedEnergyInequality :=
  differentiated_energy_inequality_of
    trainErrBasic_proof
    trainErrJetL2_proof
    trainPressureRegular_proof
    trainJetEnergyBalance_proof
    jetViscousIBP_proof
    jetPressureOrth_proof
    jetTransportBound_proof
    transportWeightSum_proof
    jetForcingIBP_proof
    vcStressJetBound_proof
    energyClosure_proof

end UnforcedLeray.Short.PartI
