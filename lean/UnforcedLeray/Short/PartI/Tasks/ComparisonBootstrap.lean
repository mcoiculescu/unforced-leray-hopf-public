import UnforcedLeray.Short.PartI.Sub.PartI_T09.Assembly
import UnforcedLeray.Short.PartI.Sub.PartI_T09.ComparisonGronwall
import UnforcedLeray.Short.PartI.Sub.PartI_T09.BootstrapContinuity
import UnforcedLeray.Short.PartI.Sub.PartI_T09.JetL2Bridge
import UnforcedLeray.Short.PartI.Sub.PartI_T09.JetSupBridge
import UnforcedLeray.Short.PartI.Sub.PartI_T09.TrainErrInitial
import UnforcedLeray.Short.PartI.Sub.PartI_T09.TrainErrGradSup
import UnforcedLeray.Short.PartI.Sub.PartI_T09.TrainPeriodAsymptotics
import UnforcedLeray.Short.PartI.Sub.PartI_T09.JetArithmetic
import UnforcedLeray.Short.PartI.Sub.PartI_T09.GradClosing
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic

/-!
# `PartI:T09`: `TrainComparison`

Source of record: `the November 2 reference manuscript`, lines 337-355.
The statement is assembled from the leaves by `train_comparison_of`
(`Sub/PartI_T09/Assembly.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem train_comparison : UnforcedLeray.Short.PartI.TrainComparison :=
  train_comparison_of differentiated_energy_inequality trainErrBasic_proof
    comparisonGronwall_proof bootstrapContinuity_proof
    jetL2Bridge_proof jetSupBridge_proof
    trainErrInitial_proof trainErrGradSup_proof
    trainPeriodAsymptotics_proof jetArithmetic_proof gradClosing_proof

end UnforcedLeray.Short.PartI

end
