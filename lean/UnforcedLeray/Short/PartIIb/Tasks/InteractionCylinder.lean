import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F1
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.CylWeightedKernel
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.TrainGradCoeff
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.PlanarCompact
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder.PlanarKernel

namespace UnforcedLeray.Short.IIb

theorem interactionCylinder_proof : InteractionCylinderComparison ∧ InteractionCollectiveCompact :=
  interactionCylinder_of
    cylWeightedKernelStep_proof
    trainGradCoeffStep_proof
    planarInteractionCompactStep_proof
    planarKernelBoundStep_proof

end UnforcedLeray.Short.IIb
