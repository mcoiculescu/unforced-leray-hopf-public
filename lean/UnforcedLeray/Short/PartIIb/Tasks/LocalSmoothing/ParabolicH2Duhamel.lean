import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org
import UnforcedLeray.Short.Spine.Proofs.TrainEstimates
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.OrbitSmoothing
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.OrbitExists
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.LinearVersion

/-!
# Part II-b, task `PartII-b:F8/1` — Assembly of `CylinderParabolicH2Duhamel` (SP 2296–2305)

Assembles `CylinderParabolicH2Duhamel` from `cylinderParabolicH2Duhamel_of_org`,
`UnforcedLeray.Short.Spine.trainEstimates.2`, and the four `PartII-b_F8_1_org` leaves
(`cylOseenOrbitSmoothing_proof`, `cylOseenOrbitExists_proof`,
`meridionalDuhamelRegularity_proof`, `meridionalLinearVersion_proof`).
-/

namespace UnforcedLeray.Short.IIb

theorem cylinderParabolicH2Duhamel_proof : UnforcedLeray.Short.IIb.CylinderParabolicH2Duhamel :=
  cylinderParabolicH2Duhamel_of_org
    UnforcedLeray.Short.Spine.trainEstimates.2
    cylOseenOrbitSmoothing_proof
    cylOseenOrbitExists_proof
    meridionalDuhamelRegularity_proof
    meridionalLinearVersion_proof

end UnforcedLeray.Short.IIb
