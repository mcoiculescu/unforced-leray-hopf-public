import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth

/-!
# `PartII-b:S3`: Strong regularity assembly (SP 2525-2562)

Assembles `strongRegularity_of_jointSmooth` with `jointSmoothnessFromSpatialAllOrders_proof`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem strongRegularity_of (hS1 : UnforcedLeray.Short.IIb.StrongFirstDerivative)
    (hS2 : UnforcedLeray.Short.IIb.StrongAllOrders) :
    UnforcedLeray.Short.IIb.StrongRegularity :=
  strongRegularity_of_jointSmooth jointSmoothnessFromSpatialAllOrders_proof hS1 hS2

end UnforcedLeray.Short.IIb
