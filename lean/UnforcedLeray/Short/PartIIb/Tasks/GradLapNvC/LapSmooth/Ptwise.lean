import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.Ptwise.Axis
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.Ptwise.Split
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.Ptwise.NvReal
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.LapSmooth.Ptwise.CommRe
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5_5

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Pointwise Laplacian identity: assembled from the four leaves via `lapPtwise_of`. -/
theorem lapPtwise_proof : UnforcedLeray.Short.IIb.LapPtwise :=
  lapPtwise_of lapAxis lapSplit lapNvReal lapCommRe

end UnforcedLeray.Short.IIb
