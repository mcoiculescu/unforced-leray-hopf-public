import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_3
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5_6

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem latSmooth (as : ℝ) (χf : ℝ → ℝ) : LatSmooth as χf :=
  latSmooth_of as χf localTsumSmooth (latTermSmooth as χf) (latTermMajor as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
