import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Split
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Train
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Support
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Meas

/-!
# `PartIII-b:C/asrc/ra/8`: `RPerBound`

Assembly of `rPerBound_of` (`Sub/PartIII-b_C_asrc_ra_8.lean`) from the five leaves
`rPerSplit`, `rCrossBound`, `rTrainBound`, `rPerSupport`, `rPerMeas`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rPerBound (as : ℝ) (χf : ℝ → ℝ) : RPerBound as χf :=
  rPerBound_of as χf (rPerSplit as χf) (rCrossBound as χf) (rTrainBound as χf)
    (rPerSupport as χf) (rPerMeas as χf)

end UnforcedLeray.Short.PartIIIb.Concrete
