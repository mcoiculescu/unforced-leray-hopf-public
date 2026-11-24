import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2.Ibp2Step
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2.InletD3Global
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2.Yq2

/-!
# `gEQuad2 : GEQuad2` (`PartIII-b:C/ward/12/3/2/2/4`)

Source `the November 2 reference manuscript`,
lines 2552-2559, 2525-2533, 1515-1531, 2381-2387.

Proves `gEQuad2 : GEQuad2` unconditionally from:
* `gEQIbp2_step : GEQIbp2Step` (`Quad2/Ibp2Step.lean`),
* `gEQInletD3Global : GEQInletD3Global` (`Quad2/InletD3Global.lean`),
* `gEQYq2 : GEQYq2` (`Quad2/Yq2.lean`),
* `gEQIbp2_of_step` and `gEQuad2_of` (`Quad2/Defs.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Order-2 weak integration by parts for the quadratic term** (source 2552-2559). -/
theorem gEQIbp2 : GEQIbp2 :=
  gEQIbp2_of_step gEQIbp2_step

/-- **Order-2 quadratic leaf** `gEQuad2 : GEQuad2` (source 2552-2559, 2525-2533, 1515-1531,
2381-2387). -/
theorem gEQuad2 : GEQuad2 :=
  gEQuad2_of gEQIbp2 gEQYq2

end UnforcedLeray.Short.PartIIIb.Concrete
