import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_3_4

/-!
# `XSStreamPsi` from the five pieces (task `PartIII-b:C/srcL/6/3`)

Source 4178-4186, 4917-4937.  The decomposition `xsStreamPsi_of` (in `Sub/PartIII-b_C_srcL_6_3.lean`)
reduces `XSStreamPsi` to the five pieces, which are proved in the modules `Sub/PartIII-b_C_srcL_6_3_k.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem xsStreamPsi : XSStreamPsi :=
  xsStreamPsi_of xsPsiReparam xsParamSmoothOpen xsPsiFamSmooth xsPsiFamMeas xsPsiDomination

end UnforcedLeray.Short.PartIIIb.Concrete
