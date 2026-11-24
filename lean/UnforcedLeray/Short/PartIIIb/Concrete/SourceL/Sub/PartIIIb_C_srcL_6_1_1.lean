import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_2
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1_3

/-!
# Smoothness of the zero-width Newton field (task `PartIII-b:C/srcL/6/1/1`)

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
The three leaves `NewtonFamSmooth`, `NewtonFamMeas`, `NewtonFamDom` (tasks `/1`, `/2`, `/3`) are
proved in their own modules; this module assembles them through `newtonVSmooth_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem newtonVSmooth : NewtonVSmooth :=
  newtonVSmooth_of newtonFamSmooth newtonFamMeas newtonFamDom

end UnforcedLeray.Short.PartIIIb.Concrete
