import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_1_1

/-!
# `PartIII-b:C/srcL/6/1`: `XSZSmooth` from the smoothness of the zero-width Newton field

Source of record: `the November 2 reference manuscript` lines 4776-4791 and
4917-4937.  The statement `XSZSmooth` is defined in `Sub/PartIII-b_C_srcL_6.lean`; the reduction
`xsZSmooth_of (h : NewtonVSmooth) : XSZSmooth` is proved in `Sub/PartIII-b_C_srcL_6_1.lean`, and
`newtonVSmooth : NewtonVSmooth` in `Concrete/SourceL/Sub/PartIII-b_C_srcL_6_1_1.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem xsZSmooth : XSZSmooth := xsZSmooth_of newtonVSmooth

end UnforcedLeray.Short.PartIIIb.Concrete
