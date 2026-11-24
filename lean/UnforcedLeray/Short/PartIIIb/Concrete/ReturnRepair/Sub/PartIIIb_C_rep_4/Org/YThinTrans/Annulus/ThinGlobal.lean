import UnforcedLeray.Short.PartIIIa.T13_ThinGlobal
import UnforcedLeray.Short.PartIIIa.T12_LtauMinkowski
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import UnforcedLeray.Short.PartIIIa.Tasks16.Dominated
import UnforcedLeray.Short.PartIIIa.Tasks16.DomYoung
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds

/-!
# `PartIII-b:C/rep/4/2/org/3/3`: the instance of `sep:thin-global`

Source `the November 2 reference manuscript` 3669-3674 (`sep:thin-global`: "the
same argument with `p = 1`"), 3631-3646 (`sep:young`).

`IIIa.SepThinGlobal` from the accepted `sep:young` ingredients (`sepWDominated`,
`sepKernelBounds`, `sepDomYoung`, assembled by `sepYoung_of`), Minkowski `ltauMinkowski` and
`thinGlobal_of_parts`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`sep:thin-global`** (source 3669-3674). -/
theorem annulus_sepThinGlobal : UnforcedLeray.Short.IIIa.SepThinGlobal :=
  UnforcedLeray.Short.IIIa.thinGlobal_of_parts
    (UnforcedLeray.Short.IIIa.sepYoung_of UnforcedLeray.Short.IIIa.sepWDominated
      UnforcedLeray.Short.IIIa.sepKernelBounds sepDomYoung)
    UnforcedLeray.Short.IIIa.ltauMinkowski

end UnforcedLeray.Short.PartIIIb.Concrete
