import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.DivCurlFreeVanish
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.CutLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.MollRegular
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.MollDiv
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.OrthUnfold
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.MollCurl
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.MollPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.MollLp
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.TensorMollApprox
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.Separate.HMeasAe

/-!
# Part II-b, leaf `PartII-b:T11/6` (`NiceFieldsSeparate`): unconditional assembly

Source of record: `the November 2 reference manuscript`, SP 2618. The conditional
theorem `niceFieldsSeparate_of` (in `Sub/T11_6.lean`) takes the ten classical leaves as hypotheses.
This file supplies each of them from its own proved file in `Tasks/FlatUnique/Separate/`, so that
`niceFieldsSeparate` is unconditional.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- The leaf `PartII-b:T11/6` with all ten leaf hypotheses discharged by their proofs. -/
theorem niceFieldsSeparate : UnforcedLeray.Short.IIb.NiceFieldsSeparate :=
  niceFieldsSeparate_of divCurlFreeVanish cutLocInt mollRegular mollDiv orthUnfold mollCurl
    mollPeriodic mollLp tensorMollApprox hMeasAe

end UnforcedLeray.Short.IIb

end
