import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison.PreparedDatum
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison.ResidualBound
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison.Duhamel

/-!
# Part III-a, task `PartIII-a:T22/2` — Assembly of `CTLongComparison`

Assembles `CTLongComparison` and `ctCompactComparison_of_impulse` from
`T22Sub.ctDuhamelTransfer`, `T22Sub.ctCanonicalBranchProps`, and `T22Sub.ctCanonicalResidual`.
-/

namespace UnforcedLeray.Short.IIIa

theorem ctLongComparison : CTLongComparison :=
  (T22Sub.ctDuhamelTransfer T22Sub.ctCanonicalBranchProps T22Sub.ctCanonicalResidual).1

theorem ctCompactComparison_of_impulse :
    CTEmbeddings → CTKineticImpulse → CTPartialMoment → CTCompactComparison :=
  (T22Sub.ctDuhamelTransfer T22Sub.ctCanonicalBranchProps T22Sub.ctCanonicalResidual).2

end UnforcedLeray.Short.IIIa
