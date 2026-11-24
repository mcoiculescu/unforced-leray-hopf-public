import UnforcedLeray.Short.PartIIIa.T20_CTEmbeddings
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.KineticImpulse
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.TestedImpulse

/-!
# Part III-a, task `PartIII-a:T22/4` — Assembly of `CTCompactComparison` (SP 3290-3299)

Assembles `CTCompactComparison` from `ctCompactComparison_of_impulse`,
`ctEmbeddings`, `ctKineticImpulse`, and `ctPartialMoment`.
-/

namespace UnforcedLeray.Short.IIIa

theorem ctCompactComparison : CTCompactComparison :=
  ctCompactComparison_of_impulse ctEmbeddings ctKineticImpulse ctPartialMoment

end UnforcedLeray.Short.IIIa
