import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.KineticImpulse
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.TestedImpulse
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.CompactComparison
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.Mellin
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.AbsoluteStress
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.Anisotropy

/-!
# Part III-a, task `PartIII-a:T22` — Assembly of `canonicalTransferAll` (SP 3106–3404)

Assembles `CTLongComparison ∧ CTKineticImpulse ∧ CTPartialMoment ∧ CTTestedImpulse ∧
CTCompactComparison ∧ CTMellin ∧ CTAbsoluteStress ∧ CTStressDefect ∧ CTAnisotropy`
from `T22Sub.canonicalTransferAll_of` and the seven `T22_CanonicalTransfer` child modules.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem canonicalTransferAll :
    UnforcedLeray.Short.IIIa.CTLongComparison ∧
      UnforcedLeray.Short.IIIa.CTKineticImpulse ∧
      UnforcedLeray.Short.IIIa.CTPartialMoment ∧
      UnforcedLeray.Short.IIIa.CTTestedImpulse ∧
      UnforcedLeray.Short.IIIa.CTCompactComparison ∧
      UnforcedLeray.Short.IIIa.CTMellin ∧
      UnforcedLeray.Short.IIIa.CTAbsoluteStress ∧
      UnforcedLeray.Short.IIIa.CTStressDefect ∧
      UnforcedLeray.Short.IIIa.CTAnisotropy :=
  T22Sub.canonicalTransferAll_of
    ctLongComparison ctKineticImpulse ctPartialMoment ctTestedImpulse
    ctCompactComparison ctMellin ctAbsoluteStress ctStressDefect ctAnisotropy

end UnforcedLeray.Short.IIIa
