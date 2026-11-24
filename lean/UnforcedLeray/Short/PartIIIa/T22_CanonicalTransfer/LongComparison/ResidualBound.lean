import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22_2_2
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison.ResidualBound.CanonicalSolutionRep
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison.ResidualBound.ColumnWeakEq
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison.ResidualBound.GaussAndJetBound

/-!
# Part III-a, task `PartIII-a:T22/2/2` — Assembly of `ctCanonicalResidual` (SP 3129-3215)

Assembles `CTCanonicalResidual` from `ctCanonicalResidual_of` and the three leaf
proofs `hasCanonicalSolutionRep_proof`, `canonicalColumnWeakEq_proof`, and
`canonicalGaussAndJetBound_proof`.
-/

namespace UnforcedLeray.Short.IIIa.T22Sub

theorem ctCanonicalResidual : UnforcedLeray.Short.IIIa.T22Sub.CTCanonicalResidual :=
  ctCanonicalResidual_of
    hasCanonicalSolutionRep_proof
    canonicalColumnWeakEq_proof
    canonicalGaussAndJetBound_proof

end UnforcedLeray.Short.IIIa.T22Sub
