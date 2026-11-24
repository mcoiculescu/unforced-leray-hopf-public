import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22_2_1
import UnforcedLeray.Short.PartIIIa.T22_CanonicalTransfer.LongComparison.PreparedDatum.CompactXGBound

/-!
# Part III-a, task `PartIII-a:T22/2/1` — Assembly of `ctCanonicalBranchProps` (SP 3121-3128, 3223-3225, 3300-3302)

Assembles `ctCanonicalBranchProps` from `ctCanonicalBranchProps_of`
(`UnforcedLeray.Short.«PartIII-a».Sub.«PartIII-a_T22_2_1»`) and `canonicalCompactXGBound_proof`
(`UnforcedLeray.Short.«PartIII-a».T22_CanonicalTransfer.LongComparison.PreparedDatum.CompactXGBound`).
-/

namespace UnforcedLeray.Short.IIIa.T22Sub

theorem ctCanonicalBranchProps : UnforcedLeray.Short.IIIa.T22Sub.CTCanonicalBranchProps :=
  ctCanonicalBranchProps_of canonicalCompactXGBound_proof

end UnforcedLeray.Short.IIIa.T22Sub
