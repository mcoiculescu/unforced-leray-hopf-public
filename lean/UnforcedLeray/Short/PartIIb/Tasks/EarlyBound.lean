import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F6
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound.GreenVorticityUncurl
import UnforcedLeray.Short.PartIIb.Tasks.InvariantProjections

/-!
# Part II-b, task `PartII-b:F6`: early meridional correction bound (`EarlyBound`, SP 2254–2268)

Source of record: `the November 2 reference manuscript`
(SP), lines 2254–2268, display `short-bg:early` at line 2263.

Assembles `earlyBound_of_duhamel` (and convenience wrapper `earlyBound_of_blockDichotomy`) from
`earlyBound_of_duhamel_leaves`, `greenVorticityUncurlDuhamel_proof`, and `dichotomyProjections_of`.
-/

namespace UnforcedLeray.Short.IIb

theorem earlyBound_of_duhamel
    (hDP : UnforcedLeray.Short.IIb.DichotomyProjections)
    (hBS : UnforcedLeray.Short.IIb.BodySourceBound) :
    UnforcedLeray.Short.IIb.EarlyBound :=
  earlyBound_of_duhamel_leaves greenVorticityUncurlDuhamel_proof hDP hBS

theorem earlyBound_of_blockDichotomy
    (hBD : UnforcedLeray.Short.IIb.BlockDichotomy)
    (hBS : UnforcedLeray.Short.IIb.BodySourceBound) :
    UnforcedLeray.Short.IIb.EarlyBound :=
  earlyBound_of_duhamel (dichotomyProjections_of hBD) hBS

end UnforcedLeray.Short.IIb
