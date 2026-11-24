import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.SmoothPer
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Band
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Deriv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.ExpDecay
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Identity
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Decay1
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.ParsevalMerid
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Comp
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.MomI
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.FamilyBound
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds

/-!
# Part II-a, task `PartII-a:N02/4/4` (`NzFinPotentials`): assembly

Source of record: `the November 2 reference manuscript`, lines 1713-1727 and 1744-1745.

`nzFinPotentials_of` (Sub/PartII-a_N02_4_4.lean) assembles `NzFinPotentials` from the eleven
per-mode lemma Props (`NzFp*`), `NzModeSolve` and `NzModeBounds`. This file supplies each of them.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`NzFinPotentials` (task `PartII-a:N02/4/4`).** -/
theorem nzFinPotentials : UnforcedLeray.Short.PartIIa.NzFinPotentials :=
  nzFinPotentials_of nzFpSmoothPer nzFpBand nzFpDeriv nzFpExpDecay nzFpIdentity nzFpDecay1
    nzFpParseval nzFpParsevalMerid nzFpComp nzFpMomI nzFpFamilyBound nzModeSolve nzModeBounds

end UnforcedLeray.Short.PartIIa
