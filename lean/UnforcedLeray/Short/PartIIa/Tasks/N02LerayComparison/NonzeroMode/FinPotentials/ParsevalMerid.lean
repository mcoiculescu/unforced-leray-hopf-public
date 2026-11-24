import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_8
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.ParsevalMerid.Band2Decay1
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.ParsevalMerid.MeridOpS

/-!
# Part II-a, task `PartII-a:N02/4/4/8`: `NzFpParsevalMerid`

Source of record: `the November 2 reference manuscript`, lines 1713-1727 and 1744-1745.
The proof is `nzFpParsevalMerid_of` applied to `nzFpParseval`, `nzFpBand2Decay1` and `nzFpMeridOpS`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem nzFpParsevalMerid : UnforcedLeray.Short.PartIIa.NzFpParsevalMerid :=
  nzFpParsevalMerid_of nzFpParseval nzFpBand2Decay1 nzFpMeridOpS

end UnforcedLeray.Short.PartIIa
