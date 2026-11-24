import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval.QScalar
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval.HFubini
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval.ProdInt
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval.OneModeInt
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval.S2Smooth
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.FinPotentials.Parseval.OpSIter

/-!
# Part II-a, task `PartII-a:N02/4/4/7`: `NzFpParseval` from the six lemma Props

Source of record: `the November 2 reference manuscript`, lines 1713-1727 and 1744-1745.
The proof is `nzFpParseval_of` applied to the six lemma theorems proved in the `Parseval/` folder.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem nzFpParseval : UnforcedLeray.Short.PartIIa.NzFpParseval :=
  nzFpParseval_of nzFpQScalar nzFpHFubini nzFpOneModeInt nzFpProdInt nzFpOpSIter nzFpS2Smooth

end UnforcedLeray.Short.PartIIa
