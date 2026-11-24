import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_4
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.LocalSobolevBox
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.BoxXNorm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.PdCxPeriodic

/-!
# `PartIII-a:T21/2/7/2/1/2/1/3/4`: `supBddByXNorm`

Assembles `SupBddByXNorm` from the three leaves `localSobolevBox`, `boxXNorm`, `pdCxPeriodic`
through `supBddByXNorm_of` (Sub `PartIII-a_T21_2_7_2_1_2_1_3_4`).
-/

theorem supBddByXNorm : UnforcedLeray.Short.IIIa.SupBddByXNorm :=
  UnforcedLeray.Short.IIIa.supBddByXNorm_of UnforcedLeray.Short.IIIa.localSobolevBox
    UnforcedLeray.Short.IIIa.boxXNorm UnforcedLeray.Short.IIIa.pdCxPeriodic
