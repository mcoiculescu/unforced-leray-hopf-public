import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Sub.PartIIIa_T21_2_7_2_1_2_1_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.StPartialSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.TimeIterDerivAe
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.SmoothAeJet
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.SupBddByXNorm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.TimeJetXNormBdd

/-!
# `PartIII-a:T21/2/7/2/1/2/1/3`: `TimeJetPartialBdd` from five leaves

Assembles `TimeJetPartialBdd` from the five leaves `stPartialSmooth`, `timeIterDerivAe`,
`smoothAeJet`, `supBddByXNorm`, `timeJetXNormBdd` through `timeJetPartialBdd_of`
(Sub `PartIII-a_T21_2_7_2_1_2_1_3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem timeJetPartialBdd : UnforcedLeray.Short.IIIa.TimeJetPartialBdd :=
  timeJetPartialBdd_of stPartialSmooth timeIterDerivAe smoothAeJet supBddByXNorm timeJetXNormBdd

end UnforcedLeray.Short.IIIa
