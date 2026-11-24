import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartIIa.Calc.JetToolkitProof
import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc
import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc.AgeSmoothLocal
import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc.HeatOpLin
import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc.AgeComm
import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc.AgeWE
import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc.HeatOpK
import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc.MeanHeatEq
import UnforcedLeray.Short.PartIIa.Calc.BlockA2Calc.StressWords
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.FluctWords
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanSmoothQ
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.HeatWords
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanHeatPart
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanRemPart
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanWords

/-!
# Part II-a, task `PartII-a:R02/12`: the `A₂` block of the late table (assembly)

No new mathematics: the block follows from `Jet.A2.ringLateA2_of_parts` (`Calc/BlockA2Calc.lean`),
the jet toolkit `Jet.jetToolkit` (`Calc/JetToolkitProof.lean`), the base-jet leaves
(`Calc/BaseJets/*.lean`) and the seven `A₂` leaves (`Calc/BlockA2Calc/*.lean`).  Source of record:
`the November 2 reference manuscript`, lines 1253-1254, 1278, 1281, 1284-1285.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02/12`**: the `A₂` block of the late residual table, from the late ingredients
and the train mean equations. -/
theorem ringLateA2_of (h : LateIngredients) (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) :
    RingLateA2 :=
  Jet.A2.ringLateA2_of_parts Jet.jetToolkit (Jet.fluctWords_of h)
    (Jet.meanWords_of (Jet.meanSmoothQ_of h) (Jet.heatWords_of h.heat Jet.jetToolkit.iterLin)
      Jet.jetToolkit.iterLin (Jet.meanHeatPart_of h) (Jet.meanRemPart_of h))
    Jet.A2.ageSmoothLocal Jet.A2.heatOpLin (Jet.A2.ageComm_of h.comm) Jet.A2.ageWE
    (Jet.A2.heatOpK_of h.comm Jet.jetToolkit.comm) (Jet.A2.meanHeatEq_of hE)
    (Jet.A2.stressWords_of h)

end UnforcedLeray.Short.PartIIa
