import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartIIa.Sub.R02_8
import UnforcedLeray.Short.PartIIa.Calc.JetToolkitProof
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.FluctWords
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanSmoothQ
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.HeatWords
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanHeatPart
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanRemPart
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanWords

/-!
# Part II-a, task `PartII-a:R02/8`: the `A₁` block of the late table (assembly)

No new mathematics: the block follows from `Jet.ringLateA1_of_parts` (`Sub/R02_8.lean`), the
jet toolkit `Jet.jetToolkit` (`Calc/JetToolkitProof.lean`) and the base-jet leaves
(`Calc/BaseJets/*.lean`).  Source of record:
`the November 2 reference manuscript`, lines 1243-1285.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02/8`**: the `A₁` block of the late residual table, from the late ingredients. -/
theorem ringLateA1_of (h : LateIngredients) : RingLateA1 :=
  Jet.ringLateA1_of_parts Jet.jetToolkit (Jet.fluctWords_of h)
    (Jet.meanWords_of (Jet.meanSmoothQ_of h) (Jet.heatWords_of h.heat Jet.jetToolkit.iterLin)
      Jet.jetToolkit.iterLin (Jet.meanHeatPart_of h) (Jet.meanRemPart_of h))

end UnforcedLeray.Short.PartIIa
