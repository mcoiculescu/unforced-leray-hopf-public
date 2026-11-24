import UnforcedLeray.Short.PartIIa.Calc.BlockB2
import UnforcedLeray.Short.PartIIa.Calc.BlockB2.RemWords
import UnforcedLeray.Short.PartIIa.Calc.JetToolkitProof
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.FluctWords
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanSmoothQ
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.HeatWords
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanHeatPart
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanRemPart
import UnforcedLeray.Short.PartIIa.Calc.BaseJets.MeanWords

/-!
# Part II-a, task `PartII-a:R02/10`: the late block `B₂`

Final assembly of the `B₂` block of the late residual table (`RingLateB2`, `Sub/R02.lean`,
line 103).  No new mathematics: the block is `Jet.B2.ringLateB2_of_parts` (`Calc/BlockB2.lean`,
line 570) applied to the jet toolkit, the fluctuation words, the mean words and the remainder
words, each obtained from `LateIngredients` by its leaf.

Source of record: `the November 2 reference manuscript`, lines 1243-1283
(`B₂ = -v₁(K+1)H + HH_η + 2ν(K+1)H_q - ν(K+1)²v₂`, line 1256; late table, lines 1273-1279;
leading mean `4a₀²G∂_ηG` of `K`-degree `-3`, lines 1281-1283).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02/10`**: the late block `B₂` (sizes `s^{-3/2}`, `s^{-2}`, `s^{-5/2}`, and
`∂_q B₂` exponentially small), from the late ingredients. -/
theorem ringLateB2_of (h : LateIngredients) : RingLateB2 :=
  Jet.B2.ringLateB2_of_parts Jet.jetToolkit (Jet.fluctWords_of h)
    (Jet.meanWords_of (Jet.meanSmoothQ_of h)
      (Jet.heatWords_of h.heat Jet.jetToolkit.iterLin)
      Jet.jetToolkit.iterLin (Jet.meanHeatPart_of h) (Jet.meanRemPart_of h))
    (Jet.B2.remWords32_of h (Jet.meanSmoothQ_of h)
      (Jet.heatWords_of h.heat Jet.jetToolkit.iterLin))

end UnforcedLeray.Short.PartIIa
