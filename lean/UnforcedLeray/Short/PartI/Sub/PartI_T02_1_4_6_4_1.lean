import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Needed

/-!
# `stressOrbitIsHeat` from the five analytic facts N1-N5 and one composition

Source: `the November 2 reference manuscript`,
lines 261-288 (the Duhamel term of the mild solution is the heat flow of `div (u ⊗ u)`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Composition lemma** (source lines 261-288): the identity `HeatDivStressIdentity` follows from
the five facts N1-N5 of `StressOrbitIsHeat/Needed.lean`.  Chain: `tensorH3Bilinear_planeValue_ae`,
`vectorH3NormalizedValue_actualHeatDivH3`, `heatDivVecL2CLM_apply_to_periodic`, N2 + N3 to rewrite
`heatDiv θ (w ⊗ w) = heat θ (advection w)`, N4 for the periodic heat on `L²`, N5 to pass between
centered and normalized classes. -/
def HeatDivStressComposition : Prop :=
  NeedSmoothRowIBP → NeedRowDivHeat → NeedRowTensorDivergence → NeedHeatPeriodicL2 →
    NeedZeroClassNormalized → HeatDivStressIdentity

theorem stressOrbitIsHeat_of_needs (hcomp : HeatDivStressComposition)
    (n1 : NeedSmoothRowIBP) (n2 : NeedRowDivHeat) (n3 : NeedRowTensorDivergence)
    (n4 : NeedHeatPeriodicL2) (n5 : NeedZeroClassNormalized) : StressOrbitIsHeat :=
  stressOrbitIsHeat_of (hcomp n1 n2 n3 n4 n5)

end UnforcedLeray.Short.PartI
