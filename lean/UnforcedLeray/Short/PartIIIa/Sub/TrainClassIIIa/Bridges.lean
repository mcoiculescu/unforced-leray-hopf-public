import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c2_2_7
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c2_2_8
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

/-!
# Part III-a: the BUC class in the free-moving and weak-smoothing chains (`ORG:train-class-IIIa/sub`)

Source of record: `the November 2 reference manuscript` (SP), lines 270-288 (the
train is the Gallay-Slijepcevic solution in `BUC`: bounded with bounded derivatives on every finite
age interval), 2937-2962 (free moving energy), 3040-3094 (weak smoothing).

`ORG:train-class-IIIa/sub` added the hypothesis `PartI.IsBUCTrain tr` after the train binder of the
statements that use a train property beyond `B0140.IsTrain`:

* free moving energy (SP 2937-2962): `FmeRate` (`Sub/T21_c2.lean`), `FmrTrainClose`, `FmrVelBdd`,
  `FmrVelGap`, `FmrRegular` (`Sub/T21_c2_2.lean`); `FmrIBP`, `FmrDeriv`, `FmrTransfer`,
  `FmrBracket`, `FmrIsoRadial` are unchanged (their train enters only through `IsTrain` fields
  and an explicit velocity bound, or not at all);
* weak smoothing (SP 3040-3084): `ShortWeakSmoothing` (`Clock/Stages.lean`), `MovingWeakStrong`,
  `WeakSmoothingPhys` (`Clock/WeakSmoothing.lean`), `RescaledTrainBounds`,
  `AdjointLocalizedBound`, `AdjointEnergyIneqs`, `AdjointExists` (`Clock/WeakSmoothing/Adjoint.lean`;
  `AdjointExists` in the `∃ ν₀` form of `AdjointWeakExistsBUC`), `LocalizedSourceBounds`
  (`Sub/PartIIIa_T21_2_1.lean`), `AdjointEnergyCase` (`Sub/PartIIIa_T21_2_2.lean`),
  `AdjChiWeighted` (`Sub/T21_2_2/E0/Defs.lean`), `AdjChiDerivBound` (`Sub/T21_2_2/E1/Defs.lean`).
  `ZeroCirculationPreserved` is unchanged (it uses no train property: the `L²` Biot-Savart velocity
  of the flow forces zero circulation).

The existence chain (SP 2819-2836) needed no change: its only train input is
`FiniteHorizonTrainBounds` (`Sub/T21_3_TrainBounds.lean`), supplied for BUC trains by
`TrainBoundsSmall`; the horizon leaves take a horizon flux path, which carries the bounds.

This file records that the BUC forms written earlier by the auditors are now the statements
themselves (proved by the identity), so the leaf tasks can be closed by one line.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

/-- `FmrVelBdd` (now for BUC trains) is `FmrVelBddBUC`, proved by `fmrVelBddBUC`. -/
theorem fmrVelBdd_of_BUC : FmrVelBdd := fmrVelBddBUC

/-- `FmrVelGap` (now for BUC trains) is `FmrVelGapBUC`; `fmrVelGapBUC_of` proves it from the two
leaves and the Part I comparison (SP 291-303, 2955). -/
theorem fmrVelGap_of_parts (hI : FmrVelImage) (hC : FmrVelCompSup)
    (hTC : UnforcedLeray.Short.PartI.TrainComparison) : FmrVelGap :=
  fmrVelGapBUC_of hI hC hTC

/-- `RescaledTrainBounds m` (now for BUC trains) is `RescaledTrainBoundsBUC m`. -/
theorem rescaledTrainBounds_iff_BUC (m : ℝ) : RescaledTrainBounds m ↔ RescaledTrainBoundsBUC m :=
  Iff.rfl

/-- `AdjointExists m` (BUC trains, `ν ≤ ν₀`) from the BUC weak existence, the time-local train
and weighted-jet bounds, and the parabolic regularity of weak solutions
(`adjointExistsBUC_of_regular`). -/
theorem adjointExists_of_BUC (m : ℝ) (hB : LadTrainBddAll m) (hJ : TrainJetsBddAll m)
    (h1 : AdjointWeakExistsBUC m)
    (h2 : AdjointWeakRegular m) : AdjointExists m :=
  adjointExistsBUC_of_regular m hB hJ h1 h2

end UnforcedLeray.Short.IIIa
