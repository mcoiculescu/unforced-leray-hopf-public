import UnforcedLeray.Short.Spine.Assembly

/-!
# Spine: global existence of the train (task `Spine:SP-TRAIN`)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic Theorem 1.1 and Remark 1.3(2) after swapping coordinates; the finite-energy
and `L²`-continuation estimate at lines 278-285; central oddness by uniqueness).

`Spine:SP-TRAIN` is a coordination task. Its target `Short.PartI.TrainGlobalExistence` is the very
statement of the Part I train area's task `PartI:T04` (`trainGlobalExistence_proof`), whose own
chain is `PartI:T02` (local classical train: mild `H³` solution, weak Navier-Stokes, parabolic
bootstrap, Leray pressure and Biot-Savart stream with decay gauge, oddness by uniqueness) and
`PartI:T03` (vorticity `L^1`, `L^∞` bounds and zero circulation). The Spine should not duplicate
that proof, and the INF16 named hypotheses `B0141.LocalWellPosed`, `B0141.AprioriH3` and
`B0141.HmUnique` stay unused.

`trainGlobalExistence_of` is the conditional statement (the Part I area's result gives the Spine's
`trainGlobalExistence`), and `trainExistence_of_partI` records the first consumer: with `PartI:T04`
proved, the library's `B0140.TrainExistence` follows by the compiled bridge
`Spine.trainExistence_of_global`. The unconditional `trainGlobalExistence` is the task
`Spine:SP-TRAIN` (`Short/Spine/Proofs/TrainGlobalExistence.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Spine

/-- **Global existence of the train, as proved by the Part I area** (`PartI:T04`, source lines
261-288): for every `ν > 0`, `c ≥ 1` the global smooth finite-energy train in the BUC class with the periodized Gaussian
datum, decaying stream and pressure gauge, and central oddness exists. This is the unmodified
`Short.PartI.TrainGlobalExistence`. -/
def PartIGlobalTrain : Prop := PartI.TrainGlobalExistence

/-- **Conditional**: the Part I area's global existence gives the Spine's target. -/
theorem trainGlobalExistence_of (h : PartIGlobalTrain) : PartI.TrainGlobalExistence := h

/-- The existence of the train in the BUC class (period `c = ν^{-2}`, small `ν`) from the Part I
area's global existence: the existence input of `PartIOutput`. -/
theorem trainBUCExistence_of_partI (h : PartIGlobalTrain) : TrainBUCExistence :=
  trainBUCExistence_of_global (trainGlobalExistence_of h)

/-- The library's `B0140.TrainExistence` (period `c = ν^{-2}`, small `ν`) from the Part I area's
global existence. -/
theorem trainExistence_of_partI (h : PartIGlobalTrain) : B0140.TrainExistence :=
  trainExistence_of_global (trainGlobalExistence_of h)

end UnforcedLeray.Short.Spine

end
