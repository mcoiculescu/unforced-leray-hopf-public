import UnforcedLeray.Short.PartI.Sub.PartI_T21
import UnforcedLeray.Short.PartI.Sub.PartI_T21.TransverseTail
import UnforcedLeray.Short.PartI.Sub.PartI_T21.WeightedJetBounds

/-!
# `PartI:T21` (`TrainStreamTails.lean`): transverse tails and weighted bounds for `(ψ, v, p)`

Source of record: `the November 2 reference manuscript`, lines 499-526
(old 493-515), in the proof of Lemma `sct:heat`.

All proved stream/mean-stream evenness theorems (`PartI_T21.train_stream_even`,
`PartI_T21.train_meanStream_even`, `PartI_T21.train_meanStream_even_all`), the `wCellL2`-from-`wSupNorm`
reduction (`PartI_T21.wCellL2_le_of_wSupNorm_add_two`, `PartI_T21.trainWeightedJetBounds_of_wSupNorm`),
the leaf propositions `TrainStreamVelocityPressureTransverseTail` (`PartI:T21/1`) and
`TrainWeightedJetBounds` (`PartI:T21/2`), and the conditional assembly
`train_stream_velocity_pressure_tails_of` are in `UnforcedLeray.Short.PartI.Sub.PartI_T21`.

Once `PartI:T21/1` and `PartI:T21/2` are proved, the unconditional theorem
`train_stream_velocity_pressure_tails` is obtained by applying
`train_stream_velocity_pressure_tails_of trainStreamVelocityPressureTransverseTail_proof trainWeightedJetBounds_proof hOv hVort`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem train_stream_velocity_pressure_tails (hOv : TrainOverlap) (hVort : TrainVorticityGaussianTail) : TrainStreamVelocityPressureTails := by
  exact train_stream_velocity_pressure_tails_of trainStreamVelocityPressureTransverseTail_proof trainWeightedJetBounds_proof hOv hVort

end UnforcedLeray.Short.PartI

