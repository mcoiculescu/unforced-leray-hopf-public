import UnforcedLeray.Short.PartIIb.Sub.G4_3_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletIBP
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletT0
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletLap
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.ProfileUnique
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Mem
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Difference
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof

/-!
# Part II-b, task `PartII-b:G4/3` (`AffineColumnComparison`): assembly

Source of record: `the November 2 reference manuscript` (SP), lines 2347-2385
(display `short-bg:affine`). Assembles `affineColumnComparison` from the eight column leaves
(`PartII-b:G4/3/1`..`8`) and the Part I train tail / fixed-band bounds (`PartI:T24`, `PartI:T25`)
through `affineColumnComparison_of` in `Sub/G4_3_org.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.PartI

/-- **Task `PartII-b:G4/3`** (`AffineColumnComparison`, SP 2347-2385): identification of the
unprojected affine column `𝒞_ε`, membership in `H_p`, and `‖𝒞_ε - 𝒞_0‖_{ℝ²→H_p} ≤ Cν^{-k}ε`. -/
theorem affineColumnComparison : UnforcedLeray.Short.IIb.AffineColumnComparison :=
  let hFD0 : OverlapFluctuationDecay := overlap_fluctuation_decay overlap_highnorm_uniform
  let hOv : TrainOverlap :=
    trainOverlap_proof hFD0 (overlap_mean_decay overlap_highnorm_uniform hFD0 overlap_mean_primitive)
  let hVort : TrainVorticityGaussianTail := train_vorticity_gaussian_tail hOv
  let hTails : TrainStreamVelocityPressureTails := train_stream_velocity_pressure_tails hOv hVort
  let hFD : TrainFluctuationDecay := trainFluctuationDecay_proof hTails hFD0 hOv
  let hR : RawJetBound :=
    rawJetBound_of (trainTransverseTails_proof hVort hTails) (trainFixedBand_proof hTails hFD)
  affineColumnComparison_of
    (columnIdentification_of
      (columnPairing_of inletIBP (inletL0Ptw_of inletT0Ptw inletLapPtw) inletBPtw)
      profileUnique
      (columnMem_of hR))
    (columnMem_of hR)
    (columnDifference_of hR)

end UnforcedLeray.Short.IIb

end
