import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Fluct.Interp
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainJetsBoundedFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainFluctAgeJetFixed
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Sub.PartI_T20

/-!
# `PartII-b:S2/wtd/fluct`: Fixed-threshold doubled-weight polynomial bound for stream fluctuation jets

Source of record: `the November 2 reference manuscript`, lines 429–467, 481–526.
Proves `UnforcedLeray.Short.PartIIIb.Concrete.FluctDoubledWeightPoly` unconditionally from
`PartI.train_vorticity_gaussian_tail_zero_pointwise` (via `PartI.trainOverlap_proof`),
`PartI.trainJetsBoundedFixed`, `PartI.trainFluctAgeJetFixed`, and the unit-patch/slice-energy
transverse tail chain in `WeightedTrain/Fluct/{Core,Calc,Interp}.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.WeightedTrainFluctAux

open UnforcedLeray.Short.PartI

theorem vortGaussTailFixed_proof : VortGaussTailFixed := by
  have hFD : OverlapFluctuationDecay := overlap_fluctuation_decay overlap_highnorm_uniform
  have hOv : TrainOverlap :=
    trainOverlap_proof hFD (overlap_mean_decay overlap_highnorm_uniform hFD overlap_mean_primitive)
  intro ρ hρ
  obtain ⟨C', ν₀, hC', hν₀, hpt⟩ := train_vorticity_gaussian_tail_zero_pointwise hOv ρ hρ
  exact ⟨ν₀, hν₀, fun ν hν hle tr htr =>
    ⟨1 / 4, 2, C', 40, by norm_num, by norm_num, hC', by norm_num,
      fun s hs z => hpt ν hν hle tr htr s hs.le z⟩⟩

end UnforcedLeray.Short.IIb.WeightedTrainFluctAux

namespace UnforcedLeray.Short.IIb

/-- **Fixed-threshold doubled-weight polynomial bound for stream fluctuation age/spatial jets
(`PartII-b:S2/wtd/fluct`)**: source lines 429–467, 481–526. -/
theorem fluctDoubledWeightPoly_proof :
    UnforcedLeray.Short.PartIIIb.Concrete.FluctDoubledWeightPoly :=
  WeightedTrainFluctAux.fluctDoubledWeightPoly_of_transverseTail
    UnforcedLeray.Short.PartI.trainFluctAgeJetFixed
    (WeightedTrainFluctAux.fluctTransverseTailFixed_of_gauss
      WeightedTrainFluctAux.vortGaussTailFixed_proof
      UnforcedLeray.Short.PartI.trainJetsBoundedFixed
      UnforcedLeray.Short.PartI.trainFluctAgeJetFixed)

end UnforcedLeray.Short.IIb
