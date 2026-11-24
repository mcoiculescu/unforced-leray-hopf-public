import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.HeatFieldJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.RingLiftPtJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.RingProfileMeridJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.TrainStreamWtdBdd_Sub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2.WtdJetInterp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2.MeanJetsFixed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1.MeanJetFormula
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_2_2_1_2.PsiJetInterior
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainFluctAgeJetFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainJetsBoundedFixed
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromAgeJets
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.JointFromMixed1D
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth.RawParityForm.HeatTermSmooth
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Fluct
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Mean

/-!
# `PartII-b:S2/1/1`: `RawAllDerivsBdd`, reduced to two fixed-parameter weighted train leaves

Source of record: `the November 2 reference manuscript`
(SP), lines 1217-1219, 1322-1325, 2541-2559.

`rawAllDerivsBdd_of_offAxis` reduces `RawAllDerivsBdd` to `RingLiftOffAxisDerivBdd`, which
`ringLiftOffAxisDerivBdd_of` assembles from `TrainHeatRemWtd`, `TrainStreamWtdBdd` and three
proved jet leaves.  Every remaining input is closed here except the two fixed-parameter weighted
train estimates (one threshold `ν₀` for all orders):

* `WeightedTrainFluctAgeJetFixed` (SP 439-445 with the weight, proof SP 516-526), equivalently
  `FluctDoubledWeightPoly` given the proved `PartI.trainFluctAgeJetFixed`;
* `WeightedTrainMeanRemMixedFixed` (SP 455-458, proof SP 527-551).

`PsiJetWtd` is closed from `PartI.trainTransverseTails_proof` and `psiJetInterior`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.PartIIIb.Concrete

/-- `PsiJetWtd` from the proved transverse tails (Part I overlap chain) and `psiJetInterior`. -/
theorem psiJetWtd_s211 : PsiJetWtd := by
  have hFD0 : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hFD0
      (UnforcedLeray.Short.PartI.overlap_mean_decay
        UnforcedLeray.Short.PartI.overlap_highnorm_uniform hFD0
        UnforcedLeray.Short.PartI.overlap_mean_primitive)
  have hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  exact psiJetWtd_of (UnforcedLeray.Short.PartI.trainTransverseTails_proof hVort hTails)
    _root_.psiJetInterior

/-- Bounded-age form of the weighted fluctuation leaf (the proof of `trainFluctWtdAgeJet_of`,
restated against the `WeightedTrainFluctAgeJetFixed` of `..._org_1_1_1`, whose text is identical to
the copy in `..._org_1_1/TrainFluctWtdFixed.lean`; the two modules cannot be imported together). -/
theorem trainFluctWtdAgeJet_of_s211 (h : WeightedTrainFluctAgeJetFixed) :
    TrainFluctWtdAgeJet := by
  intro ρ hρ
  obtain ⟨ν₀, hν₀, h'⟩ := h ρ hρ
  refine ⟨ν₀, hν₀, fun ν c hν hle hc tr htr m ℓ j S => ?_⟩
  subst hc
  obtain ⟨C, κ, hκ, hC⟩ := h' ν hν hle tr htr m ℓ j
  refine ⟨|C|, fun s hs _ z => ?_⟩
  have he0 : 0 ≤ Real.exp (-(κ * s)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(κ * s)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hκ.le hs.le))
  calc (1 + |z.2|) ^ m * ‖Short.PartI.ageJet ℓ j
          (fun r w => tr.ψ r w - Short.PartI.hmean (Short.PartI.trainPeriod ρ ν) (tr.ψ r) w.2) s z‖
      ≤ C * Real.exp (-(κ * s)) := hC s hs z
    _ ≤ |C| * Real.exp (-(κ * s)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) he0
    _ ≤ |C| := mul_le_of_le_one_right (abs_nonneg C) he1

/-- `TrainMeanWtdBdd` (one threshold for all orders), closed. -/
theorem trainMeanWtdBdd_s211 : TrainMeanWtdBdd :=
  trainMeanWtdBdd_of (trainMeanWtdMixed_of psiJetWtd_s211 meanJetFormula)
    (meanJetsFixed_of UnforcedLeray.Short.PartI.trainJetsBoundedFixed) wtdJetInterp

/-- **`RawAllDerivsBdd` from the two fixed-parameter weighted train leaves.** -/
theorem rawAllDerivsBdd_of_wtdLeaves (hF : WeightedTrainFluctAgeJetFixed)
    (hM : WeightedTrainMeanRemMixedFixed) : RawAllDerivsBdd :=
  rawAllDerivsBdd_of_offAxis
    (ringLiftOffAxisDerivBdd_of
      (trainHeatRemWtd_of UnforcedLeray.Short.PartI.trainStreamSmooth
        UnforcedLeray.Short.PartI.trainMeanEquations_proof heatTermSmooth
        (trainFluctWtdFixed_of UnforcedLeray.Short.PartI.trainStreamSmooth
          UnforcedLeray.Short.PartI.trainMeanEquations_proof
          UnforcedLeray.Short.PartI.jointFromAgeJets hF)
        (trainMeanRemWtdFixed_of UnforcedLeray.Short.PartI.trainMeanEquations_proof
          heatTermSmooth UnforcedLeray.Short.PartI.jointFromMixed1D hM))
      (trainStreamWtdBdd_of (trainFluctWtdBdd_of (trainFluctWtdAgeJet_of_s211 hF))
        trainMeanWtdBdd_s211)
      ringLiftPtJet ringProfileMeridJet heatFieldJet)

/-- The same reduction with the fluctuation leaf replaced by the doubled-weight polynomial datum
(`weightedTrainFluctAgeJetFixed_of` and the proved `PartI.trainFluctAgeJetFixed`). -/
theorem rawAllDerivsBdd_of_doubledWeight (hD : FluctDoubledWeightPoly)
    (hM : WeightedTrainMeanRemMixedFixed) : RawAllDerivsBdd :=
  rawAllDerivsBdd_of_wtdLeaves
    (weightedTrainFluctAgeJetFixed_of UnforcedLeray.Short.PartI.trainFluctAgeJetFixed hD) hM

/-- **Globally bounded spatial derivatives of `p.raw τ` of all orders (`PartII-b:S2/1/1`)**:
source lines 1217-1219, 1322-1325, 2541-2559. -/
theorem rawAllDerivsBdd_proof : UnforcedLeray.Short.IIb.RawAllDerivsBdd :=
  rawAllDerivsBdd_of_doubledWeight fluctDoubledWeightPoly_proof
    weightedTrainMeanRemMixedFixed_proof

end UnforcedLeray.Short.IIb

end
