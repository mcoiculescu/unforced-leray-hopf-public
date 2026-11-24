import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_6_1_3_1_org_1_org_1_1_2
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Mean.Stress
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Mean.Datum
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder.WeightedTrain.Mean.Source

/-!
# Shared task `PartII-b:S2/wtd/mean`: `WeightedTrainMeanRemMixedFixed`

Source of record: `the November 2 reference manuscript` (SP), lines 429–467 and
516–551.

Proves `UnforcedLeray.Short.PartIIIb.Concrete.WeightedTrainMeanRemMixedFixed` unconditionally at a
single smallness threshold `ν₀ > 0` depending only on `ρ > 1/2`:
1. `PartI.trainMeanStreamDuhamel_proof` gives the Duhamel splitting
   `∂_η^b ∂_s^ℓ (meanRemainder tr N) = ∂_η^b ∂_s^ℓ (meanDatumRemainder tr N) +
   ∂_η^b ∂_s^ℓ (meanSourceRemainder tr N)` (`PartI_T23.meanRemainder_slice_eq_add_of_duhamel`) for
   all `0 < ν ≤ ν_duh`.
2. `WeightedTrainMeanAux.meanStress_weighted_jet_fixed` (`Mean/Stress.lean`) provides all-weight,
   all-order exponential decay of `meanStress` for all `0 < ν ≤ ν_st`.
3. `WeightedTrainMeanAux.weightedMeanDatumRemainder_fixed` (`Mean/Datum.lean`) and
   `WeightedTrainMeanAux.weightedMeanSourceRemainder_fixed` (`Mean/Source.lean`) bound
   `|η| ^ m' * |∂_η^b ∂_s^ℓ R_N(s, η)|` at both `m' = 0` and `m' = m`; combining with
   `(1 + |η|) ^ m ≤ 2 ^ m * (1 + |η| ^ m)` yields the `(1 + |η|) ^ m`-weighted bound.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short

/-- **Weighted mixed mean-remainder bound at fixed parameters** (`PartII-b:S2/wtd/mean`,
SP 429–467, 516–551). -/
theorem weightedTrainMeanRemMixedFixed_proof :
    UnforcedLeray.Short.PartIIIb.Concrete.WeightedTrainMeanRemMixedFixed := by
  intro ρ hρ
  have hOv : PartI.TrainOverlap :=
    PartI.trainOverlap_proof
      (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof)
      (PartI.overlap_mean_decay_of PartI.overlapHighNormUniform_proof
        (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof)
        PartI.overlap_mean_primitive PartI.overlap_mean_duhamel_split)
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv (PartI.train_vorticity_gaussian_tail hOv)
  have hFD : PartI.TrainFluctuationDecay :=
    PartI.trainFluctuationDecay_proof hTails
      (PartI.overlap_fluctuation_decay PartI.overlapHighNormUniform_proof) hOv
  obtain ⟨ν_duh, hν_duh, hDuhAll⟩ :=
    PartI.trainMeanStreamDuhamel_proof hTails hFD PartI.overlap_mean_primitive ρ hρ
  obtain ⟨ν_st, hν_st, hStAll⟩ := WeightedTrainMeanAux.meanStress_weighted_jet_fixed ρ hρ
  refine ⟨min (min ν_duh ν_st) (1 / 2), lt_min (lt_min hν_duh hν_st) (by norm_num), ?_⟩
  intro ν hν hν_le tr htr N m b ℓ
  have hν_duh_le : ν ≤ ν_duh := hν_le.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν_st_le : ν ≤ ν_st := hν_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν_half : ν ≤ 1 / 2 := hν_le.trans (min_le_right _ _)
  have hν1 : ν ≤ 1 := by linarith
  let c := PartI.trainPeriod ρ ν
  have hc1 : 1 ≤ c := by
    dsimp [c, PartI.trainPeriod]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν hν1 (by linarith)
  have hDuh := hDuhAll ν hν hν_duh_le tr htr
  have hStress : WeightedTrainMeanAux.HasWeightedMeanStressDecay tr :=
    hStAll ν hν hν_st_le tr htr
  obtain ⟨C_d0, M_d0, hCd0, hBd0⟩ :=
    WeightedTrainMeanAux.weightedMeanDatumRemainder_fixed hν hν1 hc1 tr N 0 b ℓ
  obtain ⟨C_s0, M_s0, hCs0, hBs0⟩ :=
    WeightedTrainMeanAux.weightedMeanSourceRemainder_fixed hν hν1 hc1 tr htr hDuh hStress N 0 b ℓ
  obtain ⟨C_dm, M_dm, _hCdm, hBdm⟩ :=
    WeightedTrainMeanAux.weightedMeanDatumRemainder_fixed hν hν1 hc1 tr N m b ℓ
  obtain ⟨C_sm, M_sm, _hCsm, hBsm⟩ :=
    WeightedTrainMeanAux.weightedMeanSourceRemainder_fixed hν hν1 hc1 tr htr hDuh hStress N m b ℓ
  set P₀ : ℝ := PartI.polyP C_d0 M_d0 ν c + PartI.polyP C_s0 M_s0 ν c
  set Pₘ : ℝ := PartI.polyP C_dm M_dm ν c + PartI.polyP C_sm M_sm ν c
  refine ⟨(2 : ℝ) ^ m * (P₀ + Pₘ), fun s hs η => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs
  rw [Real.norm_eq_abs]
  have hsplit := PartI.PartI_T23.meanRemainder_slice_eq_add_of_duhamel
    hν hc1 tr htr hDuh N b ℓ hs0 η
  set α₀ : ℝ := ((0 : ℝ) - b - 2 * N - 3) / 2 - ℓ
  set α : ℝ := (((m : ℝ) - (b : ℝ)) - 2 * N - 3) / 2 - ℓ
  have hα₀_le : α₀ ≤ α := by
    dsimp [α₀, α]
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hrpow_le : s ^ α₀ ≤ s ^ α := Real.rpow_le_rpow_of_exponent_le hs hα₀_le
  have hP₀_nn : 0 ≤ P₀ := by
    dsimp [P₀]
    unfold PartI.polyP
    have hc0 : 0 ≤ c := zero_le_one.trans hc1
    have hν_inv : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
    positivity
  have h0_bd :
      |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanRemainder tr N r e) s) η| ≤
        P₀ * s ^ α := by
    rw [hsplit]
    have hd := hBd0 s hs η
    have hsrc := hBs0 s hs η
    simp only [pow_zero, one_mul, Nat.cast_zero] at hd hsrc
    calc |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanDatumRemainder tr N r e) s) η +
            iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanSourceRemainder tr N r e) s) η|
        ≤ |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanDatumRemainder tr N r e) s) η| +
            |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanSourceRemainder tr N r e) s) η| :=
          abs_add_le _ _
      _ ≤ PartI.polyP C_d0 M_d0 ν c * s ^ α₀ + PartI.polyP C_s0 M_s0 ν c * s ^ α₀ :=
          add_le_add hd hsrc
      _ = P₀ * s ^ α₀ := by dsimp [P₀]; ring
      _ ≤ P₀ * s ^ α := mul_le_mul_of_nonneg_left hrpow_le hP₀_nn
  have hm_bd :
      |η| ^ m *
        |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanRemainder tr N r e) s) η| ≤
        Pₘ * s ^ α := by
    rw [hsplit]
    have hd := hBdm s hs η
    have hsrc := hBsm s hs η
    calc |η| ^ m *
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanDatumRemainder tr N r e) s) η +
            iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanSourceRemainder tr N r e) s) η|
        ≤ |η| ^ m *
            (|iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanDatumRemainder tr N r e) s) η| +
              |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanSourceRemainder tr N r e) s) η|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ = |η| ^ m *
            |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanDatumRemainder tr N r e) s) η| +
          |η| ^ m *
            |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanSourceRemainder tr N r e) s) η| := by
          ring
      _ ≤ PartI.polyP C_dm M_dm ν c * s ^ α + PartI.polyP C_sm M_sm ν c * s ^ α :=
          add_le_add hd hsrc
      _ = Pₘ * s ^ α := by dsimp [Pₘ]; ring
  have hw_pow : (1 + |η|) ^ m ≤ (2 : ℝ) ^ m * (1 + |η| ^ m) :=
    PartIIa.pow_one_add_le m (abs_nonneg η)
  calc (1 + |η|) ^ m *
        |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanRemainder tr N r e) s) η|
      ≤ ((2 : ℝ) ^ m * (1 + |η| ^ m)) *
          |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanRemainder tr N r e) s) η| :=
        mul_le_mul_of_nonneg_right hw_pow (abs_nonneg _)
    _ = (2 : ℝ) ^ m *
          (|iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanRemainder tr N r e) s) η| +
            |η| ^ m *
              |iteratedDeriv b (fun e => iteratedDeriv ℓ (fun r => PartI.meanRemainder tr N r e) s) η|) := by
        ring
    _ ≤ (2 : ℝ) ^ m * (P₀ * s ^ α + Pₘ * s ^ α) :=
        mul_le_mul_of_nonneg_left (add_le_add h0_bd hm_bd) (by positivity)
    _ = ((2 : ℝ) ^ m * (P₀ + Pₘ)) * s ^ α := by ring

end UnforcedLeray.Short.IIb
