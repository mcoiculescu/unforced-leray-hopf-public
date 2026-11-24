import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F7
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F5_2
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.FlatGraphD2Slice
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradBound
import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof
import UnforcedLeray.Short.PartIIb.Tasks.HardyL1
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.TrainLp22over3Loc
import UnforcedLeray.Short.PartIIb.Tasks.BodySource.SliceHolder.CylProjection.FlatBvWeakLeibniz
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice.TrainTail
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.TailSourceSlice.SliceP0Lift

/-!
# Part II-b, task `PartII-b:F7/1`: `TailSourceSliceBound` (`short-bg:tail-source`, SP 2269–2282)

Source of record: `the November 2 reference manuscript`
(SP), lines 2269–2282, display `short-bg:tail-source` at line 2281.

This file proves:
1. `ae_hMeas_of_ae_vol_pos`, `hNorm_congr_ae_pos`, `hNorm_sqrtS_congr_ae_pos`,
   `hNorm_mulS_congr_ae_pos`, and `flatGraph_global_hNorm_bounds`: unconditional global `H_p`
   (`p = bgp = 11/4`) bounds
   `hNorm c bgp b0' ≤ ENNReal.ofReal C_G * hNorm c bgp F`,
   `ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0q) ≤ ENNReal.ofReal C_G * hNorm c bgp F`,
   `ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0η) ≤ ENNReal.ofReal C_G * hNorm c bgp F`,
   `ENNReal.ofReal ν * hNorm c bgp (mulS (D2 i j)) ≤ ENNReal.ofReal C_G * hNorm c bgp F`
   for arbitrary representatives `b0', b0q, b0η, D2` satisfying the `HasWeakVec` hypotheses, via
   `flatLerayLiftOfSlice cylinderHelmholtzLr`, `windowBound_with_D2`, `dyadicSummation`,
   `flat_unique`, and `GradBoundHelp.hasWeakVec_unique`;
2. `sliceB1_eq_mul`, `sliceB2_eq_mul`, and `tailSliceRHS_eq`: exact simplification of
   `tailSliceRHS ν c b0' b0q b0η D2 s` for `0 < ν` and `0 < s`:
   `tailSliceRHS ν c b0' b0q b0η D2 s =
     ENNReal.ofReal (s ^ (-63 / 44 : ℝ)) * sliceLpNorm c b0' s +
     ENNReal.ofReal (s ^ (-41 / 44 : ℝ)) *
       (sliceLpNorm c b0q s + sliceLpNorm c b0η s + ∑ i, ∑ j, sliceLpNorm c (D2 i j) s)`;
3. `trainD12Pt`, `norm_flatBv_le_separated`, `norm_flatBvQ_le_separated`,
   `norm_flatBvEta_le_separated`, `sliceH1Norm_flatBv_le_separated`, and
   `sliceH1Norm_flatBv_le_tailSliceRHS`: separated-order `L^{22/3}`–`L^{11/4}` Hölder slice bounds
   bounding `sliceH1Norm c U Uq Uη s` by `ENNReal.ofReal (16 * M) * tailSliceRHS ν c b0' b0q b0η D2 s`;
4. `trainFluctuationDecay_uncond` and `trainMeanExpansion_uncond`: unconditional assembly of Part I
   `TrainFluctuationDecay` (`PartI:T22`) and `TrainMeanExpansion` (`PartI:T23`);
5. `TrainTailLp22over3` and `tailSourceSliceBound_of_leaves`: conditional assembly of
   `TailSourceSliceBound` from `TrainTailLp22over3` and the cylinder Leray projection leaves
   `FlatBvWeakLeibniz`, `FlatBvSliceGoodAe`, `P0SliceLiftH1` (`Tasks/BodySource/SliceHolder/CylProjection.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

namespace TailSliceHelp

/-! ## 1. Unconditional global `H_p` bounds on arbitrary weak-derivative representatives -/

/-- Any relation holding `volume`-a.e. on `{x : Coord | 0 < x.1}` holds `hMeas c bgp`-a.e. -/
theorem ae_hMeas_of_ae_vol_pos {c : ℝ} (hc : 0 < c) {u v : CProf}
    (h : ∀ᵐ x : Coord, 0 < x.1 → u x = v x) :
    u =ᵐ[hMeas c bgp] v := by
  have h1 : ∀ᵐ x ∂hMeas c bgp, 0 < x.1 → u x = v x := (fw_hMeas_ac c bgp) h
  filter_upwards [h1, Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)] with x hx hmem
  exact hx hmem.1

theorem hNorm_congr_ae_pos {c : ℝ} (hc : 0 < c) {u v : CProf}
    (h : ∀ᵐ x : Coord, 0 < x.1 → u x = v x) :
    hNorm c bgp u = hNorm c bgp v :=
  eLpNorm_congr_ae (ae_hMeas_of_ae_vol_pos hc h)

theorem hNorm_sqrtS_congr_ae_pos {c : ℝ} (hc : 0 < c) {u v : CProf}
    (h : ∀ᵐ x : Coord, 0 < x.1 → u x = v x) :
    hNorm c bgp (sqrtS u) = hNorm c bgp (sqrtS v) := by
  refine hNorm_congr_ae_pos hc ?_
  filter_upwards [h] with x hx hpos
  simp [sqrtS, hx hpos]

theorem hNorm_mulS_congr_ae_pos {c : ℝ} (hc : 0 < c) {u v : CProf}
    (h : ∀ᵐ x : Coord, 0 < x.1 → u x = v x) :
    hNorm c bgp (mulS u) = hNorm c bgp (mulS v) := by
  refine hNorm_congr_ae_pos hc ?_
  filter_upwards [h] with x hx hpos
  simp [mulS, hx hpos]

/-- **Unconditional global `H_p` bounds (`p = bgp = 11/4`) on any weak-derivative representatives
`(b0', b0q, b0η, D2)` of a flat response `b0`** (SP 2270–2271):
via `flatLerayLiftOfSlice cylinderHelmholtzLr`, `windowBound_with_D2`, `dyadicSummation`,
`flat_unique`, and `GradBoundHelp.hasWeakVec_unique`, there is a universal constant `C_G > 0` such
that for all `ν > 0`, `c > 0` and any `F, b0, b0', b0q, b0η, D2` satisfying the weak-derivative
hypotheses of `TailSourceSliceBound`,
* `hNorm c bgp b0' ≤ ENNReal.ofReal C_G * hNorm c bgp F`,
* `ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0q) ≤ ENNReal.ofReal C_G * hNorm c bgp F`,
* `ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0η) ≤ ENNReal.ofReal C_G * hNorm c bgp F`,
* `∀ i j, ENNReal.ofReal ν * hNorm c bgp (mulS (D2 i j)) ≤ ENNReal.ofReal C_G * hNorm c bgp F`. -/
theorem flatGraph_global_hNorm_bounds :
    ∃ C_G : ℝ, 0 < C_G ∧
      ∀ {ν c : ℝ}, 0 < ν → 0 < c →
      ∀ (F b0 b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf),
        InHr c bgp F → InFlatClass c bgp b0 → IsFlatResponse ν 0 F b0 →
        (∀ᵐ x : Coord, 0 < x.1 → b0' x = b0 x) →
        HasWeakVec vQ0 dZero b0 b0q → HasWeakVec vEta dZero b0 b0η →
        HasWeakVec vQ0 dZero b0q (D2 0 0) → HasWeakVec vEta dZero b0q (D2 0 1) →
        HasWeakVec vQ0 dZero b0η (D2 1 0) → HasWeakVec vEta dZero b0η (D2 1 1) →
        hNorm c bgp b0' ≤ ENNReal.ofReal C_G * hNorm c bgp F ∧
        ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0q) ≤
          ENNReal.ofReal C_G * hNorm c bgp F ∧
        ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS b0η) ≤
          ENNReal.ofReal C_G * hNorm c bgp F ∧
        (∀ i j, ENNReal.ofReal ν * hNorm c bgp (mulS (D2 i j)) ≤
          ENNReal.ofReal C_G * hNorm c bgp F) := by
  obtain ⟨CL, hCL, hL⟩ := flatLerayLiftOfSlice cylinderHelmholtzLr bgp bgp_gt_one bgp_lt_three
  obtain ⟨K, hK, hWK⟩ := windowBound_with_D2 bgp bgp_gt_one bgp_lt_three
  have ha : 0 < (0 : ℂ).re + (3 / bgp - 1) / 2 := bgp_gap_pos
  set A : ℝ := CL / ((0 : ℂ).re + (3 / bgp - 1) / 2) with hA
  set B : ℝ := CL + A with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact div_nonneg hCL.le ha.le
  have hB0 : 0 ≤ B := by rw [hB]; exact add_nonneg hCL.le hA0
  have hK4 : 0 ≤ 4 * K := mul_nonneg (by norm_num) hK.le
  have hKB : 0 ≤ 4 * K * B := mul_nonneg hK4 hB0
  set C_tot : ℝ := A + 4 * K * B + 1
  have hC_tot : 0 < C_tot := by positivity
  refine ⟨C_tot, hC_tot, fun {ν c} hν hc F b0 b0' b0q b0η D2
      hF hbc0 hb0 hae_b0' hwq hwη hw00 hw01 hw10 hw11 => ?_⟩
  obtain ⟨G, hGH, hGn, hGs, hGp⟩ := hL c hc F hF
  have hbm := duhamelMeasurable bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH
  have hbn := duhamelBound bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH
  have hbper := duhamelPeriodic ν 0 c G hc hGH.periodic
  have hbH : InHr c bgp (flatDuhamel ν 0 G) :=
    ⟨hbper, hbm, lt_of_le_of_lt hbn (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGH.finite)⟩
  have hbs := duhamelSolenoidal bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH hGs hbH
  have hresp : IsFlatResponse ν 0 F (flatDuhamel ν 0 G) := by
    refine ⟨hbs, fun Ψ hΨ => ?_⟩
    obtain ⟨hi1, hi2, he⟩ := duhamelEquation bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH hbH Ψ hΨ
    obtain ⟨hj1, hj2⟩ := hGp Ψ hΨ
    have hsplit := cdot_eq_add_sub F G Ψ
    refine ⟨hi1, ?_, ?_⟩
    · rw [hsplit]; exact hi2.add hj1
    · rw [hsplit, integral_add hi2 hj1, hj2, add_zero]; exact he
  have hfull := duhamelFullEq bgp bgp_gt_one bgp_lt_three 0 ha ν c hν hc G hGH hbH
  set b := flatDuhamel ν 0 G
  have hbF : hNorm c bgp b ≤ ENNReal.ofReal A * hNorm c bgp F := by
    calc hNorm c bgp b ≤ ENNReal.ofReal (1 / ((0 : ℂ).re + (3 / bgp - 1) / 2)) * hNorm c bgp G := hbn
      _ ≤ ENNReal.ofReal (1 / ((0 : ℂ).re + (3 / bgp - 1) / 2)) * (ENNReal.ofReal CL * hNorm c bgp F) := by
          gcongr
      _ = ENNReal.ofReal A * hNorm c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (one_div_pos.mpr ha).le, hA]
          congr 2; ring
  have hP : ENNReal.ofReal (4 * K) * (hNorm c bgp G + hNorm c bgp b) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c bgp F := by
    have hGbF : hNorm c bgp G + hNorm c bgp b ≤ ENNReal.ofReal B * hNorm c bgp F := by
      rw [hB, ENNReal.ofReal_add hCL.le hA0, add_mul]
      exact add_le_add hGn hbF
    calc ENNReal.ofReal (4 * K) * (hNorm c bgp G + hNorm c bgp b)
        ≤ ENNReal.ofReal (4 * K) * (ENNReal.ofReal B * hNorm c bgp F) := by gcongr
      _ = ENNReal.ofReal (4 * K * B) * hNorm c bgp F := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hK4]
  have hPfin : ENNReal.ofReal (4 * K * B) * hNorm c bgp F < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.finite
  obtain ⟨S, Q, E, D2w, hw⟩ := hWK ν c hν hc G b hGH hbH hfull
  obtain ⟨Sb, hSbw, hSbp, hSbm, hSbe⟩ := weakGlue vS fw_vS_smooth c b S
    (fun a ha' => (hw a ha').1) (fun a ha' => (hw a ha').2.2.2.2.2.1)
  obtain ⟨Qb, hQbw, hQbp, hQbm, hQbe⟩ := weakGlue vQ0 fw_vQ0_smooth c b Q
    (fun a ha' => (hw a ha').2.1) (fun a ha' => (hw a ha').2.2.2.2.2.2.1)
  obtain ⟨Eb, hEbw, hEbp, hEbm, hEbe⟩ := weakGlue vEta fw_vEta_smooth c b E
    (fun a ha' => (hw a ha').2.2.1) (fun a ha' => (hw a ha').2.2.2.2.2.2.2.1)
  have hD2_0_on : ∀ j a, 0 < a → HasWeakVecOn (winOpen a) (vDir j) dZero Qb (D2w a 0 j) :=
    fun j a ha' => hasWeakVecOn_congr_left j (hQbe a ha') ((hw a ha').2.2.2.1 j)
  have hD2_1_on : ∀ j a, 0 < a → HasWeakVecOn (winOpen a) (vDir j) dZero Eb (D2w a 1 j) :=
    fun j a ha' => hasWeakVecOn_congr_left j (hEbe a ha') ((hw a ha').2.2.2.2.1 j)
  have hD2_glue : ∀ i j : Fin 2, ∃ Gl : CProf,
      HasWeakVec (vDir j) dZero (if i = 0 then Qb else Eb) Gl ∧
      QPeriodic c Gl ∧ AEStronglyMeasurable Gl volume ∧
      ∀ a : ℝ, 0 < a → ∀ᵐ x ∂(volume : Measure Coord), x ∈ winOpen a → Gl x = D2w a i j x := by
    intro i j
    fin_cases i
    · simpa using weakGlue (vDir j) (vDir_smooth j) c Qb (fun a => D2w a 0 j)
        (hD2_0_on j) (fun a ha' => (hw a ha').2.2.2.2.2.2.2.2.1 0 j)
    · simpa using weakGlue (vDir j) (vDir_smooth j) c Eb (fun a => D2w a 1 j)
        (hD2_1_on j) (fun a ha' => (hw a ha').2.2.2.2.2.2.2.2.1 1 j)
  choose D2g hD2gw _hD2gp hD2gm hD2ge using hD2_glue
  have hpos : ∀ k : ℤ, (0 : ℝ) < (2 : ℝ) ^ k := fun k => zpow_pos (by norm_num) k
  have hSk : ∀ k : ℤ, ENNReal.ofReal 1 * hNormOn c bgp (winOpen ((2 : ℝ) ^ k)) Sb ≤
      ENNReal.ofReal K * (hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [ENNReal.ofReal_one, one_mul, fw_hNormOn_congr (hSbe _ (hpos k))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2.2.1
  have hSn : hNorm c bgp Sb ≤ ENNReal.ofReal (4 * K * B) * hNorm c bgp F := by
    have h := dyadicSummation bgp c bgp_gt_one.le hc Sb G b 1 K zero_le_one hK.le
      (hSbm.mono_ac (fw_hMeas_ac c bgp)) hGH.meas hbH.meas hSk
    rw [ENNReal.ofReal_one, one_mul] at h
    exact h.trans hP
  have hQk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c bgp (winOpen ((2 : ℝ) ^ k)) (sqrtS Qb) ≤
      ENNReal.ofReal K * (hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hQbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2.2.2.1
  have hQn : ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS Qb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c bgp F :=
    (dyadicSummation bgp c bgp_gt_one.le hc (sqrtS Qb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c bgp))) hGH.meas hbH.meas
      hQk).trans hP
  have hEk : ∀ k : ℤ, ENNReal.ofReal (Real.sqrt ν) *
      hNormOn c bgp (winOpen ((2 : ℝ) ^ k)) (sqrtS Eb) ≤
      ENNReal.ofReal K * (hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro k
    rw [fw_hNormOn_congr (fw_sqrtS_ae (hEbe _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2.2.2.2.1
  have hEn : ENNReal.ofReal (Real.sqrt ν) * hNorm c bgp (sqrtS Eb) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c bgp F :=
    (dyadicSummation bgp c bgp_gt_one.le hc (sqrtS Eb) G b (Real.sqrt ν) K (Real.sqrt_nonneg _) hK.le
      (aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c bgp))) hGH.meas hbH.meas
      hEk).trans hP
  have hD2k : ∀ i j : Fin 2, ∀ k : ℤ, ENNReal.ofReal ν *
      hNormOn c bgp (winOpen ((2 : ℝ) ^ k)) (mulS (D2g i j)) ≤
      ENNReal.ofReal K * (hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) G +
        hNormOn c bgp (winSet2 ((2 : ℝ) ^ k)) b) := by
    intro i j k
    rw [fw_hNormOn_congr (fw_mulS_ae (hD2ge i j _ (hpos k)))]
    exact (hw _ (hpos k)).2.2.2.2.2.2.2.2.2.2.2.2 i j
  have hD2n : ∀ i j : Fin 2, ENNReal.ofReal ν * hNorm c bgp (mulS (D2g i j)) ≤
      ENNReal.ofReal (4 * K * B) * hNorm c bgp F := fun i j =>
    (dyadicSummation bgp c bgp_gt_one.le hc (mulS (D2g i j)) G b ν K hν.le hK.le
      (aestronglyMeasurable_mulS ((hD2gm i j).mono_ac (fw_hMeas_ac c bgp))) hGH.meas hbH.meas
      (hD2k i j)).trans hP
  have hsq0 : ENNReal.ofReal (Real.sqrt ν) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hν)).ne'
  have hQfin : hNorm c bgp (sqrtS Qb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hQn hPfin).ne hsq0
  have hEfin : hNorm c bgp (sqrtS Eb) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hEn hPfin).ne hsq0
  have hbc : InFlatClass c bgp b :=
    ⟨hbH, Sb, Qb, Eb, hSbw, hQbw, hEbw,
      ⟨hSbp, hSbm.mono_ac (fw_hMeas_ac c bgp), lt_of_le_of_lt hSn hPfin⟩,
      ⟨qPeriodic_sqrtS hQbp, aestronglyMeasurable_sqrtS (hQbm.mono_ac (fw_hMeas_ac c bgp)), hQfin⟩,
      ⟨qPeriodic_sqrtS hEbp, aestronglyMeasurable_sqrtS (hEbm.mono_ac (fw_hMeas_ac c bgp)), hEfin⟩⟩
  have h0 : b0 - b =ᵐ[hMeas c bgp] 0 :=
    flat_unique hc hν bgp_gt_one bgp_lt_three ha (b0 - b) (flatClassSub c bgp b0 b hbc0 hbc)
      (flatResponseSub ν 0 F b0 b hb0 hresp)
  have hbb0 : b0 =ᵐ[hMeas c bgp] b := by
    filter_upwards [h0] with x hx
    exact sub_eq_zero.mp hx
  have hae_b0_b : ∀ᵐ x : Coord, 0 < x.1 → b0 x = b x :=
    CongrHelp.ae_volume_of_ageμ hc hbc0.inHr.periodic hbc.inHr.periodic hbb0
  have hae_b0'_b : ∀ᵐ x : Coord, 0 < x.1 → b0' x = b x := by
    filter_upwards [hae_b0', hae_b0_b] with x hx1 hx2 hpos
    exact (hx1 hpos).trans (hx2 hpos)
  have hQbw0 : HasWeakVec vQ0 dZero b0 Qb :=
    hasWeakVec_congr hae_b0_b (Eventually.of_forall fun _ _ => rfl) hQbw
  have hEbw0 : HasWeakVec vEta dZero b0 Eb :=
    hasWeakVec_congr hae_b0_b (Eventually.of_forall fun _ _ => rfl) hEbw
  have hae_q : ∀ᵐ x : Coord, 0 < x.1 → b0q x = Qb x :=
    GradBoundHelp.hasWeakVec_unique hwq hQbw0
  have hae_η : ∀ᵐ x : Coord, 0 < x.1 → b0η x = Eb x :=
    GradBoundHelp.hasWeakVec_unique hwη hEbw0
  have hwD2g_00 : HasWeakVec vQ0 dZero b0q (D2g 0 0) :=
    hasWeakVec_congr hae_q (Eventually.of_forall fun _ _ => rfl) (hD2gw 0 0)
  have hwD2g_01 : HasWeakVec vEta dZero b0q (D2g 0 1) :=
    hasWeakVec_congr hae_q (Eventually.of_forall fun _ _ => rfl) (hD2gw 0 1)
  have hwD2g_10 : HasWeakVec vQ0 dZero b0η (D2g 1 0) :=
    hasWeakVec_congr hae_η (Eventually.of_forall fun _ _ => rfl) (hD2gw 1 0)
  have hwD2g_11 : HasWeakVec vEta dZero b0η (D2g 1 1) :=
    hasWeakVec_congr hae_η (Eventually.of_forall fun _ _ => rfl) (hD2gw 1 1)
  have hae_D2 : ∀ i j : Fin 2, ∀ᵐ x : Coord, 0 < x.1 → D2 i j x = D2g i j x := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact GradBoundHelp.hasWeakVec_unique hw00 hwD2g_00
    · exact GradBoundHelp.hasWeakVec_unique hw01 hwD2g_01
    · exact GradBoundHelp.hasWeakVec_unique hw10 hwD2g_10
    · exact GradBoundHelp.hasWeakVec_unique hw11 hwD2g_11
  have hA_le : ENNReal.ofReal A ≤ ENNReal.ofReal C_tot :=
    ENNReal.ofReal_le_ofReal (by dsimp [C_tot]; linarith)
  have hKB_le : ENNReal.ofReal (4 * K * B) ≤ ENNReal.ofReal C_tot :=
    ENNReal.ofReal_le_ofReal (by dsimp [C_tot]; linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hNorm_congr_ae_pos hc hae_b0'_b]
    exact hbF.trans (mul_le_mul_of_nonneg_right hA_le zero_le)
  · rw [hNorm_sqrtS_congr_ae_pos hc hae_q]
    exact hQn.trans (mul_le_mul_of_nonneg_right hKB_le zero_le)
  · rw [hNorm_sqrtS_congr_ae_pos hc hae_η]
    exact hEn.trans (mul_le_mul_of_nonneg_right hKB_le zero_le)
  · intro i j
    rw [hNorm_mulS_congr_ae_pos hc (hae_D2 i j)]
    exact (hD2n i j).trans (mul_le_mul_of_nonneg_right hKB_le zero_le)

/-! ## 2. Exact scaling identities for `sliceB0`, `sliceB1`, `sliceB2`, and `tailSliceRHS` -/

theorem sliceB1_eq_mul {ν c s : ℝ} (hν : 0 ≤ ν) (b0q b0η : CProf) :
    sliceB1 ν c b0q b0η s =
      ENNReal.ofReal (Real.sqrt ν * Real.sqrt s) * (sliceLpNorm c b0q s + sliceLpNorm c b0η s) := by
  unfold sliceB1
  rw [Real.sqrt_mul hν]

theorem sliceB2_eq_mul (ν c s : ℝ) (D2 : Fin 2 → Fin 2 → CProf) :
    sliceB2 ν c D2 s =
      ENNReal.ofReal (ν * s) * ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s :=
  rfl

/-- **Exact identity for `tailSliceRHS` on `0 < ν`, `0 < s`**:
since `sliceB1` carries `√(ν s)` and `sliceB2` carries `ν s`,
`ν⁻¹ * s^{-85/44} * sliceB2 + s^{-63/44} * (ν^{-1/2} * sliceB1 + sliceB0)` equals
`s^{-63/44} * sliceLpNorm c b0' s + s^{-41/44} * (sliceLpNorm c b0q s + sliceLpNorm c b0η s + ∑ i, ∑ j, sliceLpNorm c (D2 i j) s)`. -/
theorem tailSliceRHS_eq {ν c s : ℝ} (hν : 0 < ν) (hs : 0 < s)
    (b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf) :
    tailSliceRHS ν c b0' b0q b0η D2 s =
      ENNReal.ofReal (s ^ (-63 / 44 : ℝ)) * sliceLpNorm c b0' s +
        ENNReal.ofReal (s ^ (-41 / 44 : ℝ)) *
          (sliceLpNorm c b0q s + sliceLpNorm c b0η s +
            ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s) := by
  unfold tailSliceRHS sliceB0
  rw [sliceB1_eq_mul hν.le, sliceB2_eq_mul]
  have h1 : ENNReal.ofReal (ν⁻¹ * s ^ (-85 / 44 : ℝ)) * ENNReal.ofReal (ν * s) =
      ENNReal.ofReal (s ^ (-41 / 44 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hν_ne : ν ≠ 0 := hν.ne'
    have hs_pow : s ^ (-85 / 44 : ℝ) * s = s ^ (-41 / 44 : ℝ) := by
      have hs1 : s ^ (-85 / 44 : ℝ) * s ^ (1 : ℝ) = s ^ (-85 / 44 + 1 : ℝ) :=
        (Real.rpow_add hs (-85 / 44) 1).symm
      rw [Real.rpow_one] at hs1
      rw [hs1]
      congr 1; norm_num
    calc ν⁻¹ * s ^ (-85 / 44 : ℝ) * (ν * s)
        = (ν⁻¹ * ν) * (s ^ (-85 / 44 : ℝ) * s) := by ring
      _ = 1 * s ^ (-41 / 44 : ℝ) := by rw [inv_mul_cancel₀ hν_ne, hs_pow]
      _ = s ^ (-41 / 44 : ℝ) := one_mul _
  have h2 : ENNReal.ofReal (s ^ (-63 / 44 : ℝ)) *
        (ENNReal.ofReal (ν ^ (-1 / 2 : ℝ)) * ENNReal.ofReal (Real.sqrt ν * Real.sqrt s)) =
      ENNReal.ofReal (s ^ (-41 / 44 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hν_sqrt : ν ^ (-1 / 2 : ℝ) * Real.sqrt ν = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hν]
      norm_num
    have hs_sqrt : s ^ (-63 / 44 : ℝ) * Real.sqrt s = s ^ (-41 / 44 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs]
      congr 1; norm_num
    calc s ^ (-63 / 44 : ℝ) * (ν ^ (-1 / 2 : ℝ) * (Real.sqrt ν * Real.sqrt s))
        = (ν ^ (-1 / 2 : ℝ) * Real.sqrt ν) * (s ^ (-63 / 44 : ℝ) * Real.sqrt s) := by ring
      _ = 1 * s ^ (-41 / 44 : ℝ) := by rw [hν_sqrt, hs_sqrt]
      _ = s ^ (-41 / 44 : ℝ) := one_mul _
  rw [← mul_assoc (ENNReal.ofReal (ν⁻¹ * s ^ (-85 / 44 : ℝ))), h1, mul_add,
    ← mul_assoc (ENNReal.ofReal (ν ^ (-1 / 2 : ℝ))),
    ← mul_assoc (ENNReal.ofReal (s ^ (-63 / 44 : ℝ))), h2]
  ring

/-! ## 3. Separated-order pointwise and `L^{22/3}`–`L^{11/4}` Hölder slice bounds -/

/-- Componentwise first-and-second derivative envelope `|Dv_i(s, z)| + |D²v_i(s, z)|`. -/
def trainD12Comp {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ) (i : Fin 2) : ℝ :=
  |trD1 tr (1, 0) s z i| + |trD1 tr (0, 1) s z i| +
    |trD2 tr (1, 0) (1, 0) s z i| + |trD2 tr (1, 0) (0, 1) s z i| +
    |trD2 tr (0, 1) (1, 0) s z i| + |trD2 tr (0, 1) (0, 1) s z i|

/-- Pointwise first-and-second derivative envelope `|Dv(s, z)| + |D²v(s, z)|` (excluding `|v(s, z)|`),
which multiplies the undifferentiated profile `b0'` in `flatBv`, `flatBvQ`, `flatBvEta`. -/
def trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ) : ℝ :=
  ∑ i : Fin 2, trainD12Comp tr s z i

theorem trainD12Comp_nonneg {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ) (i : Fin 2) :
    0 ≤ trainD12Comp tr s z i := by
  unfold trainD12Comp; positivity

theorem trainD12Pt_nonneg {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ) :
    0 ≤ trainD12Pt tr s z := by
  unfold trainD12Pt
  exact Finset.sum_nonneg fun i _ => trainD12Comp_nonneg tr s z i

theorem trainD12Comp_le_trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : trainD12Comp tr s z i ≤ trainD12Pt tr s z :=
  Finset.single_le_sum (fun j _ => trainD12Comp_nonneg tr s z j) (Finset.mem_univ i)

theorem continuous_trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    Continuous (trainD12Pt tr s) := by
  unfold trainD12Pt trainD12Comp
  refine continuous_finsetSum _ fun i _ => ?_
  have h10 := (contDiff_trD1 tr (1, 0) hs i).continuous.abs
  have h01 := (contDiff_trD1 tr (0, 1) hs i).continuous.abs
  have h1010 := (contDiff_trD2 tr (1, 0) (1, 0) hs i).continuous.abs
  have h1001 := (contDiff_trD2 tr (1, 0) (0, 1) hs i).continuous.abs
  have h0110 := (contDiff_trD2 tr (0, 1) (1, 0) hs i).continuous.abs
  have h0101 := (contDiff_trD2 tr (0, 1) (0, 1) hs i).continuous.abs
  exact ((((h10.add h01).add h1010).add h1001).add h0110).add h0101

theorem measurable_trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    Measurable (trainD12Pt tr s) :=
  (continuous_trainD12Pt tr hs).measurable

theorem abs_trD1_10_le_trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD1 tr (1, 0) s z i| ≤ trainD12Pt tr s z := by
  refine le_trans ?_ (trainD12Comp_le_trainD12Pt tr s z i)
  unfold trainD12Comp
  linarith [abs_nonneg (trD1 tr (0, 1) s z i),
    abs_nonneg (trD2 tr (1, 0) (1, 0) s z i), abs_nonneg (trD2 tr (1, 0) (0, 1) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD1_01_le_trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD1 tr (0, 1) s z i| ≤ trainD12Pt tr s z := by
  refine le_trans ?_ (trainD12Comp_le_trainD12Pt tr s z i)
  unfold trainD12Comp
  linarith [abs_nonneg (trD1 tr (1, 0) s z i),
    abs_nonneg (trD2 tr (1, 0) (1, 0) s z i), abs_nonneg (trD2 tr (1, 0) (0, 1) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD2_10_10_le_trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD2 tr (1, 0) (1, 0) s z i| ≤ trainD12Pt tr s z := by
  refine le_trans ?_ (trainD12Comp_le_trainD12Pt tr s z i)
  unfold trainD12Comp
  linarith [abs_nonneg (trD1 tr (1, 0) s z i), abs_nonneg (trD1 tr (0, 1) s z i),
    abs_nonneg (trD2 tr (1, 0) (0, 1) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD2_10_01_le_trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD2 tr (1, 0) (0, 1) s z i| ≤ trainD12Pt tr s z := by
  refine le_trans ?_ (trainD12Comp_le_trainD12Pt tr s z i)
  unfold trainD12Comp
  linarith [abs_nonneg (trD1 tr (1, 0) s z i), abs_nonneg (trD1 tr (0, 1) s z i),
    abs_nonneg (trD2 tr (1, 0) (1, 0) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i), abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD2_01_10_le_trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD2 tr (0, 1) (1, 0) s z i| ≤ trainD12Pt tr s z := by
  refine le_trans ?_ (trainD12Comp_le_trainD12Pt tr s z i)
  unfold trainD12Comp
  linarith [abs_nonneg (trD1 tr (1, 0) s z i), abs_nonneg (trD1 tr (0, 1) s z i),
    abs_nonneg (trD2 tr (1, 0) (1, 0) s z i), abs_nonneg (trD2 tr (1, 0) (0, 1) s z i),
    abs_nonneg (trD2 tr (0, 1) (0, 1) s z i)]

theorem abs_trD2_01_01_le_trainD12Pt {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : ℝ × ℝ)
    (i : Fin 2) : |trD2 tr (0, 1) (0, 1) s z i| ≤ trainD12Pt tr s z := by
  refine le_trans ?_ (trainD12Comp_le_trainD12Pt tr s z i)
  unfold trainD12Comp
  linarith [abs_nonneg (trD1 tr (1, 0) s z i), abs_nonneg (trD1 tr (0, 1) s z i),
    abs_nonneg (trD2 tr (1, 0) (1, 0) s z i), abs_nonneg (trD2 tr (1, 0) (0, 1) s z i),
    abs_nonneg (trD2 tr (0, 1) (1, 0) s z i)]

/-- Pointwise sum of `‖b0q x‖ + ‖b0η x‖ + ∑ i, ∑ j, ‖D2 i j x‖` (the derivatives of `b0'`). -/
def ptD12Sum (b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) : ℝ :=
  ‖b0q x‖ + ‖b0η x‖ + ∑ i : Fin 2, ∑ j : Fin 2, ‖D2 i j x‖

/-- Slice `L^p(Cyl.avgμ c)` sum of `b0q, b0η, D2 i j` at age `s`. -/
def sliceD12Sum (c : ℝ) (b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf) (s : ℝ) : ℝ≥0∞ :=
  sliceLpNorm c b0q s + sliceLpNorm c b0η s + ∑ i : Fin 2, ∑ j : Fin 2, sliceLpNorm c (D2 i j) s

theorem norm_flatBv_apply_le_separated {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf)
    (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) (i : Fin 2) :
    ‖flatBv tr b0' b0q b0η x i‖ ≤
      2 * (trainD12Pt tr x.1 x.2 * ‖b0' x‖ +
        trainJetPt tr x.1 x.2 * ptD12Sum b0q b0η D2 x) := by
  have h1 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 0) (b0q x) i
  have h2 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 1) (b0η x) i
  have h3 := norm_cmerid_mul_real_le (abs_trD1_10_le_trainD12Pt tr x.1 x.2 i) (b0' x) 0
  have h4 := norm_cmerid_mul_real_le (abs_trD1_01_le_trainD12Pt tr x.1 x.2 i) (b0' x) 1
  have htri : ‖flatBv tr b0' b0q b0η x i‖ ≤
      ‖((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i‖ +
      ‖((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i‖ +
      ‖b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ)‖ +
      ‖b0' x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)‖ := by
    change ‖((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i +
        b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ) +
        b0' x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)‖ ≤ _
    linarith [norm_add_le
      (((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i +
        b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ))
      (b0' x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)),
      norm_add_le
      (((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i)
      (b0' x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ)),
      norm_add_le (((tr.v x.1 x.2 0 : ℝ) : ℂ) * b0q x i) (((tr.v x.1 x.2 1 : ℝ) : ℂ) * b0η x i)]
  have hJ := trainJetPt_nonneg tr x.1 x.2
  have hD2 : 0 ≤ ∑ k : Fin 2, ∑ l : Fin 2, ‖D2 k l x‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold ptD12Sum
  nlinarith [norm_nonneg (b0q x), norm_nonneg (b0η x)]

theorem norm_flatBv_le_separated {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf)
    (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) :
    ‖flatBv tr b0' b0q b0η x‖ ≤
      4 * (trainD12Pt tr x.1 x.2 * ‖b0' x‖ +
        trainJetPt tr x.1 x.2 * ptD12Sum b0q b0η D2 x) := by
  have h := cmerid_norm_le_sum (flatBv tr b0' b0q b0η x)
  have h0 := norm_flatBv_apply_le_separated tr b0' b0q b0η D2 x 0
  have h1 := norm_flatBv_apply_le_separated tr b0' b0q b0η D2 x 1
  linarith

theorem norm_flatBvQ_apply_le_separated {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf)
    (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) (i : Fin 2) :
    ‖flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) x i‖ ≤
      3 * (trainD12Pt tr x.1 x.2 * ‖b0' x‖ +
        trainJetPt tr x.1 x.2 * ptD12Sum b0q b0η D2 x) := by
  have h1 := norm_real_mul_cmerid_le (abs_trD1_10_le_trainJetPt tr x.1 x.2 0) (b0q x) i
  have h2 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 0) (D2 0 0 x) i
  have h3 := norm_real_mul_cmerid_le (abs_trD1_10_le_trainJetPt tr x.1 x.2 1) (b0η x) i
  have h4 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 1) (D2 1 0 x) i
  have h5 := norm_cmerid_mul_real_le (abs_trD1_10_le_trainJetPt tr x.1 x.2 i) (b0q x) 0
  have h6 := norm_cmerid_mul_real_le (abs_trD2_10_10_le_trainD12Pt tr x.1 x.2 i) (b0' x) 0
  have h7 := norm_cmerid_mul_real_le (abs_trD1_01_le_trainJetPt tr x.1 x.2 i) (b0q x) 1
  have h8 := norm_cmerid_mul_real_le (abs_trD2_01_10_le_trainD12Pt tr x.1 x.2 i) (b0' x) 1
  set t1 : ℂ := ((trD1 tr (1, 0) x.1 x.2 0 : ℝ) : ℂ) * b0q x i
  set t2 : ℂ := ((tr.v x.1 x.2 0 : ℝ) : ℂ) * D2 0 0 x i
  set t3 : ℂ := ((trD1 tr (1, 0) x.1 x.2 1 : ℝ) : ℂ) * b0η x i
  set t4 : ℂ := ((tr.v x.1 x.2 1 : ℝ) : ℂ) * D2 1 0 x i
  set t5 : ℂ := b0q x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ)
  set t6 : ℂ := b0' x 0 * ((trD2 tr (1, 0) (1, 0) x.1 x.2 i : ℝ) : ℂ)
  set t7 : ℂ := b0q x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)
  set t8 : ℂ := b0' x 1 * ((trD2 tr (0, 1) (1, 0) x.1 x.2 i : ℝ) : ℂ)
  have htri : ‖flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) x i‖ ≤
      ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ + ‖t5‖ + ‖t6‖ + ‖t7‖ + ‖t8‖ := by
    change ‖t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8‖ ≤ _
    linarith [norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8,
      norm_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7,
      norm_add_le (t1 + t2 + t3 + t4 + t5) t6,
      norm_add_le (t1 + t2 + t3 + t4) t5,
      norm_add_le (t1 + t2 + t3) t4,
      norm_add_le (t1 + t2) t3,
      norm_add_le t1 t2]
  have hJ := trainJetPt_nonneg tr x.1 x.2
  have hJ12 := trainD12Pt_nonneg tr x.1 x.2
  unfold ptD12Sum
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  nlinarith [norm_nonneg (b0' x), norm_nonneg (b0q x), norm_nonneg (b0η x),
    norm_nonneg (D2 0 0 x), norm_nonneg (D2 0 1 x), norm_nonneg (D2 1 0 x), norm_nonneg (D2 1 1 x)]

theorem norm_flatBvQ_le_separated {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf)
    (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) :
    ‖flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) x‖ ≤
      6 * (trainD12Pt tr x.1 x.2 * ‖b0' x‖ +
        trainJetPt tr x.1 x.2 * ptD12Sum b0q b0η D2 x) := by
  have h := cmerid_norm_le_sum (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) x)
  have h0 := norm_flatBvQ_apply_le_separated tr b0' b0q b0η D2 x 0
  have h1 := norm_flatBvQ_apply_le_separated tr b0' b0q b0η D2 x 1
  linarith

theorem norm_flatBvEta_apply_le_separated {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf)
    (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) (i : Fin 2) :
    ‖flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) x i‖ ≤
      3 * (trainD12Pt tr x.1 x.2 * ‖b0' x‖ +
        trainJetPt tr x.1 x.2 * ptD12Sum b0q b0η D2 x) := by
  have h1 := norm_real_mul_cmerid_le (abs_trD1_01_le_trainJetPt tr x.1 x.2 0) (b0q x) i
  have h2 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 0) (D2 0 1 x) i
  have h3 := norm_real_mul_cmerid_le (abs_trD1_01_le_trainJetPt tr x.1 x.2 1) (b0η x) i
  have h4 := norm_real_mul_cmerid_le (abs_tr_v_le_trainJetPt tr x.1 x.2 1) (D2 1 1 x) i
  have h5 := norm_cmerid_mul_real_le (abs_trD1_10_le_trainJetPt tr x.1 x.2 i) (b0η x) 0
  have h6 := norm_cmerid_mul_real_le (abs_trD2_10_01_le_trainD12Pt tr x.1 x.2 i) (b0' x) 0
  have h7 := norm_cmerid_mul_real_le (abs_trD1_01_le_trainJetPt tr x.1 x.2 i) (b0η x) 1
  have h8 := norm_cmerid_mul_real_le (abs_trD2_01_01_le_trainD12Pt tr x.1 x.2 i) (b0' x) 1
  set t1 : ℂ := ((trD1 tr (0, 1) x.1 x.2 0 : ℝ) : ℂ) * b0q x i
  set t2 : ℂ := ((tr.v x.1 x.2 0 : ℝ) : ℂ) * D2 0 1 x i
  set t3 : ℂ := ((trD1 tr (0, 1) x.1 x.2 1 : ℝ) : ℂ) * b0η x i
  set t4 : ℂ := ((tr.v x.1 x.2 1 : ℝ) : ℂ) * D2 1 1 x i
  set t5 : ℂ := b0η x 0 * ((trD1 tr (1, 0) x.1 x.2 i : ℝ) : ℂ)
  set t6 : ℂ := b0' x 0 * ((trD2 tr (1, 0) (0, 1) x.1 x.2 i : ℝ) : ℂ)
  set t7 : ℂ := b0η x 1 * ((trD1 tr (0, 1) x.1 x.2 i : ℝ) : ℂ)
  set t8 : ℂ := b0' x 1 * ((trD2 tr (0, 1) (0, 1) x.1 x.2 i : ℝ) : ℂ)
  have htri : ‖flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) x i‖ ≤
      ‖t1‖ + ‖t2‖ + ‖t3‖ + ‖t4‖ + ‖t5‖ + ‖t6‖ + ‖t7‖ + ‖t8‖ := by
    change ‖t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8‖ ≤ _
    linarith [norm_add_le (t1 + t2 + t3 + t4 + t5 + t6 + t7) t8,
      norm_add_le (t1 + t2 + t3 + t4 + t5 + t6) t7,
      norm_add_le (t1 + t2 + t3 + t4 + t5) t6,
      norm_add_le (t1 + t2 + t3 + t4) t5,
      norm_add_le (t1 + t2 + t3) t4,
      norm_add_le (t1 + t2) t3,
      norm_add_le t1 t2]
  have hJ := trainJetPt_nonneg tr x.1 x.2
  have hJ12 := trainD12Pt_nonneg tr x.1 x.2
  unfold ptD12Sum
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  nlinarith [norm_nonneg (b0' x), norm_nonneg (b0q x), norm_nonneg (b0η x),
    norm_nonneg (D2 0 0 x), norm_nonneg (D2 0 1 x), norm_nonneg (D2 1 0 x), norm_nonneg (D2 1 1 x)]

theorem norm_flatBvEta_le_separated {ν c : ℝ} (tr : B0140.TrainSol ν c) (b0' b0q b0η : CProf)
    (D2 : Fin 2 → Fin 2 → CProf) (x : Coord) :
    ‖flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) x‖ ≤
      6 * (trainD12Pt tr x.1 x.2 * ‖b0' x‖ +
        trainJetPt tr x.1 x.2 * ptD12Sum b0q b0η D2 x) := by
  have h := cmerid_norm_le_sum (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) x)
  have h0 := norm_flatBvEta_apply_le_separated tr b0' b0q b0η D2 x 0
  have h1 := norm_flatBvEta_apply_le_separated tr b0' b0q b0η D2 x 1
  linarith

theorem eLpNorm_mul_ptD12Sum_le {c : ℝ} (hc : 0 < c) {W : B0579.Plane → ℝ}
    (hW : Measurable W) (hW0 : ∀ z, 0 ≤ W z) {b0q b0η : CProf}
    {D2 : Fin 2 → Fin 2 → CProf} (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j)) (s : ℝ) :
    eLpNorm (fun z : B0579.Plane => W z * ptD12Sum b0q b0η D2 (s, z)) 2
        (volume.restrict (B0579.cell c)) ≤
      (eLpNorm W (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceD12Sum c b0q b0η D2 s := by
  set μ := volume.restrict (B0579.cell c)
  have hm_u : ∀ {u : CProf}, StronglyMeasurable u →
      AEStronglyMeasurable (fun z : B0579.Plane => W z * ‖u (s, z)‖) μ := fun hu =>
    (hW.mul ((hu.measurable.comp (measurable_const.prodMk measurable_id)).norm)).aestronglyMeasurable
  have h12 : (1 : ℝ≥0∞) ≤ 2 := one_le_two
  have hmq := hm_u hsmq
  have hmη := hm_u hsmη
  have hm00 := hm_u (hsmD2 0 0)
  have hm01 := hm_u (hsmD2 0 1)
  have hm10 := hm_u (hsmD2 1 0)
  have hm11 := hm_u (hsmD2 1 1)
  have heq : (fun z : B0579.Plane => W z * ptD12Sum b0q b0η D2 (s, z)) =
      (((fun z => W z * ‖b0q (s, z)‖) + (fun z => W z * ‖b0η (s, z)‖)) +
        (((fun z => W z * ‖D2 0 0 (s, z)‖) + (fun z => W z * ‖D2 0 1 (s, z)‖)) +
          ((fun z => W z * ‖D2 1 0 (s, z)‖) + (fun z => W z * ‖D2 1 1 (s, z)‖)))) := by
    funext z
    unfold ptD12Sum
    rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Pi.add_apply]
    ring
  rw [heq]
  have h_add1 := eLpNorm_add_le (hmq.add hmη) ((hm00.add hm01).add (hm10.add hm11)) h12
  have h_add2 := eLpNorm_add_le hmq hmη h12
  have h_add3 := eLpNorm_add_le (hm00.add hm01) (hm10.add hm11) h12
  have h_add4 := eLpNorm_add_le hm00 hm01 h12
  have h_add5 := eLpNorm_add_le hm10 hm11 h12
  have hbq := cell_holder_22_3_real hc hW hW0 hsmq s
  have hbη := cell_holder_22_3_real hc hW hW0 hsmη s
  have hb00 := cell_holder_22_3_real hc hW hW0 (hsmD2 0 0) s
  have hb01 := cell_holder_22_3_real hc hW hW0 (hsmD2 0 1) s
  have hb10 := cell_holder_22_3_real hc hW hW0 (hsmD2 1 0) s
  have hb11 := cell_holder_22_3_real hc hW hW0 (hsmD2 1 1) s
  unfold sliceD12Sum
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  calc eLpNorm (((fun z => W z * ‖b0q (s, z)‖) + (fun z => W z * ‖b0η (s, z)‖)) +
          (((fun z => W z * ‖D2 0 0 (s, z)‖) + (fun z => W z * ‖D2 0 1 (s, z)‖)) +
            ((fun z => W z * ‖D2 1 0 (s, z)‖) + (fun z => W z * ‖D2 1 1 (s, z)‖)))) 2 μ
      ≤ (eLpNorm (fun z => W z * ‖b0q (s, z)‖) 2 μ +
          eLpNorm (fun z => W z * ‖b0η (s, z)‖) 2 μ) +
          ((eLpNorm (fun z => W z * ‖D2 0 0 (s, z)‖) 2 μ +
            eLpNorm (fun z => W z * ‖D2 0 1 (s, z)‖) 2 μ) +
          (eLpNorm (fun z => W z * ‖D2 1 0 (s, z)‖) 2 μ +
            eLpNorm (fun z => W z * ‖D2 1 1 (s, z)‖) 2 μ)) := by
        refine h_add1.trans (add_le_add h_add2 (h_add3.trans (add_le_add h_add4 h_add5)))
    _ ≤ ((eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c b0q s +
          eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c b0η s) +
          ((eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c (D2 0 0) s +
            eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c (D2 0 1) s) +
          (eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c (D2 1 0) s +
            eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ)) *
            sliceLpNorm c (D2 1 1) s))) := by
        gcongr
    _ = (eLpNorm W (ENNReal.ofReal (22 / 3)) μ * ENNReal.ofReal (c ^ (4 / 11 : ℝ))) *
          (sliceLpNorm c b0q s + sliceLpNorm c b0η s +
            ((sliceLpNorm c (D2 0 0) s + sliceLpNorm c (D2 0 1) s) +
              (sliceLpNorm c (D2 1 0) s + sliceLpNorm c (D2 1 1) s))) := by
        ring

theorem eLpNorm_le_of_norm_le_separated {ν c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (tr : B0140.TrainSol ν c) {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    {s : ℝ} (hs : 0 ≤ s) {E : Type*} [NormedAddCommGroup E] (F : B0579.Plane → E)
    (hF : ∀ z : B0579.Plane,
      ‖F z‖ ≤ K * (trainD12Pt tr s z * ‖b0' (s, z)‖ +
        trainJetPt tr s z * ptD12Sum b0q b0η D2 (s, z))) :
    eLpNorm F 2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal K *
        ((eLpNorm (trainD12Pt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
            ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceLpNorm c b0' s +
          (eLpNorm (trainJetPt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
            ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceD12Sum c b0q b0η D2 s) := by
  set μ := volume.restrict (B0579.cell c)
  let A_fn : B0579.Plane → ℝ := fun z => trainD12Pt tr s z * ‖b0' (s, z)‖
  let B_fn : B0579.Plane → ℝ := fun z => trainJetPt tr s z * ptD12Sum b0q b0η D2 (s, z)
  have hmA : AEStronglyMeasurable A_fn μ :=
    ((measurable_trainD12Pt tr hs).mul
      ((hsm0.measurable.comp (measurable_const.prodMk measurable_id)).norm)).aestronglyMeasurable
  have hm_u : ∀ {u : CProf}, StronglyMeasurable u →
      Measurable (fun z : B0579.Plane => ‖u (s, z)‖) := fun hu =>
    (hu.measurable.comp (measurable_const.prodMk measurable_id)).norm
  have hm_ptD12 : Measurable (fun z : B0579.Plane => ptD12Sum b0q b0η D2 (s, z)) := by
    unfold ptD12Sum
    exact ((hm_u hsmq).add (hm_u hsmη)).add
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => hm_u (hsmD2 i j))
  have hmB : AEStronglyMeasurable B_fn μ :=
    ((measurable_trainJetPt tr hs).mul hm_ptD12).aestronglyMeasurable
  have hsmul : (fun z : B0579.Plane => K * (A_fn z + B_fn z)) = K • (A_fn + B_fn) := by
    funext z; simp [smul_eq_mul]
  have hA_bd := cell_holder_22_3_real hc (measurable_trainD12Pt tr hs)
    (trainD12Pt_nonneg tr s) hsm0 s
  have hB_bd := eLpNorm_mul_ptD12Sum_le hc (measurable_trainJetPt tr hs)
    (trainJetPt_nonneg tr s) hsmq hsmη hsmD2 s
  calc eLpNorm F 2 μ
      ≤ eLpNorm (fun z : B0579.Plane => K * (A_fn z + B_fn z)) 2 μ := eLpNorm_mono_real hF
    _ = ENNReal.ofReal K * eLpNorm (A_fn + B_fn) 2 μ := by
        rw [hsmul, eLpNorm_const_smul, Real.enorm_eq_ofReal hK]
    _ ≤ ENNReal.ofReal K * (eLpNorm A_fn 2 μ + eLpNorm B_fn 2 μ) :=
        mul_le_mul_of_nonneg_left (eLpNorm_add_le hmA hmB one_le_two) zero_le
    _ ≤ ENNReal.ofReal K *
          ((eLpNorm (trainD12Pt tr s) (ENNReal.ofReal (22 / 3)) μ *
              ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceLpNorm c b0' s +
            (eLpNorm (trainJetPt tr s) (ENNReal.ofReal (22 / 3)) μ *
              ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceD12Sum c b0q b0η D2 s) :=
        mul_le_mul_of_nonneg_left (add_le_add hA_bd hB_bd) zero_le

/-- **Separated-order `H¹(C_c)` slice bound on `flatBv` and its formal Leibniz derivatives**:
`sliceH1Norm c U Uq Uη s` is bounded by `16` times the sum of the `trainD12Pt` `L^{22/3}` norm
paired with `b0'` and the `trainJetPt` `L^{22/3}` norm paired with `(b0q, b0η, D2)`. -/
theorem sliceH1Norm_flatBv_le_separated {ν c : ℝ} (hc : 0 < c)
    (tr : B0140.TrainSol ν c) {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    {s : ℝ} (hs : 0 ≤ s) :
    sliceH1Norm c (flatBv tr b0' b0q b0η)
        (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
        (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s ≤
      ENNReal.ofReal 16 *
        ((eLpNorm (trainD12Pt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
            ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceLpNorm c b0' s +
          (eLpNorm (trainJetPt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
            ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceD12Sum c b0q b0η D2 s) := by
  have hb0 := eLpNorm_le_of_norm_le_separated hc (by norm_num : (0 : ℝ) ≤ 4)
    tr hsm0 hsmq hsmη hsmD2 hs (fun z => flatBv tr b0' b0q b0η (s, z))
    (fun z => norm_flatBv_le_separated tr b0' b0q b0η D2 (s, z))
  have hbq := eLpNorm_le_of_norm_le_separated hc (by norm_num : (0 : ℝ) ≤ 6)
    tr hsm0 hsmq hsmη hsmD2 hs (fun z => flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) (s, z))
    (fun z => norm_flatBvQ_le_separated tr b0' b0q b0η D2 (s, z))
  have hbη := eLpNorm_le_of_norm_le_separated hc (by norm_num : (0 : ℝ) ≤ 6)
    tr hsm0 hsmq hsmη hsmD2 hs (fun z => flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) (s, z))
    (fun z => norm_flatBvEta_le_separated tr b0' b0q b0η D2 (s, z))
  unfold sliceH1Norm
  have h16 : ENNReal.ofReal 4 + ENNReal.ofReal 6 + ENNReal.ofReal 6 = ENNReal.ofReal 16 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  calc eLpNorm (fun z => flatBv tr b0' b0q b0η (s, z)) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0) (s, z)) 2
          (volume.restrict (B0579.cell c)) +
        eLpNorm (fun z => flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1) (s, z)) 2
          (volume.restrict (B0579.cell c))
      ≤ _ := add_le_add (add_le_add hb0 hbq) hbη
    _ = (ENNReal.ofReal 4 + ENNReal.ofReal 6 + ENNReal.ofReal 6) *
          ((eLpNorm (trainD12Pt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
              ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceLpNorm c b0' s +
            (eLpNorm (trainJetPt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
              ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceD12Sum c b0q b0η D2 s) := by
        ring
    _ = ENNReal.ofReal 16 *
          ((eLpNorm (trainD12Pt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
              ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceLpNorm c b0' s +
            (eLpNorm (trainJetPt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
              ENNReal.ofReal (c ^ (4 / 11 : ℝ))) * sliceD12Sum c b0q b0η D2 s) := by
        rw [h16]

/-- Combining `sliceH1Norm_flatBv_le_separated` with `tailSliceRHS_eq`: if at age `s > 0`,
`‖trainD12Pt(s)‖_{22/3} c^{4/11} ≤ M s^{-63/44}` and
`‖trainJetPt(s)‖_{22/3} c^{4/11} ≤ M s^{-41/44}`, then
`sliceH1Norm c U Uq Uη s ≤ ENNReal.ofReal (16 * M) * tailSliceRHS ν c b0' b0q b0η D2 s`. -/
theorem sliceH1Norm_flatBv_le_tailSliceRHS {ν c s M : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 < s)
    (hM : 0 ≤ M) (tr : B0140.TrainSol ν c)
    {b0' b0q b0η : CProf} {D2 : Fin 2 → Fin 2 → CProf}
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    (hD12 : eLpNorm (trainD12Pt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ)) ≤
      ENNReal.ofReal (M * s ^ (-63 / 44 : ℝ)))
    (hJet : eLpNorm (trainJetPt tr s) (ENNReal.ofReal (22 / 3)) (volume.restrict (B0579.cell c)) *
        ENNReal.ofReal (c ^ (4 / 11 : ℝ)) ≤
      ENNReal.ofReal (M * s ^ (-41 / 44 : ℝ))) :
    sliceH1Norm c (flatBv tr b0' b0q b0η)
        (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
        (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s ≤
      ENNReal.ofReal (16 * M) * tailSliceRHS ν c b0' b0q b0η D2 s := by
  have hsep := sliceH1Norm_flatBv_le_separated hc tr hsm0 hsmq hsmη hsmD2 hs.le
  rw [tailSliceRHS_eq hν hs b0' b0q b0η D2]
  change sliceH1Norm c (flatBv tr b0' b0q b0η)
      (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
      (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s ≤
    ENNReal.ofReal (16 * M) *
      (ENNReal.ofReal (s ^ (-63 / 44 : ℝ)) * sliceLpNorm c b0' s +
        ENNReal.ofReal (s ^ (-41 / 44 : ℝ)) * sliceD12Sum c b0q b0η D2 s)
  calc sliceH1Norm c (flatBv tr b0' b0q b0η)
          (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
          (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s
      ≤ ENNReal.ofReal 16 *
          (ENNReal.ofReal (M * s ^ (-63 / 44 : ℝ)) * sliceLpNorm c b0' s +
            ENNReal.ofReal (M * s ^ (-41 / 44 : ℝ)) * sliceD12Sum c b0q b0η D2 s) := by
        refine hsep.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) zero_le)
        · exact mul_le_mul_of_nonneg_right hD12 zero_le
        · exact mul_le_mul_of_nonneg_right hJet zero_le
    _ = ENNReal.ofReal (16 * M) *
          (ENNReal.ofReal (s ^ (-63 / 44 : ℝ)) * sliceLpNorm c b0' s +
            ENNReal.ofReal (s ^ (-41 / 44 : ℝ)) * sliceD12Sum c b0q b0η D2 s) := by
        rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_mul hM, ENNReal.ofReal_mul (by norm_num)]
        ring

/-! ## 4. Unconditional Part I `TrainFluctuationDecay` and `TrainMeanExpansion` assembly -/

theorem overlapFD_uncond : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
  UnforcedLeray.Short.PartI.overlap_fluctuation_decay
    UnforcedLeray.Short.PartI.overlap_highnorm_uniform

theorem trainOverlap_uncond : UnforcedLeray.Short.PartI.TrainOverlap :=
  UnforcedLeray.Short.PartI.trainOverlap_proof overlapFD_uncond
    (UnforcedLeray.Short.PartI.overlap_mean_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform overlapFD_uncond
      UnforcedLeray.Short.PartI.overlap_mean_primitive)

theorem trainStreamVelocityPressureTails_uncond :
    UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
  UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails trainOverlap_uncond
    (UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail trainOverlap_uncond)

/-- Unconditional proof of `PartI.TrainFluctuationDecay` (`PartI:T22`, SP 439–446). -/
theorem trainFluctuationDecay_uncond : UnforcedLeray.Short.PartI.TrainFluctuationDecay :=
  UnforcedLeray.Short.PartI.trainFluctuationDecay_proof
    trainStreamVelocityPressureTails_uncond overlapFD_uncond trainOverlap_uncond

/-- Unconditional proof of `PartI.TrainMeanExpansion` (`PartI:T23`, SP 447–462). -/
theorem trainMeanExpansion_uncond : UnforcedLeray.Short.PartI.TrainMeanExpansion :=
  UnforcedLeray.Short.PartI.trainMeanExpansion_proof
    trainStreamVelocityPressureTails_uncond trainFluctuationDecay_uncond
    UnforcedLeray.Short.PartI.overlap_mean_primitive

end TailSliceHelp

open TailSliceHelp

/-! ## 5. Part I `s ≥ 1` train `L^{22/3}` decay leaf and conditional assembly of `TailSourceSliceBound` -/

/-- **Part I train `L^{22/3}(C_c)` tail decay on `s ≥ 1` (SP 2273–2275)**:
since `1/2 - 1/(2 · 22/3) = 41/44`, `trainFluctuationDecay_uncond` (`sct:fluctuation`) and
`trainMeanExpansion_uncond` (`sct:expansion`) give `C_tr > 0`, `k_tr : ℕ`, `ν_tr > 0` such that in
`BgRegime p d dm dp` with `p.ν ≤ ν_tr`, for every `s ≥ 1`:
* `‖trainJetPt p.train s‖_{L^{22/3}(C_{p.c})} · p.c^{4/11} ≤ C_tr · (p.ν ^ k_tr)⁻¹ · s^{-41/44}`,
* `‖trainD12Pt p.train s‖_{L^{22/3}(C_{p.c})} · p.c^{4/11} ≤ C_tr · (p.ν ^ k_tr)⁻¹ · s^{-63/44}`. -/
def TrainTailLp22over3 : Prop :=
  ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_tr : ℝ) (k_tr : ℕ) (ν_tr : ℝ), 0 < C_tr ∧ 0 < ν_tr ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν_tr →
      ∀ s : ℝ, 1 ≤ s →
        eLpNorm (trainJetPt p.train s) (ENNReal.ofReal (22 / 3))
            (volume.restrict (B0579.cell p.c)) *
          ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) ≤
            ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹ * s ^ (-41 / 44 : ℝ)) ∧
        eLpNorm (trainD12Pt p.train s) (ENNReal.ofReal (22 / 3))
            (volume.restrict (B0579.cell p.c)) *
          ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) ≤
            ENNReal.ofReal (C_tr * (p.ν ^ k_tr)⁻¹ * s ^ (-63 / 44 : ℝ))

/-! ## 6. Unconditional proof of `TrainTailLp22over3` and `TailSourceSliceBound` -/

namespace TailSliceAssemblyAux

open UnforcedLeray.Train (jet)
open UnforcedLeray.Short.PartI (ageJet)

private theorem contDiff_train_v_slice {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (tr.v s) := by
  have hslice : ContDiffOn ℝ ∞ (fun z : B0579.Plane => tr.v s z) univ :=
    tr.isTrain.smooth_v.comp ((contDiffOn_const (c := s)).prodMk contDiffOn_id)
      (fun z _ => (⟨hs, mem_univ z⟩ : ((s, z) : ℝ × B0579.Plane) ∈ Ici 0 ×ˢ univ))
  exact contDiffOn_univ.1 hslice

private theorem abs_tr_v_le_ageJet0 {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) (z : B0579.Plane)
    (i : Fin 2) : |tr.v s z i| ≤ ‖ageJet 0 0 tr.v s z‖ := by
  have h1 : |tr.v s z i| ≤ ‖tr.v s z‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (tr.v s z) i
  have h0 : ‖ageJet 0 0 tr.v s z‖ = ‖tr.v s z‖ := by
    simp [ageJet, jet, iteratedDeriv_zero, norm_iteratedFDeriv_zero]
  linarith

private theorem abs_trD1_le_ageJet1 {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    {d : B0579.Plane} (hd : ‖d‖ ≤ 1) (z : B0579.Plane) (i : Fin 2) :
    |trD1 tr d s z i| ≤ ‖ageJet 0 1 tr.v s z‖ := by
  have hu : ContDiff ℝ ∞ (tr.v s) := contDiff_train_v_slice tr hs
  have hdu : Differentiable ℝ (tr.v s) := hu.differentiable (by simp)
  have heq : trD1 tr d s z i = Dv d (tr.v s) z i := congrFun (Dv_proj hdu d i) z
  rw [heq]
  have h1 : |Dv d (tr.v s) z i| ≤ ‖Dv d (tr.v s) z‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (Dv d (tr.v s) z) i
  have h2 : ‖Dv d (tr.v s) z‖ = ‖iteratedFDeriv ℝ 0 (Dv d (tr.v s)) z‖ :=
    (norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := Dv d (tr.v s)) (x := z)).symm
  have h3 := norm_jet_Dv_le hu d 0 z
  have h4 : ‖iteratedFDeriv ℝ 1 (tr.v s) z‖ = ‖ageJet 0 1 tr.v s z‖ := by
    simp [ageJet, jet, iteratedDeriv_zero]
  nlinarith [norm_nonneg (ageJet 0 1 tr.v s z)]

private theorem abs_trD2_le_ageJet2 {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    {d₁ d₂ : B0579.Plane} (hd₁ : ‖d₁‖ ≤ 1) (hd₂ : ‖d₂‖ ≤ 1) (z : B0579.Plane) (i : Fin 2) :
    |trD2 tr d₁ d₂ s z i| ≤ ‖ageJet 0 2 tr.v s z‖ := by
  have hu : ContDiff ℝ ∞ (tr.v s) := contDiff_train_v_slice tr hs
  have hdu : Differentiable ℝ (tr.v s) := hu.differentiable (by simp)
  have hu1 : ContDiff ℝ ∞ (Dv d₁ (tr.v s)) := contDiff_Dv hu d₁
  have hdu1 : Differentiable ℝ (Dv d₁ (tr.v s)) := hu1.differentiable (by simp)
  have heq : trD2 tr d₁ d₂ s z i = Dv d₂ (Dv d₁ (tr.v s)) z i := by
    unfold trD2
    have hproj1 : (fun w => fderiv ℝ (fun y => tr.v s y i) w d₁) =
        fun w => Dv d₁ (tr.v s) w i := Dv_proj hdu d₁ i
    rw [hproj1]
    exact congrFun (Dv_proj hdu1 d₂ i) z
  rw [heq]
  have h1 : |Dv d₂ (Dv d₁ (tr.v s)) z i| ≤ ‖Dv d₂ (Dv d₁ (tr.v s)) z‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (Dv d₂ (Dv d₁ (tr.v s)) z) i
  have h2 : ‖Dv d₂ (Dv d₁ (tr.v s)) z‖ = ‖iteratedFDeriv ℝ 0 (Dv d₂ (Dv d₁ (tr.v s))) z‖ :=
    (norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := Dv d₂ (Dv d₁ (tr.v s))) (x := z)).symm
  have h3 := (norm_jet_Dv_le hu1 d₂ 0 z).trans (mul_le_of_le_one_left (norm_nonneg _) hd₂)
  have h4 := (norm_jet_Dv_le hu d₁ 1 z).trans (mul_le_of_le_one_left (norm_nonneg _) hd₁)
  have h5 : ‖iteratedFDeriv ℝ 2 (tr.v s) z‖ = ‖ageJet 0 2 tr.v s z‖ := by
    simp [ageJet, jet, iteratedDeriv_zero]
  linarith

theorem trainJetPt_le_ageJets {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (z : B0579.Plane) :
    trainJetPt tr s z ≤
      8 * (‖ageJet 0 0 tr.v s z‖ + ‖ageJet 0 1 tr.v s z‖ + ‖ageJet 0 2 tr.v s z‖) := by
  have hd10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hd01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hcomp : ∀ i : Fin 2,
      |tr.v s z i| +
        |trD1 tr (1, 0) s z i| + |trD1 tr (0, 1) s z i| +
        |trD2 tr (1, 0) (1, 0) s z i| + |trD2 tr (1, 0) (0, 1) s z i| +
        |trD2 tr (0, 1) (1, 0) s z i| + |trD2 tr (0, 1) (0, 1) s z i| ≤
        4 * (‖ageJet 0 0 tr.v s z‖ + ‖ageJet 0 1 tr.v s z‖ + ‖ageJet 0 2 tr.v s z‖) := by
    intro i
    linarith [abs_tr_v_le_ageJet0 tr s z i,
      abs_trD1_le_ageJet1 tr hs hd10 z i, abs_trD1_le_ageJet1 tr hs hd01 z i,
      abs_trD2_le_ageJet2 tr hs hd10 hd10 z i, abs_trD2_le_ageJet2 tr hs hd10 hd01 z i,
      abs_trD2_le_ageJet2 tr hs hd01 hd10 z i, abs_trD2_le_ageJet2 tr hs hd01 hd01 z i,
      norm_nonneg (ageJet 0 0 tr.v s z), norm_nonneg (ageJet 0 1 tr.v s z)]
  unfold trainJetPt
  rw [Fin.sum_univ_two]
  linarith [hcomp 0, hcomp 1]

theorem trainD12Pt_le_ageJets {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (z : B0579.Plane) :
    trainD12Pt tr s z ≤ 8 * (‖ageJet 0 1 tr.v s z‖ + ‖ageJet 0 2 tr.v s z‖) := by
  have hd10 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hd01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
  have hcomp : ∀ i : Fin 2,
      TailSliceHelp.trainD12Comp tr s z i ≤
        4 * (‖ageJet 0 1 tr.v s z‖ + ‖ageJet 0 2 tr.v s z‖) := by
    intro i
    unfold TailSliceHelp.trainD12Comp
    linarith [abs_trD1_le_ageJet1 tr hs hd10 z i, abs_trD1_le_ageJet1 tr hs hd01 z i,
      abs_trD2_le_ageJet2 tr hs hd10 hd10 z i, abs_trD2_le_ageJet2 tr hs hd10 hd01 z i,
      abs_trD2_le_ageJet2 tr hs hd01 hd10 z i, abs_trD2_le_ageJet2 tr hs hd01 hd01 z i,
      norm_nonneg (ageJet 0 1 tr.v s z)]
  unfold TailSliceHelp.trainD12Pt
  rw [Fin.sum_univ_two]
  linarith [hcomp 0, hcomp 1]

theorem continuous_norm_ageJet {ν c : ℝ} (tr : B0140.TrainSol ν c) {s : ℝ} (hs : 0 ≤ s)
    (j : ℕ) : Continuous (fun z : B0579.Plane => ‖ageJet 0 j tr.v s z‖) := by
  have heq : (fun z : B0579.Plane => ‖ageJet 0 j tr.v s z‖) =
      fun z : B0579.Plane => ‖iteratedFDeriv ℝ j (tr.v s) z‖ := by
    funext z; simp [ageJet, jet, iteratedDeriv_zero]
  rw [heq]
  exact ((contDiff_train_v_slice tr hs).continuous_iteratedFDeriv (mod_cast le_top)).norm

theorem loc_lintegral_sliceH1Norm_lt_top {ν c : ℝ} (tr : B0140.TrainSol ν c) (hc : 0 < c)
    (b0' b0q b0η : CProf) (D2 : Fin 2 → Fin 2 → CProf)
    (hb0'_hr : InHr c bgp b0') (hbq_hr : InHr c bgp (sqrtS b0q))
    (hbη_hr : InHr c bgp (sqrtS b0η)) (hD2_hr : ∀ i j, InHr c bgp (mulS (D2 i j)))
    (hsm0 : StronglyMeasurable b0') (hsmq : StronglyMeasurable b0q)
    (hsmη : StronglyMeasurable b0η) (hsmD2 : ∀ i j, StronglyMeasurable (D2 i j))
    (hTr_loc : ∀ a b : ℝ, 0 < a → ∃ C : ℝ, ∀ s ∈ Icc a b,
      trainSliceNorm22_3 c 9 tr s ≤ ENNReal.ofReal C) :
    ∀ a b : ℝ, 0 < a →
      ∫⁻ s in Icc a b,
        sliceH1Norm c (flatBv tr b0' b0q b0η)
          (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
          (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s < ⊤ := by
  intro a b ha
  by_cases hab : a ≤ b
  · let T : ℝ := max b 1
    have hT : 0 < T := lt_of_lt_of_le one_pos (le_max_right b 1)
    have hsub : Icc a b ⊆ Ioc 0 T := fun s hs =>
      ⟨lt_of_lt_of_le ha hs.1, hs.2.trans (le_max_left b 1)⟩
    obtain ⟨C, hC_bd⟩ := hTr_loc a b ha
    let K : ℝ≥0∞ := ENNReal.ofReal 16 * (ENNReal.ofReal C * ENNReal.ofReal (c ^ (4 / 11 : ℝ)))
    have hK_lt : K < ⊤ :=
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    have hm0 := measurable_sliceLpNorm c hsm0
    have hmq := measurable_sliceLpNorm c hsmq
    have hmη := measurable_sliceLpNorm c hsmη
    have hmD2 : ∀ i j, Measurable (sliceLpNorm c (D2 i j)) :=
      fun i j => measurable_sliceLpNorm c (hsmD2 i j)
    have hmSum := measurable_sliceD2Sum c hm0 hmq hmη hmD2
    have hs0_lt : sLpNorm (13 / 8) T (sliceLpNorm c b0') < ⊤ :=
      (sLpNorm_D0_le T _ hm0).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((sLpNorm_sliceLpNorm_le_hNorm c T hsm0).trans_lt hb0'_hr.finite))
    have hsq_lt : sLpNorm (13 / 8) T (sliceLpNorm c b0q) < ⊤ :=
      (sLpNorm_D1_le T _ hmq).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((sLpNorm_sqrtS_sliceLpNorm_le c T hsmq).trans_lt hbq_hr.finite))
    have hsη_lt : sLpNorm (13 / 8) T (sliceLpNorm c b0η) < ⊤ :=
      (sLpNorm_D1_le T _ hmη).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((sLpNorm_sqrtS_sliceLpNorm_le c T hsmη).trans_lt hbη_hr.finite))
    have hsD2_lt : ∀ i j, sLpNorm (13 / 8) T (sliceLpNorm c (D2 i j)) < ⊤ := fun i j => by
      rw [sLpNorm_D2_eq T _ (hmD2 i j)]
      exact (sLpNorm_mulS_sliceLpNorm_le c T (hsmD2 i j)).trans_lt (hD2_hr i j).finite
    have hsSum_lt : sLpNorm (13 / 8) T (sliceD2Sum c b0' b0q b0η D2) < ⊤ := by
      refine (sLpNorm_sliceD2Sum_le (13 / 8) T c hm0 hmq hmη hmD2).trans_lt ?_
      refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
        ⟨hs0_lt, hsq_lt⟩, hsη_lt⟩, ?_⟩
      exact ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr fun j _ => hsD2_lt i j
    have hHardy := hardyL1_proof T hT (sliceD2Sum c b0' b0q b0η D2) hmSum
    change ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s ≤
      ENNReal.ofReal (14 ^ (7 / 11 : ℝ) * T ^ (1 / 22 : ℝ)) *
        sLpNorm (13 / 8) T (sliceD2Sum c b0' b0q b0η D2) at hHardy
    have hIoc_lt : ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s < ⊤ :=
      hHardy.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsSum_lt)
    have hIcc_le : ∫⁻ s in Icc a b,
          sliceH1Norm c (flatBv tr b0' b0q b0η)
            (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
            (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s ≤
        K * ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s := by
      calc ∫⁻ s in Icc a b,
              sliceH1Norm c (flatBv tr b0' b0q b0η)
                (flatBvQ tr b0' b0q b0η (D2 0 0) (D2 1 0))
                (flatBvEta tr b0' b0q b0η (D2 0 1) (D2 1 1)) s
          ≤ ∫⁻ s in Icc a b, K * sliceD2Sum c b0' b0q b0η D2 s := by
            refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
            have hs0 : 0 ≤ s := (lt_of_lt_of_le ha hs.1).le
            refine (sliceH1Norm_flatBv_le hc (by norm_num : (0 : ℝ) ≤ 9) tr
              hsm0 hsmq hsmη hsmD2 hs0).trans ?_
            dsimp only [K]
            gcongr
            exact hC_bd s hs
        _ = K * ∫⁻ s in Icc a b, sliceD2Sum c b0' b0q b0η D2 s :=
            lintegral_const_mul' K _ hK_lt.ne
        _ ≤ K * ∫⁻ s in Ioc 0 T, sliceD2Sum c b0' b0q b0η D2 s :=
            mul_le_mul_of_nonneg_left (lintegral_mono_set hsub) zero_le
    exact hIcc_le.trans_lt (ENNReal.mul_lt_top hK_lt hIoc_lt)
  · rw [Icc_eq_empty hab, Measure.restrict_empty, lintegral_zero_measure]
    exact ENNReal.zero_lt_top

end TailSliceAssemblyAux

/-- **Unconditional proof of `TrainTailLp22over3`** (`s ≥ 1` train `L^{22/3}` decay, SP 2273–2275). -/
theorem trainTailLp22over3_proof : TrainTailLp22over3 := by
  intro dm dp _hdm
  obtain ⟨C₀, k_tr, ν_tr, hC₀, hν_tr, hJet⟩ := TailTrainAux.train_ageJet_lp22_3_tail
  refine ⟨24 * C₀, k_tr, ν_tr, by positivity, hν_tr, ?_⟩
  intro p d hreg hν_le s hs1
  have hs0 : 0 ≤ s := zero_le_one.trans hs1
  obtain ⟨hJ0, hJ1, hJ2⟩ := hJet p d hreg hν_le s hs1
  let μ := volume.restrict (B0579.cell p.c)
  let p22 : ℝ≥0∞ := ENNReal.ofReal (22 / 3)
  have hp1 : 1 ≤ p22 := ENNReal.one_le_ofReal.mpr (by norm_num)
  let g0 : B0579.Plane → ℝ := fun z => ‖UnforcedLeray.Short.PartI.ageJet 0 0 p.train.v s z‖
  let g1 : B0579.Plane → ℝ := fun z => ‖UnforcedLeray.Short.PartI.ageJet 0 1 p.train.v s z‖
  let g2 : B0579.Plane → ℝ := fun z => ‖UnforcedLeray.Short.PartI.ageJet 0 2 p.train.v s z‖
  have hm0 : AEStronglyMeasurable g0 μ :=
    (TailSliceAssemblyAux.continuous_norm_ageJet p.train hs0 0).aestronglyMeasurable
  have hm1 : AEStronglyMeasurable g1 μ :=
    (TailSliceAssemblyAux.continuous_norm_ageJet p.train hs0 1).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable g2 μ :=
    (TailSliceAssemblyAux.continuous_norm_ageJet p.train hs0 2).aestronglyMeasurable
  have hs_exp : s ^ (-63 / 44 : ℝ) ≤ s ^ (-41 / 44 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
  have hM_nn : 0 ≤ C₀ * (p.ν ^ k_tr)⁻¹ := by
    have hνp : 0 < p.ν := p.ν_pos
    positivity
  have hJ1_41 : eLpNorm g1 p22 μ * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) ≤
      ENNReal.ofReal (C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-41 / 44 : ℝ)) :=
    hJ1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs_exp hM_nn))
  have hJ2_41 : eLpNorm g2 p22 μ * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) ≤
      ENNReal.ofReal (C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-41 / 44 : ℝ)) :=
    hJ2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs_exp hM_nn))
  refine ⟨?_, ?_⟩
  · have hpt : eLpNorm (trainJetPt p.train s) p22 μ ≤
        ENNReal.ofReal 8 * (eLpNorm g0 p22 μ + eLpNorm g1 p22 μ + eLpNorm g2 p22 μ) := by
      have h1 : eLpNorm (trainJetPt p.train s) p22 μ ≤
          eLpNorm ((8 : ℝ) • ((g0 + g1) + g2)) p22 μ := by
        refine eLpNorm_mono_real fun z => ?_
        rw [Real.norm_of_nonneg (trainJetPt_nonneg p.train s z)]
        simpa [Pi.smul_apply, Pi.add_apply, smul_eq_mul, g0, g1, g2] using
          TailSliceAssemblyAux.trainJetPt_le_ageJets p.train hs0 z
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 8)] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left
        ((eLpNorm_add_le (hm0.add hm1) hm2 hp1).trans
          (add_le_add (eLpNorm_add_le hm0 hm1 hp1) le_rfl)) zero_le)
    calc eLpNorm (trainJetPt p.train s) p22 μ * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))
        ≤ ENNReal.ofReal 8 * (eLpNorm g0 p22 μ + eLpNorm g1 p22 μ + eLpNorm g2 p22 μ) *
            ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_right hpt zero_le
      _ = ENNReal.ofReal 8 *
            (eLpNorm g0 p22 μ * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) +
              eLpNorm g1 p22 μ * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) +
              eLpNorm g2 p22 μ * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) := by ring
      _ ≤ ENNReal.ofReal 8 *
            (ENNReal.ofReal (C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-41 / 44 : ℝ)) +
              ENNReal.ofReal (C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-41 / 44 : ℝ)) +
              ENNReal.ofReal (C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-41 / 44 : ℝ))) :=
          mul_le_mul_of_nonneg_left (add_le_add (add_le_add hJ0 hJ1_41) hJ2_41) zero_le
      _ = ENNReal.ofReal (24 * C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-41 / 44 : ℝ)) := by
          have hnn : 0 ≤ C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-41 / 44 : ℝ) :=
            mul_nonneg hM_nn (Real.rpow_nonneg hs0 _)
          rw [← ENNReal.ofReal_add hnn hnn, ← ENNReal.ofReal_add (add_nonneg hnn hnn) hnn,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
          congr 1; ring
  · have hpt : eLpNorm (trainD12Pt p.train s) p22 μ ≤
        ENNReal.ofReal 8 * (eLpNorm g1 p22 μ + eLpNorm g2 p22 μ) := by
      have h1 : eLpNorm (trainD12Pt p.train s) p22 μ ≤
          eLpNorm ((8 : ℝ) • (g1 + g2)) p22 μ := by
        refine eLpNorm_mono_real fun z => ?_
        rw [Real.norm_of_nonneg (trainD12Pt_nonneg p.train s z)]
        simpa [Pi.smul_apply, Pi.add_apply, smul_eq_mul, g1, g2] using
          TailSliceAssemblyAux.trainD12Pt_le_ageJets p.train hs0 z
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 8)] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (eLpNorm_add_le hm1 hm2 hp1) zero_le)
    calc eLpNorm (trainD12Pt p.train s) p22 μ * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))
        ≤ ENNReal.ofReal 8 * (eLpNorm g1 p22 μ + eLpNorm g2 p22 μ) *
            ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_right hpt zero_le
      _ = ENNReal.ofReal 8 *
            (eLpNorm g1 p22 μ * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ)) +
              eLpNorm g2 p22 μ * ENNReal.ofReal (p.c ^ (4 / 11 : ℝ))) := by ring
      _ ≤ ENNReal.ofReal 8 *
            (ENNReal.ofReal (C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-63 / 44 : ℝ)) +
              ENNReal.ofReal (C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-63 / 44 : ℝ))) :=
          mul_le_mul_of_nonneg_left (add_le_add hJ1 hJ2) zero_le
      _ = ENNReal.ofReal (16 * C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-63 / 44 : ℝ)) := by
          have hnn : 0 ≤ C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-63 / 44 : ℝ) :=
            mul_nonneg hM_nn (Real.rpow_nonneg hs0 _)
          rw [← ENNReal.ofReal_add hnn hnn, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (24 * C₀ * (p.ν ^ k_tr)⁻¹ * s ^ (-63 / 44 : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          have hs_nn : 0 ≤ (p.ν ^ k_tr)⁻¹ * s ^ (-63 / 44 : ℝ) :=
            mul_nonneg (by have := p.ν_pos; positivity) (Real.rpow_nonneg hs0 _)
          have h16_24 : 16 * C₀ ≤ 24 * C₀ := by linarith
          nlinarith

/-- **Main Theorem (`PartII-b:F7/1`, `TailSourceSliceBound`, SP 2269–2282)**:
unconditional proof of `TailSourceSliceBound` (`short-bg:tail-source`, SP 2281). -/
theorem tailSourceSliceBound_proof : UnforcedLeray.Short.IIb.TailSourceSliceBound := by
  intro dm dp hdm
  obtain ⟨C_G, hC_G, hFG_bd⟩ := flatGraph_global_hNorm_bounds
  obtain ⟨C_tr, k_tr, ν_tr, hC_tr, hν_tr, hTr_bd⟩ := trainTailLp22over3_proof dm dp hdm
  obtain ⟨ν_loc, hν_loc, hTr_loc⟩ :=
    trainWeightedLp22over3Loc_proof 9 (by norm_num : (8 : ℝ) < 9) dm dp hdm
  refine ⟨32 * C_tr, C_G, k_tr, min ν_tr ν_loc, by positivity, hC_G, lt_min hν_tr hν_loc, ?_⟩
  intro p d hreg hν_le F b0 b0' b0q b0η D2
    hF hb0_cls hb0_resp hae_b0' hb0'_hr hbq_hr hbη_hr hD2_hr
    hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11
  have hν_pos : 0 < p.ν := p.ν_pos
  have hc_pos : 0 < p.c := p.c_pos
  have hν_tr_le : p.ν ≤ ν_tr := hν_le.trans (min_le_left _ _)
  have hν_loc_le : p.ν ≤ ν_loc := hν_le.trans (min_le_right _ _)
  obtain ⟨hb0'_bd, hbq_bd, hbη_bd, hD2_bd⟩ :=
    hFG_bd hν_pos hc_pos F b0 b0' b0q b0η D2 hF hb0_cls hb0_resp hae_b0'
      hwq hwη hw00 hw01 hw10 hw11
  refine ⟨hb0'_bd, hbq_bd, hbη_bd, hD2_bd, ?_⟩
  obtain ⟨hwU_q, hwU_η⟩ :=
    flatBvWeakLeibniz_proof p.train hc_pos b0 b0' b0q b0η D2 hb0_cls hae_b0'
      hb0'_hr hbq_hr hbη_hr hD2_hr hsm0 hsmq hsmη hsmD2 hwq hwη hw00 hw01 hw10 hw11
  have hLoc :=
    TailSliceAssemblyAux.loc_lintegral_sliceH1Norm_lt_top p.train hc_pos b0' b0q b0η D2
      hb0'_hr hbq_hr hbη_hr hD2_hr hsm0 hsmq hsmη hsmD2 (hTr_loc p d hreg hν_loc_le)
  obtain ⟨g, gq, gη, hsm_g, hsm_gq, hsm_gη, hg_per, hgwq, hgwη, hg_src', hH1_le⟩ :=
    TailSliceP0LiftAux.p0SliceLiftH1_of_loc p.train hc_pos b0' b0q b0η D2
      hb0'_hr hbq_hr hbη_hr hD2_hr hsm0 hsmq hsmη hsmD2 hwU_q hwU_η hLoc
  have hg_src : IsBodySource p.train b0 b0q b0η g :=
    isBodySource_congr_b0 hae_b0' hg_src'
  refine ⟨g, gq, gη, hg_per, hgwq, hgwη, hg_src,
    CylProjectionSub.measurable_sliceH1Norm_cp p.c hsm_g hsm_gq hsm_gη, ?_⟩
  refine Eventually.of_forall fun s hs1 => ?_
  have hs0 : 0 < s := zero_lt_one.trans_le hs1
  obtain ⟨hJet_s, hD12_s⟩ := hTr_bd p d hreg hν_tr_le s hs1
  have hM_nn : 0 ≤ C_tr * (p.ν ^ k_tr)⁻¹ := by positivity
  have hU_bd := sliceH1Norm_flatBv_le_tailSliceRHS hν_pos hc_pos hs0 hM_nn p.train
    hsm0 hsmq hsmη hsmD2 hD12_s hJet_s
  calc sliceH1Norm p.c g gq gη s
      ≤ ENNReal.ofReal 2 *
          sliceH1Norm p.c (flatBv p.train b0' b0q b0η)
            (flatBvQ p.train b0' b0q b0η (D2 0 0) (D2 1 0))
            (flatBvEta p.train b0' b0q b0η (D2 0 1) (D2 1 1)) s :=
        hH1_le s hs0
    _ ≤ ENNReal.ofReal 2 *
          (ENNReal.ofReal (16 * (C_tr * (p.ν ^ k_tr)⁻¹)) *
            tailSliceRHS p.ν p.c b0' b0q b0η D2 s) :=
        mul_le_mul_of_nonneg_left hU_bd zero_le
    _ = ENNReal.ofReal (32 * C_tr * (p.ν ^ k_tr)⁻¹) *
          tailSliceRHS p.ν p.c b0' b0q b0η D2 s := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
        congr 2
        ring

end UnforcedLeray.Short.IIb

end
