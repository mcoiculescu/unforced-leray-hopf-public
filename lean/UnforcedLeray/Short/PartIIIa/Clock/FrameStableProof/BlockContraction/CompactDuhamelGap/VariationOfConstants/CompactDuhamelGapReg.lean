import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.MildSplitReg

/-!
# Regime form of `blockCompactDuhamelGap_of` (`PartIII-a:T21/c3/2/1`)

Source of record: SP lines 2962-2982.  Same proof as `blockCompactDuhamelGap_of`, from
`ComplBlockDuhamelVoCReg` (regime quantifiers `b ≥ b₀`, `ν ≤ ν₀`): the regime of the gap is
`max b_prop b₀`, `min ν_prop ν₀`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub

/-- Regime form of `blockCompactDuhamelGap_of`. -/
theorem blockCompactDuhamelGapReg_of (κ : PlanarFrameKernels)
    (hProp : DampedComplBlockPropagator κ)
    (hVoC : VariationOfConstantsMildSub.ComplBlockDuhamelVoCReg κ) :
    BlockCompactDuhamelGap κ := by
  intro hκ P hP m hm K C₀ h B α_free δ_gap hC₀ hh hh_le hB hα hδ hSeedDecay hFreeRel
  obtain ⟨M_free, K_A, b_prop, hM_free, hK_A, hb_prop, hU_b⟩ :=
    hProp hκ P hP m hm K C₀ h B α_free δ_gap hC₀ hh hh_le hB hα hδ hSeedDecay hFreeRel
  set C_uh : ℝ := 2 * M_free * Real.exp ((2 * (M_free * K_A) + 1) * B)
  have hC_uh : 0 ≤ C_uh := by positivity
  obtain ⟨b₀, hb₀⟩ := hVoC hκ P hP m hm K B hB
  refine ⟨C_uh, max b_prop b₀, hC_uh, hb_prop.trans (le_max_left _ _), fun b hb => ?_⟩
  have hbp : b_prop ≤ b := (le_max_left _ _).trans hb
  obtain ⟨ν_prop, hν_prop, hU_ν⟩ := hU_b b hbp
  have hb1 : 1 ≤ b := hb_prop.trans hbp
  obtain ⟨ν₀, hν₀, hVν⟩ := hb₀ b ((le_max_right _ _).trans hb) hb1
  refine ⟨min ν_prop ν₀, lt_min hν_prop hν₀, fun ν hν hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq f w u hFlow hCirc => ?_⟩
  dsimp only
  set F := periodizedFrame κ ν m b K hν.1 hF
  obtain ⟨F_rel, A_rel, U_rel, hF_rel, hA_rel, hDuh, hF_bdd, hA_bdd, hU_B0⟩ :=
    hU_ν ν ⟨hν.1, hν.2.trans (min_le_left _ _)⟩ hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
  have hvoc := hVν ν hν.1 (hν.2.trans (min_le_right _ _)) hF tr htr t₁ t₂ ht₁ h12 hbt₂ hB_eq
    F_rel A_rel U_rel hF_rel hA_rel hDuh f w u hFlow hCirc
  have hU_sub : ∀ σ : ℝ, 0 ≤ σ → σ ≤ B → ‖U_rel B σ‖ ≤ C_uh := by
    intro σ hσ0 hσB
    exact hDuh.norm_le (fun _ t s h1 h2 => hF_bdd s t h1 h2) (fun _ r => hA_bdd r)
      () B σ hσB (by linarith)
  have hN12_pos : 0 < clockN P ν t₁ t₂ := clockN_pos P hν.1 ht₁ (ht₁.trans h12)
  have hHom :
      ENNReal.ofReal (clockN P ν t₁ t₂ * ‖U_rel B 0‖) *
          xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁) ≤
        ENNReal.ofReal (clockN P ν t₁ t₂) *
          (ENNReal.ofReal (C₀ * Real.exp (-h * B) + α_free + δ_gap) *
            xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν t₁)) m (compl F w t₁)) := by
    rw [ENNReal.ofReal_mul hN12_pos.le, mul_assoc]
    refine mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hU_B0) zero_le) zero_le
  have hInt :
      (∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal
            ((clockA ν r) ^ (-2 : ℝ) *
              (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖)) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complModeForce κ P F tr r j))) ≤
      ∫⁻ r in Ioc t₁ t₂,
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh)) *
          (∑ j : Fin 2,
            ENNReal.ofReal ‖ampl F w r j‖ *
              xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) m
                (complModeForce κ P F tr r j)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := ht₁.trans hr.1.le
    have ha_pos : 0 < (clockA ν r) ^ (-2 : ℝ) := by
      have ha : 0 < clockA ν r := by
        have := one_le_clockA hν.1.le hr0
        linarith
      exact Real.rpow_pos_of_pos ha _
    have hN_pos : 0 < clockN P ν r t₂ := clockN_pos P hν.1 hr0 (ht₁.trans h12)
    have hz_mem := movingZ_sub_mem_Icc hν.1 ht₁ ⟨hr.1.le, hr.2⟩
    rw [hB_eq] at hz_mem
    have hU_r : ‖U_rel B (movingZ ν r - movingZ ν t₁)‖ ≤ C_uh :=
      hU_sub (movingZ ν r - movingZ ν t₁) hz_mem.1 hz_mem.2
    have hfactor :
        (clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * ‖U_rel B (movingZ ν r - movingZ ν t₁)‖) ≤
          (clockA ν r) ^ (-2 : ℝ) * (clockN P ν r t₂ * C_uh) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hU_r hN_pos.le) ha_pos.le
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hfactor) zero_le
  exact hvoc.trans (add_le_add hHom hInt)

end UnforcedLeray.Short.IIIa
