import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressEpsLocalH14.StressEpsCommutingFlowShiftQ.CutoffShift

/-!
# Transverse (`shiftEta`) leaf `PhaseDissipationCutoffShiftEta` for `PartII-a:N05/3/1`

Source of record: `the November 2 reference manuscript`,
lines 1782–1785 (`near:local-smoothing`).

Proves `phaseDissipationCutoffShiftEta : PhaseDissipationCutoffShiftEta` by combining:
1. `lintegral_profileBox_shiftEta_sub_sq_eq` (`shiftEta h` ↔ `shearZ (h * ε)` on `phaseVol P`),
2. `lintegral_phaseVol_shearZ_sub_sq_le` with displacement bound `|(h * ε) * radius y| ≤ |h| * (√σ)⁻¹`
   on `spaceBox ε σ H1 (L1 + 1)`, and
3. the cutoff-shift commutator bound from `CutoffShift.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N05FlowAux

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp UnforcedLeray.FreeStress
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open N05_1Aux N05_3Aux N05_4Aux N05_3_1Aux

private theorem cutoffShiftEta_ennreal_consolidation {Gam H1 σ cN nW ng2 N_W h : ℝ}
    (hG1 : 1 ≤ Gam) (hσ : 0 < σ) (hσH : σ ≤ H1)
    (h1H1 : 1 + H1 ≤ Gam) (hσ_sqrt : (Real.sqrt σ)⁻¹ ≤ Gam)
    (hcN0 : 0 ≤ cN) (hcN : cN ≤ Gam)
    (hnW0 : 0 ≤ nW) (hnW : nW ≤ N_W)
    (hng20 : 0 ≤ ng2) (hng2 : ng2 ≤ N_W) (hNW0 : 0 ≤ N_W)
    (hh : h ∈ Icc (-1 : ℝ) 1) :
    2 * (ENNReal.ofReal (((1 + H1) * cN) ^ 2) *
          ENNReal.ofReal (2 * (|h| * (Real.sqrt σ)⁻¹) ^ 2 * ng2 ^ 2)) +
      2 * ENNReal.ofReal (((1 + H1) * (cN * |h|) * nW) ^ 2) ≤
      ENNReal.ofReal ((6 * Gam ^ 3 * N_W) ^ 2 * |h|) := by
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hh1 : |h| ≤ 1 := abs_le.2 ⟨hh.1, hh.2⟩
  have hh_sq : |h| ^ 2 ≤ |h| := by
    calc |h| ^ 2 = |h| * |h| := sq |h|
      _ ≤ 1 * |h| := mul_le_mul_of_nonneg_right hh1 (abs_nonneg h)
      _ = |h| := one_mul |h|
  have hcut_G2 : (1 + H1) * cN ≤ Gam ^ 2 := by
    calc (1 + H1) * cN
        ≤ Gam * Gam := mul_le_mul h1H1 hcN hcN0 hG0
      _ = Gam ^ 2 := (sq Gam).symm
  have hprod1 : (1 + H1) * cN * (Real.sqrt σ)⁻¹ * ng2 ≤ Gam ^ 3 * N_W := by
    have h1 : (1 + H1) * cN * (Real.sqrt σ)⁻¹ ≤ Gam ^ 3 := by
      calc (1 + H1) * cN * (Real.sqrt σ)⁻¹
          ≤ Gam ^ 2 * Gam := mul_le_mul hcut_G2 hσ_sqrt (by positivity) (sq_nonneg Gam)
        _ = Gam ^ 3 := by ring
    exact mul_le_mul h1 hng2 hng20 (pow_nonneg hG0 3)
  have h1_real : ((1 + H1) * cN) ^ 2 * (2 * (|h| * (Real.sqrt σ)⁻¹) ^ 2 * ng2 ^ 2) ≤
      2 * (Gam ^ 3 * N_W) ^ 2 * |h| := by
    have h0_l : 0 ≤ (1 + H1) * cN * (Real.sqrt σ)⁻¹ * ng2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hcN0) (by positivity)) hng20
    have hsq := pow_le_pow_left₀ h0_l hprod1 2
    calc ((1 + H1) * cN) ^ 2 * (2 * (|h| * (Real.sqrt σ)⁻¹) ^ 2 * ng2 ^ 2)
        = 2 * ((1 + H1) * cN * (Real.sqrt σ)⁻¹ * ng2) ^ 2 * |h| ^ 2 := by ring
      _ ≤ 2 * (Gam ^ 3 * N_W) ^ 2 * |h| := by
          refine mul_le_mul ?_ hh_sq (sq_nonneg |h|) (mul_nonneg zero_le_two (sq_nonneg _))
          exact mul_le_mul_of_nonneg_left hsq zero_le_two
  have h2_real : ((1 + H1) * (cN * |h|) * nW) ^ 2 ≤ (Gam ^ 3 * N_W) ^ 2 * |h| := by
    have hG2_G3 : Gam ^ 2 ≤ Gam ^ 3 := pow_le_pow_right₀ hG1 (by norm_num)
    have hprod2 : (1 + H1) * cN * nW ≤ Gam ^ 3 * N_W := by
      calc (1 + H1) * cN * nW
          ≤ Gam ^ 2 * N_W := mul_le_mul hcut_G2 hnW hnW0 (sq_nonneg Gam)
        _ ≤ Gam ^ 3 * N_W := mul_le_mul_of_nonneg_right hG2_G3 hNW0
    have h0_l : 0 ≤ (1 + H1) * cN * nW :=
      mul_nonneg (mul_nonneg (by linarith) hcN0) hnW0
    have hsq := pow_le_pow_left₀ h0_l hprod2 2
    calc ((1 + H1) * (cN * |h|) * nW) ^ 2
        = ((1 + H1) * cN * nW) ^ 2 * |h| ^ 2 := by ring
      _ ≤ (Gam ^ 3 * N_W) ^ 2 * |h| := mul_le_mul hsq hh_sq (sq_nonneg |h|) (sq_nonneg _)
  have h2_ofReal : ∀ x : ℝ, 0 ≤ x → (2 : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) :=
    fun x _ => by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  calc 2 * ENNReal.ofReal (((1 + H1) * cN) ^ 2 * (2 * (|h| * (Real.sqrt σ)⁻¹) ^ 2 * ng2 ^ 2)) +
        2 * ENNReal.ofReal (((1 + H1) * (cN * |h|) * nW) ^ 2)
      ≤ 2 * ENNReal.ofReal (2 * (Gam ^ 3 * N_W) ^ 2 * |h|) +
          2 * ENNReal.ofReal ((Gam ^ 3 * N_W) ^ 2 * |h|) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal h1_real) zero_le)
          (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal h2_real) zero_le)
    _ = ENNReal.ofReal
          (2 * (2 * (Gam ^ 3 * N_W) ^ 2 * |h|) + 2 * ((Gam ^ 3 * N_W) ^ 2 * |h|)) := by
        rw [h2_ofReal _ (by positivity), h2_ofReal _ (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((6 * Gam ^ 3 * N_W) ^ 2 * |h|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hnn : 0 ≤ (Gam ^ 3 * N_W) ^ 2 * |h| := mul_nonneg (sq_nonneg _) (abs_nonneg h)
        nlinarith

/-- Proof of the transverse (`shiftEta`) chart-pullback and cutoff-localisation leaf
`PhaseDissipationCutoffShiftEta` (`PartII-a:N05/3/1/2`). -/
theorem phaseDissipationCutoffShiftEta : PhaseDissipationCutoffShiftEta := by
  refine ⟨3, 6, by norm_num, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM hχ _hχ1 hm _B _hB ε hε _hε1 P _ hP _hP1
    U hU W w_hd g_diss _hw hg h hh
  have hG1 := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
  have hW_norm : ‖W‖ = ‖U (B0223.liftVec hε hc hP W)‖ :=
    (norm_phaseLift_liftVec hε hc hP U W).symm
  have hg2_le_sum : ‖g_diss 2‖ ≤ ∑ j : Fin 3, ‖g_diss j‖ := by
    rw [Fin.sum_univ_three]
    linarith [norm_nonneg (g_diss 0), norm_nonneg (g_diss 1)]
  have hsum_nn : 0 ≤ ∑ j : Fin 3, ‖g_diss j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hW_le_NW : ‖W‖ ≤ ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ := by
    rw [hW_norm]
    exact (le_add_of_nonneg_right (norm_nonneg w_hd)).trans (le_add_of_nonneg_right hsum_nn)
  have hg2_le_NW : ‖g_diss 2‖ ≤
      ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ :=
    hg2_le_sum.trans
      (le_add_of_nonneg_left
        (add_nonneg (norm_nonneg (U (B0223.liftVec hε hc hP W))) (norm_nonneg w_hd)))
  have hNW0 : 0 ≤ ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ :=
    (norm_nonneg W).trans hW_le_NW
  have hh1 : |h| ≤ 1 := abs_le.2 ⟨hh.1, hh.2⟩
  have hf_meas : Measurable
      (fun p => flatStressCutRep c χ W (shiftEta h p) - flatStressCutRep c χ W p) :=
    ((measurable_flatStressCutRep c hm W).comp (measurable_shiftEta h)).sub
      (measurable_flatStressCutRep c hm W)
  have hR0 : 0 ≤
      (6 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 *
        (‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 * |h| :=
    mul_nonneg (sq_nonneg _) (abs_nonneg h)
  refine integral_norm_sq_le_of_lintegral_le hf_meas hR0 ?_
  have hsplit := lintegral_flatStressCutRep_shift_sub_sq_le_split hm (measurable_shiftEta h) W
  let ψ : Profile → ℝ := fun q => χ (shiftEta h q) - χ q
  have hψ_m : Measurable ψ := (hm.comp (measurable_shiftEta h)).sub hm
  have hψ_bd : ∀ q, |ψ q| ≤ cNorm8 χ * |h| := fun q => by
    calc |χ (shiftEta h q) - χ q|
        ≤ cNorm8 χ * ‖shiftEta h q - q‖ := abs_cutoff_sub_le hc hχ q (shiftEta h q)
      _ = cNorm8 χ * |h| := by rw [norm_shiftEta_sub]
  have hψ_supp : ∀ q, ψ q ≠ 0 → σ ≤ q.1 ∧ q.1 ≤ H1 := fun q hq => by
    by_cases h1 : χ (shiftEta h q) = 0
    · have h2 : χ q ≠ 0 := fun h0 => hq (by simp [ψ, h1, h0])
      exact ⟨(hχ.support q h2).1, (hχ.support q h2).2.1⟩
    · exact ⟨(hχ.support (shiftEta h q) h1).1, (hχ.support (shiftEta h q) h1).2.1⟩
  have hI₂ := lintegral_bounded_smul_periodize_sq_le hc hσ hσH hψ_m hψ_bd hψ_supp W
  have hb_meas : Measurable (periodize c (W : Profile → MeridC)) :=
    measurable_periodize_any c (Lp.stronglyMeasurable W).measurable
  have hg_meas : Measurable fun p : Profile =>
      periodize c (W : Profile → MeridC) (shiftEta h p) -
        periodize c (W : Profile → MeridC) p :=
    (hb_meas.comp (measurable_shiftEta h)).sub hb_meas
  have hφ_bd : ∀ p, |χ (shiftEta h p)| ≤ cNorm8 χ :=
    fun p => abs_le_cNorm8_of_nearCutoff hc hχ (shiftEta h p)
  have hφ_supp : ∀ p, χ (shiftEta h p) ≠ 0 → p ∈ profileBox σ H1 (L1 + 1) := fun p hp => by
    obtain ⟨hs1, hs2, hη⟩ := hχ.support (shiftEta h p) hp
    change |p.2.2 + h| ≤ L1 at hη
    have hη' : |p.2.2| ≤ L1 + 1 := by
      have htri : |p.2.2| ≤ |p.2.2 + h| + |h| := by
        have := abs_sub (p.2.2 + h) h
        simpa using this
      linarith
    exact ⟨hs1, hs2, hη'⟩
  have hI₁_loc := lintegral_cutoff_smul_sq_le_profileBox (c := c) hσ hσH hφ_bd hφ_supp hg_meas
  rw [lintegral_profileBox_shiftEta_sub_sq_eq hε hc hP U hU W σ H1 (L1 + 1) h] at hI₁_loc
  have hshear := lintegral_phaseVol_shearZ_sub_sq_le hg
    (measurableSet_spaceBox ε σ H1 (L1 + 1))
    (k := h * ε) (Δ := |h| * (Real.sqrt σ)⁻¹) (by positivity)
    (fun y hy => abs_mul_radius_le_of_mem_spaceBox hε hσ h hy)
  have hI₁ := hI₁_loc.trans (mul_le_mul_of_nonneg_left hshear zero_le)
  refine (hsplit.trans
    (add_le_add (mul_le_mul_of_nonneg_left hI₁ zero_le)
      (mul_le_mul_of_nonneg_left hI₂ zero_le))).trans ?_
  exact cutoffShiftEta_ennreal_consolidation
    hG1 hσ hσH
    (one_add_H1_le_gamma χ χ1 hν hc hσ hL1 hγ hM)
    (inv_sqrt_sigma_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM)
    (cNorm8_nonneg χ)
    (cNorm8_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM)
    (norm_nonneg W) hW_le_NW
    (norm_nonneg (g_diss 2)) hg2_le_NW
    hNW0 hh

end UnforcedLeray.Short.PartIIa.N05FlowAux
