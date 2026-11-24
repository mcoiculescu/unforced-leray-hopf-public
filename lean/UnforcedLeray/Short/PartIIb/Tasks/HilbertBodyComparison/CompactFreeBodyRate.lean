import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16
import UnforcedLeray.Short.PartIIa.ComposeNear
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint
import UnforcedLeray.Short.PartIIa.Tasks.N06BandLimited
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.WindowCutoff
import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.CompactFreeBodyRate.NormBridge
import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.CompactFreeBodyRate.PhysId
import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.CompactFreeBodyRate.FlatId

/-!
# Part II-b, leaf `PartII-b:T16/1` (`CompactFreeBodyRateH2`)

Source of record: `the November 2 reference manuscript`, lines 1691-1700 and
1955-1990 (the Hilbert compact free body comparison rate `O(Γ^k ε^{1/14})` on the enlarged
observation box `obsBox (σ/2) (2*H₁) (L₁ + 1)`).

Combines:
1. `nearCompactFreeComparison_of_parts nearBandLimited nearSmoothAdjointComparison` (`PartII-a`),
2. `windowCutoffExists` (`PartIII-b`, smooth periodic cutoff equal to `1` on the enlarged box),
3. `NormBridge`: `HSpace` vs `hNorm c 2` bridge (`√c⁻¹` scaling and `mulChi` indicator bound),
4. `PhysId` (`teps_ae_eq_phys_response`) and `FlatId` (`t0flat_ae_eq_flat_response`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open CompactFreeRateSub

theorem compactFreeBodyRateH2_proof : UnforcedLeray.Short.IIb.CompactFreeBodyRateH2 := by
  obtain ⟨kCF, CCF, hCCF, hCF⟩ :=
    UnforcedLeray.Short.PartIIa.nearCompactFreeComparison_of_parts
      UnforcedLeray.Short.PartIIa.nearBandLimited
      UnforcedLeray.Short.PartIIa.nearSmoothAdjointComparison
  obtain ⟨Ccut, kcut, hcut⟩ := UnforcedLeray.Short.PartIIIb.NearInst.Body.windowCutoffExists
  let Ccut' : ℝ := max Ccut 0
  have hCcut' : 0 ≤ Ccut' := le_max_right _ _
  let m : ℕ := max kcut 1
  let CG : ℝ := 21 + Ccut' * 8 ^ kcut
  have hCG_pos : 0 < CG := by positivity
  let k₁ : ℕ := m * kCF
  let C₁ : ℝ := (CCF + 1) * CG ^ kCF
  refine ⟨k₁, C₁, by positivity, ?_⟩
  intro Γ ν c σ H₁ L₁ μ hΓ1 hνΓ hνiΓ hcΓ hciΓ hσiΓ hHΓ hLΓ hμΓ hγΓ hν hc hσ hσH hL₁
    ε hε hε1 hP1 F bε b0 hF hbε hresp hb0_resp hb0_class
  have hΓ_pos : 0 < Γ := lt_of_lt_of_le zero_lt_one hΓ1
  have hΓi_pos : 0 < Γ⁻¹ := inv_pos.2 hΓ_pos
  have hγ : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hΓi_pos hγΓ
  have hσ2_pos : 0 < σ / 2 := by positivity
  have hσ2_le : σ / 2 ≤ 2 * H₁ := by linarith
  have hL1_nn : 0 ≤ L₁ + 1 := by linarith
  obtain ⟨χ, χ1, hNear, hLarge, hm, hB, h1, hNormCut⟩ :=
    hcut c (σ / 2) (2 * H₁) (L₁ + 1) hc hσ2_pos hσ2_le hL1_nn
  set σ_c : ℝ := (σ / 2) / 2
  set H_c : ℝ := 2 * (2 * H₁)
  set L_c : ℝ := 2 * (L₁ + 1) + 1
  have hσc_pos : 0 < σ_c := by positivity
  have hσc_le : σ_c ≤ H_c := by
    change (σ / 2) / 2 ≤ 2 * (2 * H₁)
    linarith
  have hLc_nn : 0 ≤ L_c := by
    change 0 ≤ 2 * (L₁ + 1) + 1
    linarith
  have hσc_inv : σ_c⁻¹ = 4 * σ⁻¹ := by
    change ((σ / 2) / 2)⁻¹ = 4 * σ⁻¹
    have h4 : (σ / 2) / 2 = σ * (4 : ℝ)⁻¹ := by ring
    rw [h4, mul_inv, inv_inv]
    ring
  have hσ2_inv : (σ / 2)⁻¹ = 2 * σ⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  have hGB_le :
      UnforcedLeray.Short.PartIIa.GammaBox ν c σ_c H_c L_c Γ Γ⁻¹ ≤ 21 * Γ := by
    unfold UnforcedLeray.Short.PartIIa.GammaBox
    rw [hσc_inv, inv_inv]
    change 2 + ν + ν⁻¹ + c + c⁻¹ + 4 * σ⁻¹ + 2 * (2 * H₁) + (2 * (L₁ + 1) + 1) + Γ + Γ ≤ 21 * Γ
    linarith
  have hCutBase_nn : 0 ≤ (σ / 2)⁻¹ + 2 * H₁ + (L₁ + 1) + 2 := by
    have : 0 < (σ / 2)⁻¹ := inv_pos.2 hσ2_pos
    linarith
  have hCutBase_le : (σ / 2)⁻¹ + 2 * H₁ + (L₁ + 1) + 2 ≤ 8 * Γ := by
    rw [hσ2_inv]
    linarith
  have hCut_le :
      UnforcedLeray.Short.PartIIa.cNorm8 χ + UnforcedLeray.Short.PartIIa.cNorm8 χ1 ≤
        (Ccut' * 8 ^ kcut) * Γ ^ kcut := by
    calc UnforcedLeray.Short.PartIIa.cNorm8 χ + UnforcedLeray.Short.PartIIa.cNorm8 χ1
        ≤ Ccut * ((σ / 2)⁻¹ + 2 * H₁ + (L₁ + 1) + 2) ^ kcut := hNormCut
      _ ≤ Ccut' * ((σ / 2)⁻¹ + 2 * H₁ + (L₁ + 1) + 2) ^ kcut :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hCutBase_nn _)
      _ ≤ Ccut' * (8 * Γ) ^ kcut :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hCutBase_nn hCutBase_le _) hCcut'
      _ = (Ccut' * 8 ^ kcut) * Γ ^ kcut := by rw [mul_pow]; ring
  have hG_nn : 0 ≤ UnforcedLeray.Short.PartIIa.Gamma ν c σ_c H_c L_c Γ Γ⁻¹ χ χ1 := by
    unfold UnforcedLeray.Short.PartIIa.Gamma UnforcedLeray.Short.PartIIa.GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ_c⁻¹ := inv_pos.2 hσc_pos
    have : 0 < (Γ⁻¹)⁻¹ := inv_pos.2 hΓi_pos
    have hH_pos : 0 < H_c := lt_of_lt_of_le hσc_pos hσc_le
    linarith [UnforcedLeray.Short.PartIIa.cNorm8_nonneg χ,
      UnforcedLeray.Short.PartIIa.cNorm8_nonneg χ1]
  have hΓ_le_m : Γ ≤ Γ ^ m := by
    simpa only [pow_one] using pow_le_pow_right₀ hΓ1 (Nat.le_max_right kcut 1)
  have hΓk_le_m : Γ ^ kcut ≤ Γ ^ m :=
    pow_le_pow_right₀ hΓ1 (Nat.le_max_left kcut 1)
  have hG_le : UnforcedLeray.Short.PartIIa.Gamma ν c σ_c H_c L_c Γ Γ⁻¹ χ χ1 ≤ CG * Γ ^ m := by
    unfold UnforcedLeray.Short.PartIIa.Gamma
    have h1' : UnforcedLeray.Short.PartIIa.GammaBox ν c σ_c H_c L_c Γ Γ⁻¹ ≤ 21 * Γ ^ m :=
      hGB_le.trans (by linarith)
    have h2' : UnforcedLeray.Short.PartIIa.cNorm8 χ + UnforcedLeray.Short.PartIIa.cNorm8 χ1 ≤
        (Ccut' * 8 ^ kcut) * Γ ^ m :=
      hCut_le.trans (mul_le_mul_of_nonneg_left hΓk_le_m (by positivity))
    change UnforcedLeray.Short.PartIIa.GammaBox ν c σ_c H_c L_c Γ Γ⁻¹ +
        UnforcedLeray.Short.PartIIa.cNorm8 χ + UnforcedLeray.Short.PartIIa.cNorm8 χ1 ≤
      (21 + Ccut' * 8 ^ kcut) * Γ ^ m
    linarith
  have hGpow_le :
      UnforcedLeray.Short.PartIIa.Gamma ν c σ_c H_c L_c Γ Γ⁻¹ χ χ1 ^ kCF ≤
        CG ^ kCF * Γ ^ k₁ := by
    calc UnforcedLeray.Short.PartIIa.Gamma ν c σ_c H_c L_c Γ Γ⁻¹ χ χ1 ^ kCF
        ≤ (CG * Γ ^ m) ^ kCF := pow_le_pow_left₀ hG_nn hG_le kCF
      _ = CG ^ kCF * (Γ ^ m) ^ kCF := mul_pow _ _ _
      _ = CG ^ kCF * Γ ^ k₁ := by rw [← pow_mul]
  have : Fact (0 < 2 * ε * c) := ⟨by positivity⟩
  obtain ⟨F', M, FH, hF'm, hF'per, -, hM0, -, hFF', hF'_ae, hFH_coe, hFH_norm⟩ :=
    exists_hs_rep hc F hF
  have hbε_ae :=
    teps_ae_eq_phys_response hν hc hε hP1 hγ hbε hresp hF'per hM0 hFF' hFH_coe
  have hb0_ae :=
    t0flat_ae_eq_flat_response hν hc hγ hF hb0_resp hb0_class hF'm hF'per hM0 hFF'
      hF'_ae hFH_coe hFH_norm
  set T_phys := UnforcedLeray.Short.PartIIa.Teps hν hε hc (P := 2 * ε * c) rfl μ
  set T_flat := UnforcedLeray.Short.PartIIa.T0flat hc ν μ
  set D : B0220.HSpace c B0223.MeridC := (T_phys - T_flat) FH
  have hD_sub : D = T_phys FH - T_flat FH := rfl
  have hD_per_sub :
      B0220.periodize c (D : B0220.Profile → B0223.MeridC) =ᵐ[hMeas c 2]
        B0220.periodize c
          ((T_phys FH : B0220.Profile → B0223.MeridC) -
            (T_flat FH : B0220.Profile → B0223.MeridC)) := by
    rw [hD_sub]
    exact ae_hMeas_periodize_congr hc (Lp.coeFn_sub (T_phys FH) (T_flat FH))
  have hD_ae : B0220.periodize c (D : B0220.Profile → B0223.MeridC) =ᵐ[hMeas c 2] bε - b0 := by
    filter_upwards [hD_per_sub, hbε_ae, hb0_ae] with p hp h1p h0p
    rw [hp]
    change B0220.periodize c (T_phys FH : B0220.Profile → B0223.MeridC) p -
        B0220.periodize c (T_flat FH : B0220.Profile → B0223.MeridC) p = bε p - b0 p
    rw [h1p, h0p]
  have hind_ae :
      indBox (σ / 2) (2 * H₁) (L₁ + 1) (bε - b0) =ᵐ[hMeas c 2]
        indBox (σ / 2) (2 * H₁) (L₁ + 1)
          (B0220.periodize c (D : B0220.Profile → B0223.MeridC)) := by
    filter_upwards [hD_ae] with p hp
    unfold indBox
    by_cases hmem : p ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
    · simp [hmem, hp]
    · simp [hmem]
  have hCF_body :=
    (hCF ν c σ_c H_c L_c Γ Γ⁻¹ χ χ1 hν hc hσc_pos hσc_le hLc_nn hΓi_pos hNear hLarge hm 1 hB
      ε hε hε1 (2 * ε * c) rfl hP1 μ hμΓ hγΓ).1 FH
  set rate : ℝ := C₁ * Γ ^ k₁ * ε ^ (1 / 14 : ℝ)
  have hmulChi_le :
      ‖UnforcedLeray.Short.PartIIa.mulChi (B0220.measureH c) χ hm hB D‖ ≤ rate * ‖FH‖ := by
    refine hCF_body.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg FH)
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hε.le _)
    calc CCF * UnforcedLeray.Short.PartIIa.Gamma ν c σ_c H_c L_c Γ Γ⁻¹ χ χ1 ^ kCF
        ≤ (CCF + 1) * (CG ^ kCF * Γ ^ k₁) := by
          refine mul_le_mul (by linarith) hGpow_le (pow_nonneg hG_nn _) (by positivity)
      _ = C₁ * Γ ^ k₁ := by ring
  have hrate_nn : 0 ≤ rate := by positivity
  calc hNorm c 2 (indBox (σ / 2) (2 * H₁) (L₁ + 1) (bε - b0))
      = hNorm c 2 (indBox (σ / 2) (2 * H₁) (L₁ + 1)
          (B0220.periodize c (D : B0220.Profile → B0223.MeridC))) :=
        eLpNorm_congr_ae hind_ae
    _ ≤ ENNReal.ofReal (Real.sqrt c⁻¹) *
          ENNReal.ofReal ‖UnforcedLeray.Short.PartIIa.mulChi (B0220.measureH c) χ hm hB D‖ :=
        hNorm_indBox_periodize_le_mulChi hc hm hB h1 D
    _ ≤ ENNReal.ofReal (Real.sqrt c⁻¹) * ENNReal.ofReal (rate * ‖FH‖) := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt c⁻¹) * (ENNReal.ofReal rate * ENNReal.ofReal ‖FH‖) := by
        rw [ENNReal.ofReal_mul hrate_nn]
    _ = ENNReal.ofReal rate * (ENNReal.ofReal (Real.sqrt c⁻¹) * ENNReal.ofReal ‖FH‖) := by
        rw [← mul_assoc, mul_comm (ENNReal.ofReal (Real.sqrt c⁻¹)), mul_assoc]
    _ = ENNReal.ofReal rate * hNorm c 2 F := by
        rw [hFH_norm]

end UnforcedLeray.Short.IIb
