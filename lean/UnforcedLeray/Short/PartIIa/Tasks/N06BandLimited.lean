import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity
import UnforcedLeray.Short.PartIIa.Tasks.N06BandLimited.BernsteinTest

/-!


Source of record: `the November 2 reference manuscript`, lines 1766-1804 and
1817-1832 (`near:local-smoothing` + band-limited dual vectors).

Assembles `nearBandLimited : NearBandLimited` by combining:
1. `nearLocalRegularity : NearLocalRegularity` (`PartII-a:N05`);
2. 3D periodic box Fourier truncation (`BoxFourier`, `HighFreqBounds`) giving `O(N⁻¹)` high-frequency
   error on `HasWeakCellH1` outputs and `O(δ^{-3/2} N^{-1/4})` error on `HasCellH14` outputs;
3. `HSpace` vs `B.boxMeas` norm equivalence and spectral Bernstein + Leibniz `H⁶` test bounds on
   `B.bandSubspace N` (`BernsteinTest`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223

namespace N06Aux.BoxParams

private theorem gamma_ge_two_inv (B : BoxParams) {ν M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hγ : 0 < γs) (hM0 : 0 ≤ M) :
    2 + B.c⁻¹ + B.σ⁻¹ ≤ Gamma ν B.c B.σ B.H1 B.L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  have : 0 < B.H1 := lt_of_lt_of_le B.hσ B.hσH1
  linarith [B.hc, B.hL1, hM0, cNorm8_nonneg χ, cNorm8_nonneg χ1]

private theorem deltaStep_rpow_le (B : BoxParams) {ν M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hγ : 0 < γs) (hM0 : 0 ≤ M) :
    B.deltaStep ^ (-(3 / 2 : ℝ)) ≤ 16 * Gamma ν B.c B.σ B.H1 B.L1 M γs χ χ1 ^ 2 := by
  set G := Gamma ν B.c B.σ B.H1 B.L1 M γs χ χ1
  have hG_ge : 2 + B.c⁻¹ + B.σ⁻¹ ≤ G := B.gamma_ge_two_inv χ χ1 hν hγ hM0
  have hc_inv : 0 < B.c⁻¹ := inv_pos.2 B.hc
  have hσ_inv : 0 < B.σ⁻¹ := inv_pos.2 B.hσ
  have hδ_pos : 0 < B.deltaStep := B.deltaStep_pos
  have hδ_inv_pos : 0 < B.deltaStep⁻¹ := inv_pos.2 hδ_pos
  have h1_le_inv : 1 ≤ B.deltaStep⁻¹ := by
    have hmul : B.deltaStep * B.deltaStep⁻¹ = 1 := mul_inv_cancel₀ hδ_pos.ne'
    have hhalf : B.deltaStep ≤ 1 / 2 := B.deltaStep_le_half
    nlinarith
  have hinv_le : B.deltaStep⁻¹ ≤ 4 * G := by
    unfold deltaStep
    rcases min_choice (min (1 / 2 : ℝ) (B.σ / 4)) (B.c / 2) with h1 | h2
    · rw [h1]
      rcases min_choice (1 / 2 : ℝ) (B.σ / 4) with h1a | h1b
      · rw [h1a]
        norm_num
        linarith
      · rw [h1b]
        have heq : (B.σ / 4)⁻¹ = 4 * B.σ⁻¹ := by ring
        rw [heq]
        linarith
    · rw [h2]
      have heq : (B.c / 2)⁻¹ = 2 * B.c⁻¹ := by ring
      rw [heq]
      linarith
  calc B.deltaStep ^ (-(3 / 2 : ℝ))
      = (B.deltaStep⁻¹) ^ (3 / 2 : ℝ) := by
        rw [Real.inv_rpow hδ_pos.le, Real.rpow_neg hδ_pos.le]
    _ ≤ (B.deltaStep⁻¹) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1_le_inv (by norm_num)
    _ = (B.deltaStep⁻¹) ^ 2 := Real.rpow_two _
    _ ≤ (4 * G) ^ 2 := pow_le_pow_left₀ hδ_inv_pos.le hinv_le 2
    _ = 16 * G ^ 2 := by ring

private theorem approx_of_weakCellH1 (B : BoxParams) {N G D : ℝ} (hN : 1 ≤ N)
    (h1_2sig : 1 + 2 * B.σ⁻¹ ≤ 2 * G) (hD : 0 ≤ D)
    {U : HSpace B.c MeridC} {u ds dq deta : Profile → MeridC}
    (hw : HasWeakCellH1 B.c B.σ B.H1 B.L1 U u ds dq deta)
    (hnorm : cellH1Norm B.c u ds dq deta ≤ D) :
    ∃ v ∈ B.bandSubspace N, ‖U - v‖ ≤ 2 * G * N⁻¹ * D := by
  refine ⟨B.evalTrig N (B.coeffMerid u), ⟨B.coeffMerid u, rfl⟩, ?_⟩
  have hN_pos : 0 < N := by linarith
  have hcmp := B.norm_sub_evalTrig_le N hw.ae_eq hw.memLp_u hw.support_u (B.coeffMerid u)
  rw [B.trigMerid_coeffMerid_eq_projMerid] at hcmp
  have hhf := B.h1_highFreq_bound hw hN
  have hprod : N⁻¹ * cellH1Norm B.c u ds dq deta ≤ N⁻¹ * D :=
    mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hsq : N⁻¹ ^ 2 * cellH1Norm B.c u ds dq deta ^ 2 ≤ (N⁻¹ * D) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (by positivity) (cellH1Norm_nonneg B.c u ds dq deta)) hprod 2
  have hsqrt : (∫ p, ‖u p - B.projMerid N u p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ) ≤ N⁻¹ * D := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_sqrt (hhf.trans hsq)).trans_eq (Real.sqrt_sq (by positivity))
  have h1_nn : 0 ≤ 1 + 2 * B.σ⁻¹ := by
    have := B.hσ
    positivity
  have h2G_nn : 0 ≤ 2 * G := h1_nn.trans h1_2sig
  calc ‖U - B.evalTrig N (B.coeffMerid u)‖
      ≤ (1 + 2 * B.σ⁻¹) * (∫ p, ‖u p - B.projMerid N u p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ) := hcmp
    _ ≤ (2 * G) * (N⁻¹ * D) :=
        mul_le_mul h1_2sig hsqrt
          (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _) h2G_nn
    _ = 2 * G * N⁻¹ * D := by ring

private theorem approx_of_cellH14 (B : BoxParams) {N G D : ℝ} (hN : 1 ≤ N)
    (hG_nn : 0 ≤ G) (h1_2sig : 1 + 2 * B.σ⁻¹ ≤ 2 * G)
    (hδ_le : B.deltaStep ^ (-(3 / 2 : ℝ)) ≤ 16 * G ^ 2) (hD : 0 ≤ D)
    {U : HSpace B.c MeridC} {u : Profile → MeridC}
    (hw : HasCellH14 B.c B.σ B.H1 B.L1 U u)
    (hnorm : cellH14Norm B.c u ≤ D) :
    ∃ v ∈ B.bandSubspace N, ‖U - v‖ ≤ 28 * G ^ 2 * N ^ (-(1 / 4 : ℝ)) * D := by
  refine ⟨B.evalTrig N (B.coeffMerid u), ⟨B.coeffMerid u, rfl⟩, ?_⟩
  have hN_pos : 0 < N := by linarith
  have hcmp := B.norm_sub_evalTrig_le N hw.ae_eq hw.memLp_u hw.support_u (B.coeffMerid u)
  rw [B.trigMerid_coeffMerid_eq_projMerid] at hcmp
  have hhf := B.h14_highFreq_bound hw hN
  have hN_sq : N ^ (-(1 / 2 : ℝ)) = (N ^ (-(1 / 4 : ℝ))) ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hN_pos.le]
    norm_num
  have h12_le : 12 * B.deltaStep ^ (-(3 / 2 : ℝ)) ≤ (14 * G) ^ 2 := by
    nlinarith [sq_nonneg G]
  have hu_sq : cellH14Norm B.c u ^ 2 ≤ D ^ 2 :=
    pow_le_pow_left₀ (cellH14Norm_nonneg B.c u) hnorm 2
  have hsq : ∫ p, ‖u p - B.projMerid N u p‖ ^ 2 ∂B.boxMeas ≤
      (14 * G * N ^ (-(1 / 4 : ℝ)) * D) ^ 2 := by
    calc ∫ p, ‖u p - B.projMerid N u p‖ ^ 2 ∂B.boxMeas
        ≤ 12 * B.deltaStep ^ (-(3 / 2 : ℝ)) * N ^ (-(1 / 2 : ℝ)) * cellH14Norm B.c u ^ 2 := hhf
      _ ≤ (14 * G) ^ 2 * (N ^ (-(1 / 4 : ℝ))) ^ 2 * D ^ 2 := by
          rw [hN_sq]
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right h12_le (sq_nonneg _))
            hu_sq
            (sq_nonneg _)
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (14 * G * N ^ (-(1 / 4 : ℝ)) * D) ^ 2 := by ring
  have hrhs_nn : 0 ≤ 14 * G * N ^ (-(1 / 4 : ℝ)) * D :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hN_pos.le _)) hD
  have hsqrt : (∫ p, ‖u p - B.projMerid N u p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ) ≤
      14 * G * N ^ (-(1 / 4 : ℝ)) * D := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_sqrt hsq).trans_eq (Real.sqrt_sq hrhs_nn)
  calc ‖U - B.evalTrig N (B.coeffMerid u)‖
      ≤ (1 + 2 * B.σ⁻¹) * (∫ p, ‖u p - B.projMerid N u p‖ ^ 2 ∂B.boxMeas) ^ (1 / 2 : ℝ) := hcmp
    _ ≤ (2 * G) * (14 * G * N ^ (-(1 / 4 : ℝ)) * D) :=
        mul_le_mul h1_2sig hsqrt
          (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _) (by positivity)
    _ = 28 * G ^ 2 * N ^ (-(1 / 4 : ℝ)) * D := by ring

end N06Aux.BoxParams

theorem nearBandLimited : NearBandLimited := by
  obtain ⟨k_loc, C_loc, hC_loc, hloc⟩ := nearLocalRegularity
  let K : ℕ := k_loc + 2
  let C : ℝ := max (28 * C_loc) N06Aux.BoxParams.C_bern
  have hC_nn : 0 ≤ C := le_trans (by positivity) (le_max_left _ _)
  refine ⟨K, C, hC_nn, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm Mχ hMχ ε hε hε1 P _ hP hP1 μ hμM hμγ N hN
  let B : N06Aux.BoxParams := ⟨c, σ, H1, L1, hc, hσ, hσH, hL1⟩
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG_ge : 2 + c⁻¹ + σ⁻¹ ≤ G := B.gamma_ge_two_inv χ χ1 hν hγ hM0
  have hc_inv : 0 < c⁻¹ := inv_pos.2 hc
  have hσ_inv : 0 < σ⁻¹ := inv_pos.2 hσ
  have hG1 : 1 ≤ G := by linarith
  have hG_nn : 0 ≤ G := by linarith
  have h1_2sig : 1 + 2 * σ⁻¹ ≤ 2 * G := by linarith
  have hδ_le : B.deltaStep ^ (-(3 / 2 : ℝ)) ≤ 16 * G ^ 2 :=
    B.deltaStep_rpow_le χ χ1 hν hγ hM0
  have hGK1 : G ^ (k_loc + 1) ≤ G ^ K := pow_le_pow_right₀ hG1 (by omega)
  have hGK2 : G ^ 2 ≤ G ^ K := pow_le_pow_right₀ hG1 (by omega)
  have h28_le : 28 * C_loc ≤ C := le_max_left _ _
  have h2_le : 2 * C_loc ≤ C := by linarith
  have hbern_le : N06Aux.BoxParams.C_bern ≤ C := le_max_right _ _
  have hN_pos : 0 < N := by linarith
  obtain ⟨hBody, hStress⟩ :=
    hloc ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm Mχ hMχ ε hε hε1 P hP hP1 μ hμM hμγ
  refine ⟨B.bandSubspace N, ?_, ?_, ?_⟩
  · intro b
    obtain ⟨⟨u₁, ds₁, dq₁, de₁, hw₁, hn₁⟩, ⟨u₀, ds₀, dq₀, de₀, hw₀, hn₀⟩⟩ := hBody b
    have hDb_nn : 0 ≤ C_loc * G ^ k_loc * ‖b‖ :=
      mul_nonneg (mul_nonneg hC_loc (pow_nonneg hG_nn _)) (norm_nonneg b)
    have h_step : 2 * G * N⁻¹ * (C_loc * G ^ k_loc * ‖b‖) ≤ C * G ^ K * N⁻¹ * ‖b‖ := by
      calc 2 * G * N⁻¹ * (C_loc * G ^ k_loc * ‖b‖)
          = (2 * C_loc) * G ^ (k_loc + 1) * N⁻¹ * ‖b‖ := by ring
        _ ≤ C * G ^ K * N⁻¹ * ‖b‖ := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul h2_le hGK1 (pow_nonneg hG_nn _) hC_nn)
                (by positivity))
              (norm_nonneg b)
    constructor
    · obtain ⟨v, hv, hvb⟩ := B.approx_of_weakCellH1 hN h1_2sig hDb_nn hw₁ hn₁
      exact ⟨v, hv, hvb.trans h_step⟩
    · obtain ⟨v, hv, hvb⟩ := B.approx_of_weakCellH1 hN h1_2sig hDb_nn hw₀ hn₀
      exact ⟨v, hv, hvb.trans h_step⟩
  · intro Seps S0 hSeps hS0 F
    obtain ⟨⟨u₁, hw₁, hn₁⟩, ⟨u₀, hw₀, hn₀⟩⟩ := hStress Seps S0 hSeps hS0 F
    have hDF_nn : 0 ≤ C_loc * G ^ k_loc * ‖F‖ :=
      mul_nonneg (mul_nonneg hC_loc (pow_nonneg hG_nn _)) (norm_nonneg F)
    have h_step : 28 * G ^ 2 * N ^ (-(1 / 4 : ℝ)) * (C_loc * G ^ k_loc * ‖F‖) ≤
        C * G ^ K * N ^ (-(1 / 4 : ℝ)) * ‖F‖ := by
      have hK_eq : (28 * C_loc) * G ^ K * N ^ (-(1 / 4 : ℝ)) * ‖F‖ =
          28 * G ^ 2 * N ^ (-(1 / 4 : ℝ)) * (C_loc * G ^ k_loc * ‖F‖) := by
        dsimp [K]; ring
      rw [← hK_eq]
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h28_le (pow_nonneg hG_nn _))
          (Real.rpow_nonneg hN_pos.le _))
        (norm_nonneg F)
    constructor
    · obtain ⟨v, hv, hvb⟩ := B.approx_of_cellH14 hN hG_nn h1_2sig hδ_le hDF_nn hw₁ hn₁
      exact ⟨v, hv, hvb.trans h_step⟩
    · obtain ⟨v, hv, hvb⟩ := B.approx_of_cellH14 hN hG_nn h1_2sig hδ_le hDF_nn hw₀ hn₀
      exact ⟨v, hv, hvb.trans h_step⟩
  · intro z hz
    obtain ⟨ζ, hζ_test, hζ_supp, hζ_ae, hζ_h6⟩ :=
      B.bandSubspace_bernstein_h6 hν hL1 hγ hM0 hχ hm hMχ hN hz
    refine ⟨ζ, hζ_test, hζ_supp, hζ_ae, hζ_h6.trans ?_⟩
    refine mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul hbern_le hGK2 (pow_nonneg hG_nn _) hC_nn)
        (by positivity))
      (norm_nonneg z)

end UnforcedLeray.Short.PartIIa
