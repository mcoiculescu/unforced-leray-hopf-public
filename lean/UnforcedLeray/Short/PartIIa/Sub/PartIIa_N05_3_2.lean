import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_3_1

/-!
# Decomposition of `PartII-a:N05/3/2`: azimuthal (`shiftQ`) `1/2`-Hölder `L²(cellMeasure c)` bound for `χ S_ε F`

Source of record: `the November 2 reference manuscript`,
lines 1765–1781 (`near:local-smoothing`).

## Structure of this file

1. **Unconditional commuting-flow `1/2`-Hölder combiner (`abs_le_sqrt_abs_of_mem_Icc`,
   `abs_eps_mul_le_sqrt_abs_of_mem_Icc`, `commuting_flow_shiftQ_sq_le`,
   `integral_shiftQ_sub_sq_le_of_commutingFlow`)**:
   Proves that for `0 < ε ≤ 1` and `h ∈ Icc (-1 : ℝ) 1`, any three-term commuting-flow translation
   estimate (source lines 1775–1780)
   `cellL2Norm c (fun p => u (shiftQ h p) - u p) ≤ |h| * A_Q + √|ε h| * A_S + |ε h| * A_E`
   implies the `1/2`-Hölder `L²(cellMeasure c)` difference-quotient bound
   `∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ (A_Q + A_S + A_E) ^ 2 * |h|`.
2. **Smooth-test commuting-flow bound and density extension**:
   Combines the unconditional smooth-test half-drift and dissipation package
   `seps_smooth_phaseLift_bounds`, the `shiftQ` measure invariance `lintegral_shiftQ_eq`, and the
   smooth-tensor density extension `integral_shift_sub_sq_le_of_testSub_eps` from
   `UnforcedLeray.Short.«PartII-a».Sub.«PartII-a_N05_3_1»`.
3. **Conditional assembly (`stressEpsCommutingFlowShiftQ_of`)**:
   Combines (1) and (2) with the log-age commuting-flow translation leaf
   `PhaseCommutingFlowCutoffShiftQ` (`PartII-a:N05/3/2/1`) to establish
   `StressEpsCommutingFlowShiftQ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open N05_1Aux N05_3Aux N05_4Aux N05_3_1Aux

namespace N05_3_2Aux

/-! ### 1. Unconditional commuting-flow `1/2`-Hölder combiner on `Icc (-1 : ℝ) 1` -/

/-- For `h ∈ Icc (-1 : ℝ) 1`, `|h| ≤ 1`. -/
theorem abs_le_one_of_mem_Icc {h : ℝ} (hh : h ∈ Icc (-1 : ℝ) 1) : |h| ≤ 1 :=
  abs_le.2 ⟨hh.1, hh.2⟩

/-- For `h ∈ Icc (-1 : ℝ) 1`, `|h| ≤ √|h|`. -/
theorem abs_le_sqrt_abs_of_mem_Icc {h : ℝ} (hh : h ∈ Icc (-1 : ℝ) 1) :
    |h| ≤ Real.sqrt |h| := by
  have h1 : |h| ≤ 1 := abs_le_one_of_mem_Icc hh
  have h0 : 0 ≤ |h| := abs_nonneg h
  have hsq : |h| ^ 2 ≤ (Real.sqrt |h|) ^ 2 := by
    rw [Real.sq_sqrt h0]
    nlinarith
  exact (abs_le_of_sq_le_sq' hsq (Real.sqrt_nonneg |h|)).2

/-- For `0 < ε ≤ 1` and `h ∈ Icc (-1 : ℝ) 1`, both `|ε * h|` and `√|ε * h|` are at most `√|h|`. -/
theorem abs_eps_mul_le_sqrt_abs_of_mem_Icc {ε h : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hh : h ∈ Icc (-1 : ℝ) 1) :
    |ε * h| ≤ Real.sqrt |h| ∧ Real.sqrt |ε * h| ≤ Real.sqrt |h| := by
  have h_abs : |ε * h| ≤ |h| := by
    rw [abs_mul, abs_of_pos hε0]
    calc ε * |h| ≤ 1 * |h| := mul_le_mul_of_nonneg_right hε1 (abs_nonneg h)
      _ = |h| := one_mul _
  exact ⟨h_abs.trans (abs_le_sqrt_abs_of_mem_Icc hh), Real.sqrt_le_sqrt h_abs⟩

/-- Squaring the three-term commuting-flow bound
`D_h ≤ |h| * A_Q + √|ε * h| * A_S + |ε * h| * A_E` on `Icc (-1 : ℝ) 1` for `0 < ε ≤ 1` yields
`D_h ^ 2 ≤ (A_Q + A_S + A_E) ^ 2 * |h|` (source lines 1775–1781). -/
theorem commuting_flow_shiftQ_sq_le {ε h D_h A_Q A_S A_E : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hh : h ∈ Icc (-1 : ℝ) 1)
    (hD0 : 0 ≤ D_h) (hAQ : 0 ≤ A_Q) (hAS : 0 ≤ A_S) (hAE : 0 ≤ A_E)
    (hflow : D_h ≤ |h| * A_Q + Real.sqrt |ε * h| * A_S + |ε * h| * A_E) :
    D_h ^ 2 ≤ (A_Q + A_S + A_E) ^ 2 * |h| := by
  have h1 := abs_le_sqrt_abs_of_mem_Icc hh
  obtain ⟨h2, h3⟩ := abs_eps_mul_le_sqrt_abs_of_mem_Icc hε0 hε1 hh
  have hle : D_h ≤ (A_Q + A_S + A_E) * Real.sqrt |h| := by
    calc D_h
        ≤ |h| * A_Q + Real.sqrt |ε * h| * A_S + |ε * h| * A_E := hflow
      _ ≤ Real.sqrt |h| * A_Q + Real.sqrt |h| * A_S + Real.sqrt |h| * A_E := by
          gcongr
      _ = (A_Q + A_S + A_E) * Real.sqrt |h| := by ring
  calc D_h ^ 2
      ≤ ((A_Q + A_S + A_E) * Real.sqrt |h|) ^ 2 := pow_le_pow_left₀ hD0 hle 2
    _ = (A_Q + A_S + A_E) ^ 2 * (Real.sqrt |h|) ^ 2 := by ring
    _ = (A_Q + A_S + A_E) ^ 2 * |h| := by rw [Real.sq_sqrt (abs_nonneg h)]

/-- Integral form of the commuting-flow `1/2`-Hölder combiner on `cellMeasure c`. -/
theorem integral_shiftQ_sub_sq_le_of_commutingFlow {c ε h A_Q A_S A_E : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hh : h ∈ Icc (-1 : ℝ) 1)
    (hAQ : 0 ≤ A_Q) (hAS : 0 ≤ A_S) (hAE : 0 ≤ A_E)
    (u : Profile → MeridC)
    (hflow : cellL2Norm c (fun p => u (shiftQ h p) - u p) ≤
      |h| * A_Q + Real.sqrt |ε * h| * A_S + |ε * h| * A_E) :
    ∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤
      (A_Q + A_S + A_E) ^ 2 * |h| := by
  have hnonneg : 0 ≤ ∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c) :=
    integral_nonneg fun _ => sq_nonneg _
  have hsq_eq : (cellL2Norm c (fun p => u (shiftQ h p) - u p)) ^ 2 =
      ∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c) := by
    unfold cellL2Norm
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]
  rw [← hsq_eq]
  exact commuting_flow_shiftQ_sq_le hε0 hε1 hh (cellL2Norm_nonneg c _) hAQ hAS hAE hflow

end N05_3_2Aux

open N05_3_2Aux

/-! ### 2. Leaf obligation and conditional assembly of `StressEpsCommutingFlowShiftQ` -/

/-- **Log-age commuting-flow translation leaf for `PartII-a:N05/3/2`
(`PhaseCommutingFlowCutoffShiftQ`, `PartII-a:N05/3/2/1`)**
(source `the November 2 reference manuscript`,
lines 1765–1781): in log age `x = log s`, the conjugate of `Q_ε` shifted by `ε` is the skew
operator `Q̃_ε = ∂_q - 2ε ∂_x - ε (η ∂_η + 1/2)` whose three constituent flows commute; for any
`W : HSpace c MeridC` whose phase lift `U (B0223.liftVec hε hc hP W)` has half-drift `w_hd`
(`(FreeStress.phaseC0 P).HasPow (1 / 2)`) and spatial gradient `g_diss` (`HasGrad`), the `shiftQ h`
`L²(cellMeasure c)` difference of the localised cutoff `flatStressCutRep c χ W` satisfies the
three-term unitary flow estimate
`cellL2Norm c (fun p => flatStressCutRep c χ W (shiftQ h p) - flatStressCutRep c χ W p) ≤ (|h| + √|ε h| + |ε h|) * C * Gamma^k * (‖U (liftVec W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖)`. -/
def PhaseCommutingFlowCutoffShiftQ : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs → 0 ≤ M →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (_hm : Measurable χ) (B : ℝ) (_hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2), N01.IsPhaseLift ε P U →
      ∀ (W : HSpace c MeridC) (w_hd : Yq P 2) (g_diss : Fin 3 → Yq P 2),
        (FreeStress.phaseC0 P).HasPow (1 / 2) (U (B0223.liftVec hε hc hP W)) w_hd →
        HasGrad (U (B0223.liftVec hε hc hP W)) g_diss →
        ∀ h ∈ Icc (-1 : ℝ) 1,
          cellL2Norm c (fun p => flatStressCutRep c χ W (shiftQ h p) - flatStressCutRep c χ W p) ≤
            (|h| + Real.sqrt |ε * h| + |ε * h|) *
              (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k *
                (‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖))

/-- **Conditional assembly of `StressEpsCommutingFlowShiftQ` (`PartII-a:N05/3/2`)** from
`PhaseCommutingFlowCutoffShiftQ`, the commuting-flow `1/2`-Hölder combiner
`integral_shiftQ_sub_sq_le_of_commutingFlow`, `N01.phaseLiftExists`, the unconditional `Gamma^3`
smooth-test half-drift and dissipation package `seps_smooth_phaseLift_bounds`, and smooth-tensor
density (`integral_shift_sub_sq_le_of_testSub_eps`). -/
theorem stressEpsCommutingFlowShiftQ_of (hFlow : PhaseCommutingFlowCutoffShiftQ) :
    StressEpsCommutingFlowShiftQ := by
  obtain ⟨C_SD, hC_SD, hSD⟩ := seps_smooth_phaseLift_bounds
  obtain ⟨k_Q, C_Q, hC_Q, hLocQ⟩ := hFlow
  refine ⟨k_Q + 3, 6 * C_Q * C_SD, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB ε hε hε1 P _ hP hP1 μ hμM hμγ
    Seps hSeps F h hh
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  obtain ⟨U, hU⟩ := N01.phaseLiftExists ε P hε
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ Gam := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hK0 : 0 ≤ (3 * C_Q * C_SD * Gam ^ (k_Q + 3)) ^ 2 * |h| :=
    mul_nonneg (sq_nonneg _) (abs_nonneg h)
  have hext := integral_shift_sub_sq_le_of_testSub_eps hν hε hc hP hσ hσH hχ hm hSeps
    (measurable_shiftQ h) (fun f hf hper _ => (lintegral_shiftQ_eq hc h hf hper).le) hK0
    (fun M_test hM_test x G hx hG => by
      obtain ⟨w_hd, g_diss, hw_hd, hg_diss, hbd⟩ :=
        hSD ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P hP hP1 U hU μ hμM hμγ
          Seps hSeps M_test hM_test x G hx hG
      set W := Teps hν hε hc hP μ G
      set N_W : ℝ := ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖
      have hNW0 : 0 ≤ N_W := by
        dsimp only [N_W]
        have : 0 ≤ ∑ j : Fin 3, ‖g_diss j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
        linarith [norm_nonneg (U (B0223.liftVec hε hc hP W)), norm_nonneg w_hd]
      set A : ℝ := C_Q * Gam ^ k_Q * N_W
      have hA0 : 0 ≤ A := by dsimp only [A]; positivity
      have hflow_leaf := hLocQ ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM0 hχ hχ1 hm B hB
        ε hε hε1 P hP hP1 U hU W w_hd g_diss hw_hd hg_diss h hh
      have hflow_rw : cellL2Norm c (fun p => flatStressCutRep c χ W (shiftQ h p) -
          flatStressCutRep c χ W p) ≤
          |h| * A + Real.sqrt |ε * h| * A + |ε * h| * A := by
        calc cellL2Norm c (fun p => flatStressCutRep c χ W (shiftQ h p) -
              flatStressCutRep c χ W p)
            ≤ (|h| + Real.sqrt |ε * h| + |ε * h|) * A := hflow_leaf
          _ = |h| * A + Real.sqrt |ε * h| * A + |ε * h| * A := by ring
      have hint_W := integral_shiftQ_sub_sq_le_of_commutingFlow hε hε1 hh hA0 hA0 hA0
        (flatStressCutRep c χ W) hflow_rw
      have h3A : A + A + A ≤ 3 * C_Q * C_SD * Gam ^ (k_Q + 3) * ‖x‖ := by
        calc A + A + A
            = 3 * C_Q * Gam ^ k_Q * N_W := by dsimp only [A]; ring
          _ ≤ 3 * C_Q * Gam ^ k_Q * (C_SD * Gam ^ 3 * ‖x‖) :=
              mul_le_mul_of_nonneg_left hbd (by positivity)
          _ = 3 * C_Q * C_SD * Gam ^ (k_Q + 3) * ‖x‖ := by ring
      have hsq : (A + A + A) ^ 2 ≤ (3 * C_Q * C_SD * Gam ^ (k_Q + 3)) ^ 2 * ‖x‖ ^ 2 := by
        calc (A + A + A) ^ 2
            ≤ (3 * C_Q * C_SD * Gam ^ (k_Q + 3) * ‖x‖) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h3A 2
          _ = (3 * C_Q * C_SD * Gam ^ (k_Q + 3)) ^ 2 * ‖x‖ ^ 2 := by ring
      calc ∫ p, ‖flatStressCutRep c χ W (shiftQ h p) -
              flatStressCutRep c χ W p‖ ^ 2 ∂(cellMeasure c)
          ≤ (A + A + A) ^ 2 * |h| := hint_W
        _ ≤ ((3 * C_Q * C_SD * Gam ^ (k_Q + 3)) ^ 2 * ‖x‖ ^ 2) * |h| :=
            mul_le_mul_of_nonneg_right hsq (abs_nonneg h)
        _ = ((3 * C_Q * C_SD * Gam ^ (k_Q + 3)) ^ 2 * |h|) * ‖x‖ ^ 2 := by ring)
    F
  calc ∫ p, ‖flatStressCutRep c χ (Seps F) (shiftQ h p) -
          flatStressCutRep c χ (Seps F) p‖ ^ 2 ∂(cellMeasure c)
      ≤ 2 * (((3 * C_Q * C_SD * Gam ^ (k_Q + 3)) ^ 2 * |h|) * ‖F‖ ^ 2) := hext
    _ ≤ (6 * C_Q * C_SD * Gam ^ (k_Q + 3) * ‖F‖) ^ 2 * |h| := by
        have : 0 ≤ ‖F‖ ^ 2 * |h| := mul_nonneg (sq_nonneg _) (abs_nonneg h)
        have : 0 ≤ (C_Q * C_SD * Gam ^ (k_Q + 3)) ^ 2 := sq_nonneg _
        nlinarith

end UnforcedLeray.Short.PartIIa
