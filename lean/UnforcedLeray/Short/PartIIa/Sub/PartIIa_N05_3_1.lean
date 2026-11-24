import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_3
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_1
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.Tasks.F07Surjective
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint
import UnforcedLeray.Short.PartIIa.Tasks.F12TensorDensity
import UnforcedLeray.Short.PartIIa.Tasks.F16aBodyInverseBounded
import UnforcedLeray.Short.PartIIa.Tasks.F16bBodyDirectGraph
import UnforcedLeray.Short.PartIIa.Tasks.F16cBodyAdjointGraph
import UnforcedLeray.Short.PartIIa.Tasks.F16dTensorDivRiesz

/-!


Source of record: `the November 2 reference manuscript`,
lines 1752–1756, 1769–1773, 1782–1785 (`near:local-smoothing`).

## Structure of this file

1. **Explicit polynomial-in-`Gamma` half-drift bound (`weakStressHalfDrift_explicit`,
   `seps_smooth_halfDrift_gamma`)**:
   Unpacks `commonBodyGraphBound`, `commonBodyAdjoint`, `phaseDilation_generator_D2`,
   `adjointSolvesPhaseEq`, `nuLapFibrewise`, `tensorDivRiesz`, `smoothTensorsDense`, and
   `FreeStress.free_stress_28_Y2'` to obtain a universal constant `C_HD` (independent of
   `ν, c, σ, H1, L1, M, γs, χ, χ1, ε, P, μ`) such that for every smooth tensor test `M_test`
   represented by `F : HTSpace c` and `G : HSpace c MeridC`, the phase lift
   `U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))` belongs to the domain of
   `(FreeStress.phaseC0 P).HasPow (1 / 2)` with norm `≤ C_HD * Gamma^3 * ‖F‖`.
2. **Combined smooth-test phase-lift package (`seps_smooth_phaseLift_bounds`)**:
   Combines `seps_smooth_halfDrift_gamma`, `seps_smooth_dissipation`, and `N01.epsSmoothBound`
   into a single `O(Gamma^3 ‖F‖)` bound on
   `‖U (liftVec (Teps G))‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖`.
3. **Shift `lintegral` invariances, cutoff-derivative bounds, and smooth-tensor density extension
   (`lintegral_shiftEta_eq`, `lintegral_shiftQ_eq`, `lintegral_shiftS_le`,
   `integral_shift_sub_sq_le_of_testSub_eps`, `cellL2Norm_flatStressCutRep_fderiv_le_mul`)**:
   Establishes the shift measure properties on `cellMeasure c`, proves that all directional
   derivatives `fderiv ℝ χ · v` (`pdS χ`, `pdQ χ`, `pdEta χ`) of a near cutoff `χ` satisfy
   `IsNearCutoff` and `|fderiv ℝ χ p v| ≤ cNorm8 χ`, and extends any smooth-test shift-difference
   bound from `N01.testSub c` (`N01.testSub_dense`) to all `F : HTSpace c` for any `Seps`
   satisfying `IsStressMap c ε (Teps hν hε hc hP μ) Seps`.
4. **Conditional assembly (`stressEpsHalfDriftDissipation_of`)**:
   Combines (1), (2), and (3) with the chart-pullback / cutoff-localisation leaf
   `PhaseHalfDriftDissipationCutoffShiftSE`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology SchwartzMap
open scoped ENNReal NNReal ContDiff Laplacian

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete (Chart Ten3)
open UnforcedLeray.Short.PartIIIb.NearInst (tv4 cartLift)
open N05_1Aux N05_3Aux N05_4Aux

namespace N05_3_1Aux

/-! ### 1. Explicit polynomial-in-`Gamma` half-drift bound on smooth tensor tests -/

/-- Explicit body-inverse bound with spectral factor `1 + (1 + ‖μ‖) / (μ.re + 1 / 4)`. -/
theorem bodyInverse_explicit :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ (ν : ℝ), 0 < ν →
      ∀ (μ : ℂ), 0 < μ.re + 1 / 4 →
      ∃ R : Yq P 2 →L[ℂ] Yq P 2,
        IsBodyInverse P ν μ R ∧ ‖R‖ ≤ CG * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4)) := by
  obtain ⟨CG, hCG0, hCG⟩ := commonBodyGraphBound 2 ENNReal.one_lt_two (by norm_num)
  refine ⟨CG, hCG0, ?_⟩
  intro P _ hP1 ν hν μ hμ
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hμ
  set Fμ : ℝ := 1 + (1 + ‖μ‖) / (μ.re + 1 / 4)
  have hFμ_eq : 1 + (1 + ‖μ‖) / (μ.re + gammaR 2) = Fμ := by rw [gammaR_two]
  have hFμ0 : 0 ≤ Fμ := by
    dsimp only [Fμ]
    have : 0 ≤ (1 + ‖μ‖) / (μ.re + 1 / 4) := div_nonneg (by positivity) hμ.le
    linarith
  have hbij := bodyOp_bijective_F16a P hP1 ν hν μ hμ'
  let Ebij : D P ν 2 ≃ₗ[ℂ] Yq P 2 := LinearEquiv.ofBijective (bodyOp P ν 2 μ) hbij
  let Lm : Yq P 2 →ₗ[ℂ] Yq P 2 :=
    (D P ν 2).subtype.comp (Ebij.symm.toLinearMap.comp
      (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top).toLinearMap)
  have hLm_bound : ∀ x : Yq P 2, ‖Lm x‖ ≤ (CG * Fμ) * ‖x‖ := by
    intro x
    set y := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top x
    set w : D P ν 2 := Ebij.symm y
    have hbw : bodyOp P ν 2 μ w = y := Ebij.apply_symm_apply y
    obtain ⟨g, -, hg⟩ := hCG P hP1 ν hν μ hμ' w
    rw [hbw, hFμ_eq] at hg
    have hsum : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
    have hwn : ‖(w : Yq P 2)‖ ≤ graphNormD w := by
      unfold graphNormD
      linarith [norm_nonneg (nuLapD w), norm_nonneg (T0D w)]
    have hy : ‖y‖ ≤ ‖x‖ := by
      calc ‖y‖ ≤ ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right B0414.norm_lerayY_two_le (norm_nonneg _)
        _ = ‖x‖ := one_mul _
    calc ‖Lm x‖ = ‖(w : Yq P 2)‖ := rfl
      _ ≤ graphNormD w := hwn
      _ ≤ CG * Fμ * ‖y‖ := by linarith
      _ ≤ (CG * Fμ) * ‖x‖ := mul_le_mul_of_nonneg_left hy (mul_nonneg hCG0 hFμ0)
  let R : Yq P 2 →L[ℂ] Yq P 2 := Lm.mkContinuous (CG * Fμ) hLm_bound
  refine ⟨R, ?_, LinearMap.mkContinuous_norm_le Lm (mul_nonneg hCG0 hFμ0) hLm_bound⟩
  intro f
  refine ⟨Ebij.symm (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f), rfl, ?_⟩
  exact Ebij.apply_symm_apply _

/-- Explicit direct graph bound with spectral factor `1 + (1 + ‖μ‖) / (μ.re + 1 / 4)`. -/
theorem directGraphBound_explicit :
    ∃ MB : ℝ, 0 ≤ MB ∧
      ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ (ν : ℝ), 0 < ν →
      ∀ (μ : ℂ), 0 < μ.re + 1 / 4 →
      ∀ R : Yq P 2 →L[ℂ] Yq P 2, IsBodyInverse P ν μ R →
        DirectGraphBound P R (MB * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4))) := by
  obtain ⟨CG, hCG0, hCG⟩ := commonBodyGraphBound 2 ENNReal.one_lt_two (by norm_num)
  refine ⟨(7 / 4) * CG, by positivity, ?_⟩
  intro P _ hP1 ν hν μ hμ R hRinv v
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hμ
  set Fμ : ℝ := 1 + (1 + ‖μ‖) / (μ.re + 1 / 4)
  have hFμ_eq : 1 + (1 + ‖μ‖) / (μ.re + gammaR 2) = Fμ := by rw [gammaR_two]
  have hFμ0 : 0 ≤ Fμ := by
    dsimp only [Fμ]
    have : 0 ≤ (1 + ‖μ‖) / (μ.re + 1 / 4) := div_nonneg (by positivity) hμ.le
    linarith
  obtain ⟨w, hwR, hwy⟩ := hRinv v
  obtain ⟨g, -, hg⟩ := hCG P hP1 ν hν μ hμ' w
  set y := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v
  rw [hwy, hFμ_eq] at hg
  have hsum : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hwn : ‖(w : Yq P 2)‖ ≤ graphNormD w := by
    unfold graphNormD
    linarith [norm_nonneg (nuLapD w), norm_nonneg (T0D w)]
  have hT0 : ‖T0D w‖ ≤ graphNormD w := by
    unfold graphNormD
    linarith [norm_nonneg (w : Yq P 2), norm_nonneg (nuLapD w)]
  have hy : ‖y‖ ≤ ‖v‖ := by
    calc ‖y‖ ≤ ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right B0414.norm_lerayY_two_le (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  refine ⟨T0D w - (3 / 4 : ℂ) • (w : Yq P 2), ?_, ?_⟩
  · rw [← hwR]
    exact phaseDilation_generator_D2 P ν w
  · have hnorm34 : ‖(3 / 4 : ℂ)‖ = (3 / 4 : ℝ) := by norm_num
    calc ‖T0D w - (3 / 4 : ℂ) • (w : Yq P 2)‖
        ≤ ‖T0D w‖ + ‖(3 / 4 : ℂ) • (w : Yq P 2)‖ := norm_sub_le _ _
      _ = ‖T0D w‖ + (3 / 4 : ℝ) * ‖(w : Yq P 2)‖ := by rw [norm_smul, hnorm34]
      _ ≤ (7 / 4 : ℝ) * graphNormD w := by linarith
      _ ≤ (7 / 4 : ℝ) * (CG * Fμ * ‖y‖) := by linarith
      _ ≤ (7 / 4 : ℝ) * (CG * Fμ * ‖v‖) := by gcongr
      _ = ((7 / 4) * CG * Fμ) * ‖v‖ := by ring

/-- Explicit adjoint graph bound with spectral factor `1 + (1 + ‖μ‖) / (μ.re + 1 / 4)`. -/
theorem adjointGraphBound_explicit :
    ∃ CA : ℝ, 0 ≤ CA ∧
      ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ (ν : ℝ), 0 < ν →
      ∀ (μ : ℂ), 0 < μ.re + 1 / 4 →
      ∀ R : Yq P 2 →L[ℂ] Yq P 2, IsBodyInverse P ν μ R →
        AdjointGraphBoundY P ν R (CA * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4))) := by
  obtain ⟨CA, hCA0, hCA⟩ := commonBodyAdjoint
  refine ⟨CA, hCA0, ?_⟩
  intro P _ hP1 ν hν μ hμ R hRinv v
  set Fμ : ℝ := 1 + (1 + ‖μ‖) / (μ.re + 1 / 4)
  have hFμ0 : 0 ≤ Fμ := by
    dsimp only [Fμ]
    have : 0 ≤ (1 + ‖μ‖) / (μ.re + 1 / 4) := div_nonneg (by positivity) hμ.le
    linarith
  set u := (ContinuousLinearMap.adjoint R) v
  set f := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top v
  have hsol := adjointSolvesPhaseEq P ν hν μ hμ R hRinv v
  obtain ⟨-, hmax⟩ := hCA P hP1 ν hν μ hμ f
  obtain ⟨hw, g, -, hbd⟩ := hmax u hsol
  have hfn : ‖f‖ ≤ ‖v‖ := by
    calc ‖f‖ ≤ ‖lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right B0414.norm_lerayY_two_le (norm_nonneg _)
      _ = ‖v‖ := one_mul _
  have hsum : 0 ≤ Real.sqrt ν * ∑ j, ‖g j‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hnl : ‖nuLapD (⟨u, hw⟩ : D P ν 2)‖ ≤ graphNormD (⟨u, hw⟩ : D P ν 2) := by
    unfold graphNormD
    linarith [norm_nonneg (u : Yq P 2), norm_nonneg (T0D (⟨u, hw⟩ : D P ν 2))]
  refine ⟨-(nuLapD (⟨u, hw⟩ : D P ν 2)), ?_, ?_⟩
  · have hB' := nuLapFibrewise P ν u (nuLapD (⟨u, hw⟩ : D P ν 2)) (hasPhaseOp_nuLapD ⟨u, hw⟩)
    filter_upwards [hB', Lp.coeFn_neg (nuLapD (⟨u, hw⟩ : D P ν 2))] with τ h1 h2
    have h2' : ((-(nuLapD (⟨u, hw⟩ : D P ν 2)) : Yq P 2) τ : Lp CVec3 2 (volume : Measure Space)) =
        -((nuLapD (⟨u, hw⟩ : D P ν 2) : Yq P 2) τ : Lp CVec3 2 (volume : Measure Space)) := h2
    rw [h2', neg_smul, h1]
    rw [← Lp.toTemperedDistributionCLM_apply, ← Lp.toTemperedDistributionCLM_apply, map_neg]
  · rw [norm_neg]
    have hgn : graphNormD (⟨u, hw⟩ : D P ν 2) ≤ CA * Fμ * ‖f‖ := by
      linarith [hbd, hsum]
    calc ‖nuLapD (⟨u, hw⟩ : D P ν 2)‖
        ≤ CA * Fμ * ‖f‖ := hnl.trans hgn
      _ ≤ CA * Fμ * ‖v‖ := mul_le_mul_of_nonneg_left hfn (mul_nonneg hCA0 hFμ0)

/-- Explicit quantitative `WeakStressHalfDrift` with universal constant `C₀` and explicit
dependence `1 + (1 + ‖μ‖) / (μ.re + 1 / 4)` on the spectral parameter `μ`. -/
theorem weakStressHalfDrift_explicit :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ (ν : ℝ), 0 < ν →
      ∀ (μ : ℂ), 0 < μ.re + 1 / 4 →
      ∀ S : symY2 P →L[ℂ] Yq P 2, IsWeakStressInverse P ν μ S →
      ∀ T : symY2 P,
        ∃ w : Yq P 2,
          (FreeStress.phaseC0 P).HasPow (1 / 2) (S T) w ∧
          ‖w‖ ≤ C₀ * (1 + (1 + ‖μ‖) / (μ.re + 1 / 4)) * ν ^ (-(1 / 2 : ℝ)) *
            ‖(T : Y2Sym P)‖ := by
  obtain ⟨CR, hCR0, hR⟩ := bodyInverse_explicit
  obtain ⟨MB, hMB0, hB⟩ := directGraphBound_explicit
  obtain ⟨MA, hMA0, hA⟩ := adjointGraphBound_explicit
  obtain ⟨CQ, hCQ0, hCQ⟩ := tensorDivRiesz
  refine ⟨Real.sqrt ((CR + MA) * (CR + MB)) * CQ, by positivity, ?_⟩
  intro P _ hP1 ν hν μ hμ S hS T
  set Fμ : ℝ := 1 + (1 + ‖μ‖) / (μ.re + 1 / 4)
  have hFμ0 : 0 ≤ Fμ := by
    dsimp only [Fμ]
    have : 0 ≤ (1 + ‖μ‖) / (μ.re + 1 / 4) := div_nonneg (by positivity) hμ.le
    linarith
  obtain ⟨R, hRinv, hRn⟩ := hR P hP1 ν hν μ hμ
  have hDir := hB P hP1 ν hν μ hμ R hRinv
  have hAdj := hA P hP1 ν hν μ hμ R hRinv
  obtain ⟨X, hXn, hXG⟩ := hCQ P hP1 ν hν
  obtain ⟨S0, hS0n, hS0⟩ := FreeStress.free_stress_28_Y2' P ν hν.le R
    (mul_nonneg hMA0 hFμ0) (mul_nonneg hMB0 hFμ0) hDir hAdj
  have hS0n' : ‖S0‖ ≤ Real.sqrt ((CR + MA) * (CR + MB)) * Fμ := by
    calc ‖S0‖
        ≤ Real.sqrt ((‖R‖ + MA * Fμ) * (‖R‖ + MB * Fμ)) := hS0n
      _ ≤ Real.sqrt (((CR + MA) * Fμ) * ((CR + MB) * Fμ)) := by
          refine Real.sqrt_le_sqrt (mul_le_mul ?_ ?_ (by positivity) (by positivity)) <;>
            linarith
      _ = Real.sqrt ((CR + MA) * (CR + MB) * Fμ ^ 2) := by
          congr 1; ring
      _ = Real.sqrt ((CR + MA) * (CR + MB)) * Fμ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hFμ0]
  have hmem : T ∈ closure {T : symY2 P | ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = (T : Y2Sym P)} := by
    rw [(smoothTensorsDense P).closure_eq]; exact mem_univ _
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.1 hmem
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hμ
  have hinj := (bodyOp_bijective_F16a P hP1 ν hν μ hμ').1
  have hn : ∀ n, (FreeStress.phaseC0 P).HasPow (1 / 2) (S (u n)) (S0 (X (u n))) := by
    intro n
    obtain ⟨G, hG1, hG2, hG3⟩ := hu n
    set f := testElem P 2 (tensorDiv G)
    set y := lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f
    have hp := hXG (u n) G hG1 hG2 hG3
    obtain ⟨w, hw1, hw2⟩ := hS (u n) G hG1 hG2 hG3
    obtain ⟨w', hw1', hw2'⟩ := hRinv y
    have hyfix : lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top y = y :=
      (B0414.lerayY_two_eq_self_iff y).2 (B0414.lerayY_two_mem f)
    have hww : w = w' := hinj (by rw [hw2, hw2', hyfix])
    have hSR : S (u n) = R y := by rw [← hw1, ← hw1', hww]
    rw [hSR]
    exact hS0 _ _ hp
  have hlim := FreeStress.MulRep.HasPow.of_tendsto (T := FreeStress.phaseC0 P) (s := 1 / 2)
    (by norm_num) (xn := fun n => S (u n)) (yn := fun n => S0 (X (u n)))
    ((S.continuous.tendsto T).comp hut) (((S0.comp X).continuous.tendsto T).comp hut) hn
  refine ⟨S0 (X T), hlim, ?_⟩
  have hT : ‖T‖ = ‖(T : Y2Sym P)‖ := rfl
  calc ‖S0 (X T)‖ ≤ ‖S0‖ * ‖X T‖ := S0.le_opNorm _
    _ ≤ ‖S0‖ * (‖X‖ * ‖T‖) := by gcongr; exact X.le_opNorm _
    _ ≤ (Real.sqrt ((CR + MA) * (CR + MB)) * Fμ) *
          ((CQ * ν ^ (-(1 / 2 : ℝ))) * ‖T‖) := by gcongr
    _ = Real.sqrt ((CR + MA) * (CR + MB)) * CQ * Fμ * ν ^ (-(1 / 2 : ℝ)) *
          ‖(T : Y2Sym P)‖ := by rw [hT]; ring

/-- Explicit `Gamma^3` half-drift bound for `Seps F` on smooth tensor tests `M` with a universal
constant `C_HD` independent of `ν, c, σ, H1, L1, M_bound, γs, χ, χ1, ε, P, μ`. -/
theorem seps_smooth_halfDrift_gamma :
    ∃ C_HD : ℝ, 0 ≤ C_HD ∧
      ∀ (ν c σ H1 L1 M_bound γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c),
        0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
        ∀ (ε : ℝ) (hε : 0 < ε) (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2), N01.IsPhaseLift ε P U →
        ∀ μ : ℂ, ‖μ‖ ≤ M_bound → γs ≤ μ.re + 1 / 4 →
        ∀ Seps : HTSpace c →L[ℂ] HSpace c MeridC,
          IsStressMap c ε (Teps hν hε hc hP μ) Seps →
        ∀ (M : Profile → TensorVal), IsTensorTest c M →
        ∀ (F : HTSpace c) (G : HSpace c MeridC),
          (F : Profile → TensorVal) =ᵐ[measureHT c] M →
          (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
          ∃ w : Yq P 2,
            (FreeStress.phaseC0 P).HasPow (1 / 2)
              (U (B0223.liftVec hε hc hP (Seps F))) w ∧
            ‖w‖ ≤ C_HD * Gamma ν c σ H1 L1 M_bound γs χ χ1 ^ 3 * ‖F‖ := by
  obtain ⟨C₀, hC₀, hHD⟩ := weakStressHalfDrift_explicit
  refine ⟨8 * C₀, by positivity, ?_⟩
  intro ν c σ H1 L1 M_bound γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P _ hP hP1 U hU μ hμM hμγ
    Seps hSeps M hM F G hF hG
  have hM0 : 0 ≤ M_bound := (norm_nonneg μ).trans hμM
  have hμ_pos : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγ hμγ
  set Fμ : ℝ := 1 + (1 + ‖μ‖) / (μ.re + 1 / 4)
  have hCK : 0 ≤ C₀ * Fμ := by
    refine mul_nonneg hC₀ ?_
    have : 0 ≤ (1 + ‖μ‖) / (μ.re + 1 / 4) := div_nonneg (by positivity) hμ_pos.le
    linarith
  have hHD_mu : ∀ (P' : ℝ) [Fact (0 < P')], P' ≤ 1 → ∀ ν' : ℝ, 0 < ν' → ∀ μ' ∈ ({μ} : Set ℂ),
      ∀ S : symY2 P' →L[ℂ] Yq P' 2, IsWeakStressInverse P' ν' μ' S → ∀ T : symY2 P',
        ∃ w : Yq P' 2, (FreeStress.phaseC0 P').HasPow (1 / 2) (S T) w ∧
          ‖w‖ ≤ (C₀ * Fμ) * ν' ^ (-(1 / 2 : ℝ)) * ‖(T : Y2Sym P')‖ := by
    intro P' _ hP' ν' hν' μ' hμ' S hS T
    rw [mem_singleton_iff] at hμ'
    rw [hμ'] at hS
    exact hHD P' hP' ν' hν' μ hμ_pos S hS T
  have hSeps_eq : Seps F = Teps hν hε hc hP μ G := hSeps M hM F G hF hG
  rw [hSeps_eq]
  obtain ⟨m₁, m₂, hm₁, hm₂, -, hn₁, hn₂, hdiv⟩ := N01.tensorTestReIm c hc M hM
  have hMLp : MemLp M 2 (measureHT c) := (Lp.memLp F).ae_eq hF
  have hL₁ : MemLp (fun p => tv4 (m₁ p)) 2 (measureHT c) :=
    hMLp.of_le hm₁.smooth.continuous.aestronglyMeasurable (Eventually.of_forall hn₁)
  have hL₂ : MemLp (fun p => tv4 (m₂ p)) 2 (measureHT c) :=
    hMLp.of_le hm₂.smooth.continuous.aestronglyMeasurable (Eventually.of_forall hn₂)
  set F₁ : HTSpace c := hL₁.toLp _
  set F₂ : HTSpace c := hL₂.toLp _
  have hF₁n : ‖F₁‖ ≤ ‖F‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hL₁.coeFn_toLp, hF] with p h1 h2
    rw [h1, h2]; exact hn₁ p
  have hF₂n : ‖F₂‖ ≤ ‖F‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hL₂.coeFn_toLp, hF] with p h1 h2
    rw [h1, h2]; exact hn₂ p
  have hG₁L := UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc _ hm₁
  have hG₂L := UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc _ hm₂
  set G₁ : HSpace c MeridC := hG₁L.toLp _
  set G₂ : HSpace c MeridC := hG₂L.toLp _
  have hGsplit : G = G₁ + Complex.I • G₂ := by
    apply Lp.ext
    filter_upwards [hG, hG₁L.coeFn_toLp, hG₂L.coeFn_toLp,
      Lp.coeFn_add G₁ (Complex.I • G₂), Lp.coeFn_smul Complex.I G₂] with p h h1 h2 h3 h4
    rw [h, h3, Pi.add_apply, h4, Pi.smul_apply, h1, h2, hdiv ε p, smul_add,
      smul_comm (p.1 : ℂ) Complex.I]
  obtain ⟨w₁, hw₁, hb₁⟩ :=
    seps_real_halfDrift hCK hHD_mu hν hε hc hP hP1 (mem_singleton μ) hμ_pos hU m₁ hm₁
      F₁ hL₁.coeFn_toLp G₁ hG₁L.coeFn_toLp
  obtain ⟨w₂, hw₂, hb₂⟩ :=
    seps_real_halfDrift hCK hHD_mu hν hε hc hP hP1 (mem_singleton μ) hμ_pos hU m₂ hm₂
      F₂ hL₂.coeFn_toLp G₂ hG₂L.coeFn_toLp
  rw [hGsplit, map_add, map_smul, map_add, map_smul, map_add, map_smul]
  refine ⟨w₁ + Complex.I • w₂, hw₁.add (hw₂.smul Complex.I), ?_⟩
  set Gam := Gamma ν c σ H1 L1 M_bound γs χ χ1
  have hG1 : 1 ≤ Gam := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hFμ_le : Fμ ≤ 2 * Gam ^ 2 := by
    have hbf := body_factor_le_gamma_sq χ χ1 hν hc hσ hσH hL1 hγ hμM hμγ
    rwa [gammaR_two] at hbf
  have hν_le : ν ^ (-(1 / 2 : ℝ)) ≤ Gam := by
    have h1 : ν ^ (-(1 / 2 : ℝ)) = (Real.sqrt ν)⁻¹ := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hν.le]
    rw [h1]
    exact inv_sqrt_nu_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hν0 : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
  have hb₁' : ‖w₁‖ ≤ 2 * (C₀ * Fμ) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ :=
    hb₁.trans (mul_le_mul_of_nonneg_left hF₁n (by positivity))
  have hb₂' : ‖w₂‖ ≤ 2 * (C₀ * Fμ) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ :=
    hb₂.trans (mul_le_mul_of_nonneg_left hF₂n (by positivity))
  have hprod : Fμ * ν ^ (-(1 / 2 : ℝ)) ≤ 2 * Gam ^ 3 := by
    calc Fμ * ν ^ (-(1 / 2 : ℝ))
        ≤ (2 * Gam ^ 2) * Gam := mul_le_mul hFμ_le hν_le hν0 (by positivity)
      _ = 2 * Gam ^ 3 := by ring
  calc ‖w₁ + Complex.I • w₂‖
      ≤ ‖w₁‖ + ‖Complex.I • w₂‖ := norm_add_le _ _
    _ = ‖w₁‖ + ‖w₂‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ 2 * (C₀ * Fμ) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ +
          2 * (C₀ * Fμ) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ := add_le_add hb₁' hb₂'
    _ = 4 * C₀ * (Fμ * ν ^ (-(1 / 2 : ℝ))) * ‖F‖ := by ring
    _ ≤ 4 * C₀ * (2 * Gam ^ 3) * ‖F‖ := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod (by positivity)) (norm_nonneg F)
    _ = 8 * C₀ * Gam ^ 3 * ‖F‖ := by ring

/-! ### 2. Combined smooth-test phase-lift package -/

/-- For every smooth tensor test `M` represented by `F : HTSpace c` and `G : HSpace c MeridC`,
the phase lift `U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))` simultaneously admits a
half-drift `w_hd` (`(FreeStress.phaseC0 P).HasPow (1 / 2)`) and a spatial gradient `g_diss`
(`HasGrad`) with combined norm `‖U (liftVec (Teps G))‖ + ‖w_hd‖ + ∑ j, ‖g_diss j‖` bounded by
`C_SD * Gamma^3 * ‖F‖`. -/
theorem seps_smooth_phaseLift_bounds :
    ∃ C_SD : ℝ, 0 ≤ C_SD ∧
      ∀ (ν c σ H1 L1 M_bound γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c),
        0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
        ∀ (ε : ℝ) (hε : 0 < ε) (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2), N01.IsPhaseLift ε P U →
        ∀ μ : ℂ, ‖μ‖ ≤ M_bound → γs ≤ μ.re + 1 / 4 →
        ∀ Seps : HTSpace c →L[ℂ] HSpace c MeridC,
          IsStressMap c ε (Teps hν hε hc hP μ) Seps →
        ∀ (M : Profile → TensorVal), IsTensorTest c M →
        ∀ (F : HTSpace c) (G : HSpace c MeridC),
          (F : Profile → TensorVal) =ᵐ[measureHT c] M →
          (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
          ∃ (w_hd : Yq P 2) (g_diss : Fin 3 → Yq P 2),
            (FreeStress.phaseC0 P).HasPow (1 / 2)
              (U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))) w_hd ∧
            HasGrad (U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))) g_diss ∧
            ‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ +
              ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ ≤
                C_SD * Gamma ν c σ H1 L1 M_bound γs χ χ1 ^ 3 * ‖F‖ := by
  obtain ⟨C_HD, hC_HD, hHD⟩ := seps_smooth_halfDrift_gamma
  obtain ⟨C_D, hC_D, hDiss⟩ := seps_smooth_dissipation
  refine ⟨2 + C_HD + C_D, by positivity, ?_⟩
  intro ν c σ H1 L1 M_bound γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P _ hP hP1 U hU μ hμM hμγ
    Seps hSeps M hM F G hF hG
  have hM0 : 0 ≤ M_bound := (norm_nonneg μ).trans hμM
  have hSeps_eq : Seps F = Teps hν hε hc hP μ G := hSeps M hM F G hF hG
  obtain ⟨w_hd, hw_hd, hw_bd⟩ :=
    hHD ν c σ H1 L1 M_bound γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P hP hP1 U hU μ hμM hμγ
      Seps hSeps M hM F G hF hG
  obtain ⟨g_diss, hg_diss, hg_bd⟩ :=
    hDiss ν c σ H1 L1 M_bound γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P hP hP1 U hU μ hμM hμγ
      Seps hSeps M hM F G hF hG
  rw [hSeps_eq] at hw_hd hg_diss
  refine ⟨w_hd, g_diss, hw_hd, hg_diss, ?_⟩
  set Gam := Gamma ν c σ H1 L1 M_bound γs χ χ1
  have hG1 : 1 ≤ Gam := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  have hγ_G : γs⁻¹ ≤ Gam := by
    unfold Gam Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hν_G : ν⁻¹ ≤ Gam := inv_nu_le_gamma_stress χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hsqrt_le : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ Gam := by
    have h1 : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (Real.sqrt (γs * ν))⁻¹ := by
      refine inv_anti₀ (Real.sqrt_pos.2 (mul_pos hγ hν)) (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_right hμγ hν.le
    have h2 : ((Real.sqrt (γs * ν))⁻¹) ^ 2 ≤ Gam ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_pos hγ hν).le, mul_inv, sq]
      exact mul_le_mul hγ_G hν_G (inv_pos.2 hν).le hG0
    exact h1.trans (abs_le_of_sq_le_sq' h2 hG0).2
  have hG_G3 : Gam ≤ Gam ^ 3 := by
    simpa using pow_le_pow_right₀ hG1 (by norm_num : 1 ≤ 3)
  have hU_norm : ‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ ≤ 2 * Gam ^ 3 * ‖F‖ := by
    rw [U.norm_map, (B0223.liftVec hε hc hP).norm_map, ← hSeps_eq]
    have h1 := stressMap_eps_norm_le hν hε hc hP hP1 (lt_of_lt_of_le hγ hμγ) hSeps F
    calc ‖Seps F‖
        ≤ 2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := h1
      _ ≤ 2 * Gam ^ 3 * ‖F‖ := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hsqrt_le.trans hG_G3) zero_le_two) (norm_nonneg F)
  have hg_bd' : ∑ j : Fin 3, ‖g_diss j‖ ≤ C_D * Gam ^ 3 * ‖F‖ := by
    calc ∑ j : Fin 3, ‖g_diss j‖
        ≤ C_D * Gam * ‖F‖ := hg_bd
      _ ≤ C_D * Gam ^ 3 * ‖F‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG_G3 hC_D) (norm_nonneg F)
  linarith

/-! ### 3. Shift `lintegral` invariances, cutoff derivatives, and density extension -/

theorem measurable_shiftS (h : ℝ) : Measurable (shiftS h) :=
  measurable_shiftS_uncurry.comp (measurable_const.prodMk measurable_id)

theorem measurable_shiftQ (h : ℝ) : Measurable (shiftQ h) :=
  measurable_shiftQ_uncurry.comp (measurable_const.prodMk measurable_id)

theorem measurable_shiftEta (h : ℝ) : Measurable (shiftEta h) :=
  measurable_shiftEta_uncurry.comp (measurable_const.prodMk measurable_id)

/-- `shiftEta h` preserves `lintegral` on `cellMeasure c`. -/
theorem lintegral_shiftEta_eq (c h : ℝ) {f : Profile → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f (shiftEta h p) ∂(cellMeasure c) = ∫⁻ p, f p ∂(cellMeasure c) := by
  rw [lintegral_cellMeasure c (fun p => f (shiftEta h p)) (hf.comp (measurable_shiftEta h)),
    lintegral_cellMeasure c f hf]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  refine setLIntegral_congr_fun measurableSet_Ioc fun q _ => ?_
  exact lintegral_add_right_eq_self (fun η => f (s, q, η)) h

/-- `shiftQ h` preserves `lintegral` on `cellMeasure c` for `c`-periodic integrands. -/
theorem lintegral_shiftQ_eq {c : ℝ} (hc : 0 < c) (h : ℝ) {f : Profile → ℝ≥0∞}
    (hf : Measurable f) (hper : QPeriodic c f) :
    ∫⁻ p, f (shiftQ h p) ∂(cellMeasure c) = ∫⁻ p, f p ∂(cellMeasure c) := by
  rw [lintegral_cellMeasure c (fun p => f (shiftQ h p)) (hf.comp (measurable_shiftQ h)),
    lintegral_cellMeasure c f hf]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  let g : ℝ → ℝ≥0∞ := fun q => ∫⁻ η, f (s, q, η)
  have hgper : Function.Periodic g c := fun q => by
    dsimp only [g]
    congr 1
    funext η
    exact hper (s, q, η)
  have hshift := lintegral_period_shift (ε := 1 / 2) (by norm_num) hc g hgper h
  have hc1 : (2 : ℝ) * (1 / 2) * c = c := by ring
  have hc2 : ENNReal.ofReal ((2 : ℝ) * (1 / 2)) = 1 := by norm_num
  rw [hc1, hc2, one_mul] at hshift
  refine Eq.trans ?_ hshift
  refine setLIntegral_congr_fun measurableSet_Ioc fun q _ => ?_
  dsimp only [g, shiftQ]
  have hq : q + h = h + q / ((2 : ℝ) * (1 / 2)) := by ring
  rw [hq]

/-- `shiftS h` contracts `lintegral` on `cellMeasure c` for integrands vanishing on `s ≤ 0`. -/
theorem lintegral_shiftS_le (c h : ℝ) {f : Profile → ℝ≥0∞} (hf : Measurable f)
    (hsupp : ∀ p : Profile, p.1 ≤ 0 → f p = 0) :
    ∫⁻ p, f (shiftS h p) ∂(cellMeasure c) ≤ ∫⁻ p, f p ∂(cellMeasure c) := by
  rw [lintegral_cellMeasure c (fun p => f (shiftS h p)) (hf.comp (measurable_shiftS h)),
    lintegral_cellMeasure c f hf]
  let N : ℝ → ℝ≥0∞ := fun s => ∫⁻ q in Ioc 0 c, ∫⁻ η, f (s, q, η)
  change ∫⁻ s in Ioi (0 : ℝ), N (s + h) ≤ ∫⁻ s in Ioi (0 : ℝ), N s
  calc ∫⁻ s in Ioi (0 : ℝ), N (s + h)
      ≤ ∫⁻ s, N (s + h) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ s, N s := lintegral_add_right_eq_self N h
    _ = ∫⁻ s in Ioi (0 : ℝ), N s := by
        symm
        refine setLIntegral_eq_of_support_subset fun s hs => ?_
        rw [mem_Ioi]
        by_contra hle
        apply hs
        have hs0 : s ≤ 0 := not_lt.1 hle
        have hzero : ∀ q η, f (s, q, η) = 0 := fun q η => hsupp (s, q, η) hs0
        simp [N, hzero]

theorem ae_cell_cellMeasure (c : ℝ) : ∀ᵐ p ∂(cellMeasure c), p ∈ cell c := by
  have hcell : MeasurableSet (cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  exact ae_restrict_mem hcell

theorem ae_cellMeasure_of_ae_measureH {c : ℝ} {P_prop : Profile → Prop}
    (hP : ∀ᵐ p ∂(measureH c), P_prop p) : ∀ᵐ p ∂(cellMeasure c), P_prop p := by
  have h1 : ∀ᵐ p ∂(cellMeasure c), weightH p ≠ 0 → P_prop p :=
    (ae_withDensity_iff measurable_weightH).1 hP
  filter_upwards [h1, ae_cell_cellMeasure c] with p hp hpcell
  refine hp ?_
  unfold weightH
  exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpcell.1 _)).ne'

theorem flatStressCutRep_sub_ae_cellMeasure {c : ℝ} (hc : 0 < c) (χ : Profile → ℝ)
    (W₁ W₂ : HSpace c MeridC) :
    (fun p => flatStressCutRep c χ W₁ p - flatStressCutRep c χ W₂ p) =ᵐ[cellMeasure c]
      flatStressCutRep c χ (W₁ - W₂) := by
  have hsub : ∀ᵐ p ∂(cellMeasure c),
      (W₁ - W₂ : HSpace c MeridC) p = W₁ p - W₂ p :=
    ae_cellMeasure_of_ae_measureH (Lp.coeFn_sub W₁ W₂)
  filter_upwards [hsub, ae_cell_cellMeasure c] with p hp hpcell
  simp only [flatStressCutRep, periodize_of_mem hc _ hpcell, hp, smul_sub]

theorem flatStressCutRep_shift_sub_ae_cellMeasure {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {shift : Profile → Profile} (hshift : Measurable shift)
    (hlint : ∀ f : Profile → ℝ≥0∞, Measurable f → QPeriodic c f →
      (∀ p : Profile, p.1 ≤ 0 → f p = 0) →
      ∫⁻ p, f (shift p) ∂(cellMeasure c) ≤ ∫⁻ p, f p ∂(cellMeasure c))
    (W₁ W₂ : HSpace c MeridC) :
    (fun p => flatStressCutRep c χ W₁ (shift p) - flatStressCutRep c χ W₂ (shift p))
      =ᵐ[cellMeasure c]
      (fun p => flatStressCutRep c χ (W₁ - W₂) (shift p)) := by
  let g : Profile → MeridC := fun p =>
    flatStressCutRep c χ W₁ p - flatStressCutRep c χ W₂ p - flatStressCutRep c χ (W₁ - W₂) p
  have hg_meas : Measurable g :=
    ((measurable_flatStressCutRep c hm W₁).sub (measurable_flatStressCutRep c hm W₂)).sub
      (measurable_flatStressCutRep c hm (W₁ - W₂))
  have hg_per : QPeriodic c g := fun p => by
    simp only [g, flatStressCutRep_periodic hc hχ W₁ p, flatStressCutRep_periodic hc hχ W₂ p,
      flatStressCutRep_periodic hc hχ (W₁ - W₂) p]
  have hg_supp : ∀ p : Profile, p.1 ≤ 0 → ‖g p‖ₑ = 0 := fun p hp0 => by
    have hχ0 : χ p = 0 := by
      by_contra hne
      have hs := (hχ.support p hne).1
      linarith
    simp [g, flatStressCutRep, hχ0]
  have hg_ae : g =ᵐ[cellMeasure c] 0 := by
    filter_upwards [flatStressCutRep_sub_ae_cellMeasure hc χ W₁ W₂] with p hp
    simp [g, hp]
  have hlint0 : ∫⁻ p, ‖g p‖ₑ ∂(cellMeasure c) = 0 := by
    rw [lintegral_eq_zero_iff hg_meas.enorm]
    filter_upwards [hg_ae] with p hp
    simp [hp]
  have hshift0 : ∫⁻ p, ‖g (shift p)‖ₑ ∂(cellMeasure c) = 0 := by
    refine le_antisymm ?_ (by positivity)
    rw [← hlint0]
    exact hlint (fun p => ‖g p‖ₑ) hg_meas.enorm (fun p => by dsimp only; rw [hg_per p]) hg_supp
  have hae_shift : (fun p => ‖g (shift p)‖ₑ) =ᵐ[cellMeasure c] 0 :=
    (lintegral_eq_zero_iff (hg_meas.comp hshift).enorm).1 hshift0
  filter_upwards [hae_shift] with p hp
  have h0 : g (shift p) = 0 := enorm_eq_zero.1 hp
  exact sub_eq_zero.1 h0

/-- Unconditional `L²(cellMeasure c)` shift-difference bound for `flatStressCutRep c χ W`. -/
theorem lintegral_shift_sub_flatStressCutRep_sq_le {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    {shift : Profile → Profile} (hshift : Measurable shift)
    (hlint : ∀ f : Profile → ℝ≥0∞, Measurable f → QPeriodic c f →
      (∀ p : Profile, p.1 ≤ 0 → f p = 0) →
      ∫⁻ p, f (shift p) ∂(cellMeasure c) ≤ ∫⁻ p, f p ∂(cellMeasure c))
    (W : HSpace c MeridC) :
    ∫⁻ p, ‖flatStressCutRep c χ W (shift p) - flatStressCutRep c χ W p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((2 * ((1 + H1) * cNorm8 χ * ‖W‖)) ^ 2) := by
  let u := flatStressCutRep c χ W
  have hu : Measurable u := measurable_flatStressCutRep c hm W
  have hpt : ∀ p : Profile,
      ‖u (shift p) - u p‖ₑ ^ (2 : ℝ) ≤
        2 * ‖u (shift p)‖ₑ ^ (2 : ℝ) + 2 * ‖u p‖ₑ ^ (2 : ℝ) := fun p => by
    have hreal : ‖u (shift p) - u p‖ ^ 2 ≤ 2 * ‖u (shift p)‖ ^ 2 + 2 * ‖u p‖ ^ 2 := by
      have htri : ‖u (shift p) - u p‖ ≤ ‖u (shift p)‖ + ‖u p‖ := norm_sub_le _ _
      have hsq : ‖u (shift p) - u p‖ ^ 2 ≤ (‖u (shift p)‖ + ‖u p‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖u (shift p)‖ - ‖u p‖)]
    have h1 : ‖u (shift p) - u p‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖u (shift p) - u p‖ ^ 2) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    have h2 : 2 * ‖u (shift p)‖ₑ ^ (2 : ℝ) + 2 * ‖u p‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (2 * ‖u (shift p)‖ ^ 2 + 2 * ‖u p‖ ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat, ← ofReal_norm, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two, Real.rpow_two]
    rw [h1, h2]
    exact ENNReal.ofReal_le_ofReal hreal
  have hf_meas : Measurable (fun p => ‖u p‖ₑ ^ (2 : ℝ)) := hu.enorm.pow_const (2 : ℝ)
  have hf_per : QPeriodic c (fun p => ‖u p‖ₑ ^ (2 : ℝ)) := fun p => by
    dsimp only [u]
    rw [flatStressCutRep_periodic hc hχ W p]
  have hf_supp : ∀ p : Profile, p.1 ≤ 0 → ‖u p‖ₑ ^ (2 : ℝ) = 0 := fun p hp0 => by
    have h0 : u p = 0 := by
      by_contra hne
      have hs := (flatStressCutRep_support hχ W p hne).1
      linarith
    simp [h0]
  have hshift_le := hlint _ hf_meas hf_per hf_supp
  have hbase := lintegral_flatStressCutRep_sq_le hc hσ hσH hχ hm W
  have hsh_meas : Measurable (fun p => ‖u (shift p)‖ₑ ^ (2 : ℝ)) := hf_meas.comp hshift
  calc ∫⁻ p, ‖u (shift p) - u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
      ≤ ∫⁻ p, (2 * ‖u (shift p)‖ₑ ^ (2 : ℝ) + 2 * ‖u p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
        lintegral_mono hpt
    _ = 2 * ∫⁻ p, ‖u (shift p)‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) +
          2 * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
        rw [lintegral_add_left (hsh_meas.const_mul 2),
          lintegral_const_mul 2 hsh_meas, lintegral_const_mul 2 hf_meas]
    _ ≤ 2 * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) +
          2 * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by gcongr
    _ = 4 * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by ring
    _ ≤ 4 * ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by gcongr
    _ = ENNReal.ofReal ((2 * ((1 + H1) * cNorm8 χ * ‖W‖)) ^ 2) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- Unconditional density extension from smooth tensor tests (`N01.testSub c`) to all `F : HTSpace c`
for any `ε > 0` stress map `Seps` (`IsStressMap c ε (Teps hν hε hc hP μ) Seps`). -/
theorem integral_shift_sub_sq_le_of_testSub_eps {ν ε c P σ H1 L1 : ℝ} [Fact (0 < P)]
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (hσ : 0 < σ) (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    (hm : Measurable χ) {μ : ℂ}
    {Seps : HTSpace c →L[ℂ] HSpace c MeridC} (hSeps : IsStressMap c ε (Teps hν hε hc hP μ) Seps)
    {shift : Profile → Profile} (hshift : Measurable shift)
    (hlint : ∀ f : Profile → ℝ≥0∞, Measurable f → QPeriodic c f →
      (∀ p : Profile, p.1 ≤ 0 → f p = 0) →
      ∫⁻ p, f (shift p) ∂(cellMeasure c) ≤ ∫⁻ p, f p ∂(cellMeasure c))
    {K : ℝ} (hK : 0 ≤ K)
    (hsmooth : ∀ (M : Profile → TensorVal) (_hM : IsTensorTest c M)
      (x : HTSpace c) (G : HSpace c MeridC),
      (x : Profile → TensorVal) =ᵐ[measureHT c] M →
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
      ∫ p, ‖flatStressCutRep c χ (Teps hν hε hc hP μ G) (shift p) -
          flatStressCutRep c χ (Teps hν hε hc hP μ G) p‖ ^ 2 ∂(cellMeasure c) ≤ K * ‖x‖ ^ 2)
    (F : HTSpace c) :
    ∫ p, ‖flatStressCutRep c χ (Seps F) (shift p) -
        flatStressCutRep c χ (Seps F) p‖ ^ 2 ∂(cellMeasure c) ≤ 2 * (K * ‖F‖ ^ 2) := by
  let uF := flatStressCutRep c χ (Seps F)
  have huF_meas : Measurable (fun p => uF (shift p) - uF p) :=
    ((measurable_flatStressCutRep c hm (Seps F)).comp hshift).sub
      (measurable_flatStressCutRep c hm (Seps F))
  have huF_lint := lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm hshift hlint (Seps F)
  have huF_int : Integrable (fun p => ‖uF (shift p) - uF p‖ ^ 2) (cellMeasure c) := by
    have hmem : MemLp (fun p => uF (shift p) - uF p) 2 (cellMeasure c) := by
      refine ⟨huF_meas.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (lt_of_le_of_lt huF_lint ENNReal.ofReal_lt_top).ne
    exact hmem.integrable_norm_pow two_ne_zero
  refine le_of_forall_pos_lt_add fun δ_eps hδ_eps => ?_
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  let C_op : ℝ := 2 * ((1 + H1) * cNorm8 χ * ‖Seps‖) + 1
  have hCop_pos : 0 < C_op := by
    dsimp only [C_op]
    have : 0 ≤ (1 + H1) * cNorm8 χ * ‖Seps‖ :=
      mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg Seps)
    linarith
  let δ1 : ℝ := Real.sqrt (δ_eps / 4) / C_op
  let δ2 : ℝ := δ_eps / (4 * (K + 1) * (2 * ‖F‖ + 1))
  let δ : ℝ := min 1 (min δ1 δ2)
  have hδ_pos : 0 < δ := by
    dsimp only [δ, δ1, δ2]
    refine lt_min zero_lt_one (lt_min ?_ ?_) <;> positivity
  have hdense := Metric.mem_closure_iff.1 (N01.testSub_dense c hc F) δ hδ_pos
  obtain ⟨x, ⟨x_sub, rfl⟩, hdist⟩ := hdense
  let x : HTSpace c := x_sub.1
  obtain ⟨M, hM, hxM⟩ := x_sub.2
  let G : HSpace c MeridC :=
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc M hM).toLp _
  have hG : (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) :=
    MemLp.coeFn_toLp _
  have hSeps_x : Seps x = Teps hν hε hc hP μ G := hSeps M hM x G hxM hG
  let ux := flatStressCutRep c χ (Seps x)
  let ud := flatStressCutRep c χ (Seps (F - x))
  have hux_int : Integrable (fun p => ‖ux (shift p) - ux p‖ ^ 2) (cellMeasure c) := by
    have hm_ux : Measurable (fun p => ux (shift p) - ux p) :=
      ((measurable_flatStressCutRep c hm (Seps x)).comp hshift).sub
        (measurable_flatStressCutRep c hm (Seps x))
    have hmem : MemLp (fun p => ux (shift p) - ux p) 2 (cellMeasure c) := by
      refine ⟨hm_ux.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (lt_of_le_of_lt
          (lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm hshift hlint (Seps x))
          ENNReal.ofReal_lt_top).ne
    exact hmem.integrable_norm_pow two_ne_zero
  have hud_int : Integrable (fun p => ‖ud (shift p) - ud p‖ ^ 2) (cellMeasure c) := by
    have hm_ud : Measurable (fun p => ud (shift p) - ud p) :=
      ((measurable_flatStressCutRep c hm (Seps (F - x))).comp hshift).sub
        (measurable_flatStressCutRep c hm (Seps (F - x)))
    have hmem : MemLp (fun p => ud (shift p) - ud p) 2 (cellMeasure c) := by
      refine ⟨hm_ud.aestronglyMeasurable, ?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
        ENNReal.toReal_ofNat]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (lt_of_le_of_lt
          (lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm hshift hlint (Seps (F - x)))
          ENNReal.ofReal_lt_top).ne
    exact hmem.integrable_norm_pow two_ne_zero
  have hae_diff : ∀ᵐ p ∂(cellMeasure c),
      uF (shift p) - uF p = (ux (shift p) - ux p) + (ud (shift p) - ud p) := by
    have hSeps_sub : Seps F - Seps x = Seps (F - x) := (map_sub Seps F x).symm
    have h1 := flatStressCutRep_sub_ae_cellMeasure hc χ (Seps F) (Seps x)
    have h2 := flatStressCutRep_shift_sub_ae_cellMeasure hc hσ hχ hm hshift hlint (Seps F) (Seps x)
    filter_upwards [h1, h2] with p hp1 hp2
    dsimp only [uF, ux, ud] at hp1 hp2 ⊢
    rw [← hSeps_sub, ← hp1, ← hp2]
    abel
  have hpt_le : ∀ᵐ p ∂(cellMeasure c),
      ‖uF (shift p) - uF p‖ ^ 2 ≤
        2 * ‖ux (shift p) - ux p‖ ^ 2 + 2 * ‖ud (shift p) - ud p‖ ^ 2 := by
    filter_upwards [hae_diff] with p hp
    rw [hp]
    have htri : ‖(ux (shift p) - ux p) + (ud (shift p) - ud p)‖ ≤
        ‖ux (shift p) - ux p‖ + ‖ud (shift p) - ud p‖ := norm_add_le _ _
    have hsq : ‖(ux (shift p) - ux p) + (ud (shift p) - ud p)‖ ^ 2 ≤
        (‖ux (shift p) - ux p‖ + ‖ud (shift p) - ud p‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖ux (shift p) - ux p‖ - ‖ud (shift p) - ud p‖)]
  have hint_split : ∫ p, ‖uF (shift p) - uF p‖ ^ 2 ∂(cellMeasure c) ≤
      2 * ∫ p, ‖ux (shift p) - ux p‖ ^ 2 ∂(cellMeasure c) +
      2 * ∫ p, ‖ud (shift p) - ud p‖ ^ 2 ∂(cellMeasure c) := by
    calc ∫ p, ‖uF (shift p) - uF p‖ ^ 2 ∂(cellMeasure c)
        ≤ ∫ p, (2 * ‖ux (shift p) - ux p‖ ^ 2 + 2 * ‖ud (shift p) - ud p‖ ^ 2) ∂(cellMeasure c) :=
          integral_mono_ae huF_int ((hux_int.const_mul 2).add (hud_int.const_mul 2)) hpt_le
      _ = 2 * ∫ p, ‖ux (shift p) - ux p‖ ^ 2 ∂(cellMeasure c) +
          2 * ∫ p, ‖ud (shift p) - ud p‖ ^ 2 ∂(cellMeasure c) := by
          rw [integral_add (hux_int.const_mul 2) (hud_int.const_mul 2),
            integral_const_mul, integral_const_mul]
  have hux_le : ∫ p, ‖ux (shift p) - ux p‖ ^ 2 ∂(cellMeasure c) ≤ K * ‖x‖ ^ 2 := by
    dsimp only [ux]
    rw [hSeps_x]
    exact hsmooth M hM x G hxM hG
  have hud_le : ∫ p, ‖ud (shift p) - ud p‖ ^ 2 ∂(cellMeasure c) ≤
      (2 * ((1 + H1) * cNorm8 χ * ‖Seps (F - x)‖)) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [ofReal_integral_eq_lintegral_ofReal hud_int (Eventually.of_forall fun _ => sq_nonneg _)]
    have hcongr : (∫⁻ p, ENNReal.ofReal (‖ud (shift p) - ud p‖ ^ 2) ∂(cellMeasure c)) =
        ∫⁻ p, ‖ud (shift p) - ud p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
      refine lintegral_congr fun p => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
    rw [hcongr]
    exact lintegral_shift_sub_flatStressCutRep_sq_le hc hσ hσH hχ hm hshift hlint (Seps (F - x))
  have hFx_lt : ‖F - x‖ < δ := by rwa [← dist_eq_norm]
  have hFx_le1 : ‖F - x‖ ≤ 1 := hFx_lt.le.trans (min_le_left 1 _)
  have hFx_le_δ1 : ‖F - x‖ ≤ δ1 :=
    hFx_lt.le.trans ((min_le_right 1 _).trans (min_le_left δ1 δ2))
  have hFx_le_δ2 : ‖F - x‖ ≤ δ2 :=
    hFx_lt.le.trans ((min_le_right 1 _).trans (min_le_right δ1 δ2))
  have hud_bound : 2 * ∫ p, ‖ud (shift p) - ud p‖ ^ 2 ∂(cellMeasure c) ≤ δ_eps / 2 := by
    have h1 : 2 * ((1 + H1) * cNorm8 χ * ‖Seps (F - x)‖) ≤ C_op * ‖F - x‖ := by
      have hSeps_op : ‖Seps (F - x)‖ ≤ ‖Seps‖ * ‖F - x‖ := Seps.le_opNorm (F - x)
      calc 2 * ((1 + H1) * cNorm8 χ * ‖Seps (F - x)‖)
          ≤ 2 * ((1 + H1) * cNorm8 χ * (‖Seps‖ * ‖F - x‖)) := by
            gcongr
            exact mul_nonneg (by linarith) (cNorm8_nonneg χ)
        _ = (2 * ((1 + H1) * cNorm8 χ * ‖Seps‖)) * ‖F - x‖ := by ring
        _ ≤ C_op * ‖F - x‖ := by
            dsimp only [C_op]
            nlinarith [norm_nonneg (F - x)]
    have h2 : C_op * ‖F - x‖ ≤ Real.sqrt (δ_eps / 4) := by
      calc C_op * ‖F - x‖ ≤ C_op * δ1 := mul_le_mul_of_nonneg_left hFx_le_δ1 hCop_pos.le
        _ = Real.sqrt (δ_eps / 4) := mul_div_cancel₀ _ hCop_pos.ne'
    have h3 : (2 * ((1 + H1) * cNorm8 χ * ‖Seps (F - x)‖)) ^ 2 ≤ δ_eps / 4 := by
      have h0_lhs : 0 ≤ 2 * ((1 + H1) * cNorm8 χ * ‖Seps (F - x)‖) :=
        mul_nonneg zero_le_two
          (mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg _))
      calc (2 * ((1 + H1) * cNorm8 χ * ‖Seps (F - x)‖)) ^ 2
          ≤ (Real.sqrt (δ_eps / 4)) ^ 2 :=
            pow_le_pow_left₀ h0_lhs (h1.trans h2) 2
        _ = δ_eps / 4 := Real.sq_sqrt (by positivity)
    linarith
  have hux_bound : 2 * (K * ‖x‖ ^ 2) < 2 * (K * ‖F‖ ^ 2) + δ_eps / 2 := by
    have hx_le : ‖x‖ ≤ ‖F‖ + ‖F - x‖ := by
      have := norm_sub_le F (F - x)
      simpa using this
    have hx_sq : ‖x‖ ^ 2 ≤ ‖F‖ ^ 2 + (2 * ‖F‖ + 1) * ‖F - x‖ := by
      have hsq : ‖x‖ ^ 2 ≤ (‖F‖ + ‖F - x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg x) hx_le 2
      have hpow : ‖F - x‖ ^ 2 ≤ ‖F - x‖ := by
        nlinarith [norm_nonneg (F - x)]
      nlinarith
    have hK_diff : 2 * K * ((2 * ‖F‖ + 1) * ‖F - x‖) < δ_eps / 2 := by
      calc 2 * K * ((2 * ‖F‖ + 1) * ‖F - x‖)
          ≤ 2 * K * ((2 * ‖F‖ + 1) * δ2) := by gcongr
        _ < 2 * (K + 1) * ((2 * ‖F‖ + 1) * δ2) := by
            have hδ2_pos : 0 < (2 * ‖F‖ + 1) * δ2 := by
              dsimp only [δ2]; positivity
            nlinarith
        _ = δ_eps / 2 := by
            dsimp only [δ2]
            have hne1 : K + 1 ≠ 0 := by linarith
            have hne2 : 2 * ‖F‖ + 1 ≠ 0 := by positivity
            field_simp
            ring
    nlinarith
  linarith

/-- For any near cutoff `χ`, `fderiv ℝ χ` is `c`-periodic in `q`. -/
theorem fderiv_periodic_of_nearCutoff {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    fderiv ℝ χ (p.1, p.2.1 + c, p.2.2) = fderiv ℝ χ p := by
  let a : Profile := (0, c, 0)
  have hpa : (p.1, p.2.1 + c, p.2.2) = p + a := by
    ext <;> simp [a]
  have hfun : (χ ∘ fun q : Profile => q + a) = χ := by
    funext q
    change χ (q + a) = χ q
    have hqa : q + a = (q.1, q.2.1 + c, q.2.2) := by
      ext <;> simp [a]
    rw [hqa]
    exact hχ.periodic q
  have hd1 : HasFDerivAt χ (fderiv ℝ χ (p + a)) (p + a) :=
    (hχ.smooth.differentiable (by decide) (p + a)).hasFDerivAt
  have hd2 : HasFDerivAt (fun q : Profile => q + a) (ContinuousLinearMap.id ℝ Profile) p := by
    simpa using (hasFDerivAt_id p).add_const a
  have hcomp : HasFDerivAt (χ ∘ fun q : Profile => q + a) (fderiv ℝ χ (p + a)) p := by
    simpa using hd1.comp p hd2
  rw [hfun] at hcomp
  rw [hpa, hcomp.fderiv]

/-- For any near cutoff `χ`, `fderiv ℝ χ` is supported in `[σ, H1] × ℝ × [-L1, L1]`. -/
theorem fderiv_support_of_nearCutoff {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) (hp : fderiv ℝ χ p ≠ 0) :
    σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1 := by
  by_contra hnot
  apply hp
  let S : Set Profile := {q : Profile | σ ≤ q.1 ∧ q.1 ≤ H1 ∧ |q.2.2| ≤ L1}
  have hS_closed : IsClosed S :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_le (continuous_snd.comp continuous_snd).abs continuous_const))
  have hp_mem : Sᶜ ∈ 𝓝 p := hS_closed.isOpen_compl.mem_nhds hnot
  have hev : χ =ᶠ[𝓝 p] (0 : Profile → ℝ) :=
    Filter.eventuallyEq_iff_exists_mem.2
      ⟨Sᶜ, hp_mem, fun q hq => by_contra fun h0 => hq (hχ.support q h0)⟩
  rw [hev.fderiv_eq]
  simp

/-- Pointwise bound `‖fderiv ℝ χ p‖ ≤ cNorm8 χ` for any near cutoff `χ`. -/
theorem norm_fderiv_le_cNorm8_of_nearCutoff {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (p : Profile) :
    ‖fderiv ℝ χ p‖ ≤ cNorm8 χ := by
  let K : Set Profile := Icc σ H1 ×ˢ (Icc 0 c ×ˢ Icc (-L1) L1)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : Continuous (fun q : Profile => ‖fderiv ℝ χ q‖) :=
    (hχ.smooth.continuous_fderiv (by decide)).norm
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hper1 : QPeriodic c (fun q : Profile => ‖fderiv ℝ χ q‖) := fun q => by
    dsimp only
    rw [fderiv_periodic_of_nearCutoff hχ q]
  have hbdd : BddAbove (range fun q : Profile => ‖iteratedFDeriv ℝ 1 χ q‖) := by
    refine ⟨max C1 0, ?_⟩
    rintro _ ⟨q, rfl⟩
    dsimp only
    rw [norm_iteratedFDeriv_one]
    let q' : Profile := (q.1, reduceIoc c q.2.1, q.2.2)
    have hpeq : ‖fderiv ℝ χ q'‖ = ‖fderiv ℝ χ q‖ :=
      periodic_reduceIoc_eq (fun r => ‖fderiv ℝ χ r‖) hper1 q.1 q.2.1 q.2.2
    rw [← hpeq]
    by_cases h0 : fderiv ℝ χ q' = 0
    · simp [h0]
    · obtain ⟨hs1, hs2, hη⟩ := fderiv_support_of_nearCutoff hχ q' h0
      have hq' : q' ∈ K := ⟨⟨hs1, hs2⟩, Ioc_subset_Icc_self (reduceIoc_mem hc q.2.1), abs_le.1 hη⟩
      have hle : ‖fderiv ℝ χ q'‖ ≤ C1 := by simpa using hC1 q' hq'
      exact hle.trans (le_max_left C1 0)
  rw [← norm_iteratedFDeriv_one]
  calc ‖iteratedFDeriv ℝ 1 χ p‖
      ≤ ⨆ q, ‖iteratedFDeriv ℝ 1 χ q‖ := le_ciSup hbdd p
    _ ≤ ∑ k ∈ Finset.range 9, ⨆ q, ‖iteratedFDeriv ℝ k χ q‖ :=
        Finset.single_le_sum (fun k _ => Real.iSup_nonneg fun _ => norm_nonneg _)
          (Finset.mem_range.2 (by omega))
    _ = cNorm8 χ := rfl

/-- Directional derivative `fun p => fderiv ℝ χ p v` of a near cutoff `χ` is itself a near cutoff. -/
theorem isNearCutoff_fderiv_apply {c σ H1 L1 : ℝ} {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) (v : Profile) :
    IsNearCutoff c σ H1 L1 (fun p => fderiv ℝ χ p v) where
  smooth := (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp
    (hχ.smooth.fderiv_right (by decide))
  periodic p := by
    dsimp only
    rw [fderiv_periodic_of_nearCutoff hχ p]
  support p hp :=
    fderiv_support_of_nearCutoff hχ p fun h0 => hp (by simp [h0])

theorem abs_fderiv_apply_le_cNorm8 {c σ H1 L1 : ℝ} (hc : 0 < c) {χ : Profile → ℝ}
    (hχ : IsNearCutoff c σ H1 L1 χ) {v : Profile} (hv : ‖v‖ ≤ 1) (p : Profile) :
    |fderiv ℝ χ p v| ≤ cNorm8 χ := by
  rw [← Real.norm_eq_abs]
  calc ‖fderiv ℝ χ p v‖
      ≤ ‖fderiv ℝ χ p‖ * ‖v‖ := (fderiv ℝ χ p).le_opNorm v
    _ ≤ cNorm8 χ * 1 := mul_le_mul (norm_fderiv_le_cNorm8_of_nearCutoff hc hχ p) hv
        (norm_nonneg v) (cNorm8_nonneg χ)
    _ = cNorm8 χ := mul_one _

/-- Unweighted `L²(cellMeasure c)` bound on `flatStressCutRep c (fun q => fderiv ℝ χ q v) W` for
any directional derivative with `‖v‖ ≤ 1`. -/
theorem cellL2Norm_flatStressCutRep_fderiv_le_mul {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    (hσH : σ ≤ H1) {χ : Profile → ℝ} (hχ : IsNearCutoff c σ H1 L1 χ)
    {v : Profile} (hv : ‖v‖ ≤ 1) (W : HSpace c MeridC) :
    cellL2Norm c (flatStressCutRep c (fun q => fderiv ℝ χ q v) W) ≤
      (1 + H1) * cNorm8 χ * ‖W‖ := by
  let dχ : Profile → ℝ := fun q => fderiv ℝ χ q v
  have hdχ : IsNearCutoff c σ H1 L1 dχ := isNearCutoff_fderiv_apply hχ v
  have hm : Measurable dχ := hdχ.smooth.continuous.measurable
  let u := flatStressCutRep c dχ W
  have hu : Measurable u := measurable_flatStressCutRep c hm W
  have hstep1 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
    calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ∫⁻ p, ENNReal.ofReal ((1 + H1) ^ 2) *
            (weightH p * ‖u p‖ₑ ^ (2 : ℝ)) ∂(cellMeasure c) :=
          lintegral_mono (flatStressCutRep_enorm_sq_le hσ hσH hdχ W)
      _ = ENNReal.ofReal ((1 + H1) ^ 2) *
            ∫⁻ p, weightH p * ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) :=
          lintegral_const_mul _ (measurable_weightH.mul (hu.enorm.pow_const (2 : ℝ)))
      _ = ENNReal.ofReal ((1 + H1) ^ 2) * ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
          rw [measureH, lintegral_withDensity_eq_lintegral_mul _
            measurable_weightH (hu.enorm.pow_const (2 : ℝ))]
          rfl
  have hB : ∀ p, |dχ p| ≤ cNorm8 χ := abs_fderiv_apply_le_cNorm8 hc hχ hv
  let U₀ := mulChi (measureH c) dχ hm hB W
  have hae : (U₀ : Profile → MeridC) =ᵐ[measureH c] u :=
    flatStressCutRep_ae_eq hc dχ hm hB W
  have hU0_norm : ‖U₀‖ ≤ cNorm8 χ * ‖W‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(memLp_chi_smul (measureH c) dχ hm hB (Lp.memLp W)).coeFn_toLp] with p hp
    change ‖((memLp_chi_smul (measureH c) dχ hm hB (Lp.memLp W)).toLp _) p‖ ≤ _
    rw [hp, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB p) (norm_nonneg _)
  have hstep2 : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) ≤
      ENNReal.ofReal ((cNorm8 χ * ‖W‖) ^ 2) := by
    have hcongr : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ∫⁻ p, ‖(U₀ : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [hp]
    have hLp : eLpNorm (U₀ : Profile → MeridC) 2 (measureH c) = ENNReal.ofReal ‖U₀‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top U₀)]
    have hlint : ∫⁻ p, ‖(U₀ : Profile → MeridC) p‖ₑ ^ (2 : ℝ) ∂(measureH c) =
        ENNReal.ofReal (‖U₀‖ ^ 2) := by
      have heq := eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := measureH c)
        (f := (U₀ : Profile → MeridC)) two_ne_zero ENNReal.ofNat_ne_top
      rw [hLp, ENNReal.toReal_ofNat] at heq
      have hpow := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) heq.symm
      rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg U₀) (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_two] at hpow
      exact hpow
    rw [hcongr, hlint]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg U₀) hU0_norm 2)
  have hlint_le : ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) ≤
      ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
    calc ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c)
        ≤ ENNReal.ofReal ((1 + H1) ^ 2) * ENNReal.ofReal ((cNorm8 χ * ‖W‖) ^ 2) :=
          hstep1.trans (by gcongr)
      _ = ENNReal.ofReal (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hmem := memLp_flatStressCutRep hc hσ hσH hdχ hm W
  have hint : Integrable (fun p => ‖u p‖ ^ 2) (cellMeasure c) :=
    hmem.integrable_norm_pow two_ne_zero
  have hofReal : ENNReal.ofReal (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) =
      ∫⁻ p, ‖u p‖ₑ ^ (2 : ℝ) ∂(cellMeasure c) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun p => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  have hB0 : 0 ≤ (1 + H1) * cNorm8 χ * ‖W‖ :=
    mul_nonneg (mul_nonneg (by linarith) (cNorm8_nonneg χ)) (norm_nonneg W)
  have hint_le : ∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c) ≤ ((1 + H1) * cNorm8 χ * ‖W‖) ^ 2 := by
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 ?_
    rw [hofReal]
    exact hlint_le
  unfold cellL2Norm
  calc (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ (((1 + H1) * cNorm8 χ * ‖W‖) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint_le (by norm_num)
    _ = (1 + H1) * cNorm8 χ * ‖W‖ := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hB0]

end N05_3_1Aux

open N05_3_1Aux


/-! ### 4. Leaf obligations and conditional assembly of `StressEpsHalfDriftDissipation` -/

/-- **Chart-pullback and cutoff-localisation leaf for age (`shiftS`) in `PartII-a:N05/3/1`
(`PhaseHalfDriftCutoffShiftS`, `PartII-a:N05/3/1/1`)**
(source `the November 2 reference manuscript`,
lines 1752–1756, 1769–1773): for any `W : HSpace c MeridC` whose phase lift
`U (B0223.liftVec hε hc hP W)` has half-drift `w_hd`
(`(FreeStress.phaseC0 P).HasPow (1 / 2) (U (liftVec W)) w_hd`, conjugating `|T - 3/4|^{1/2}` to
`|S - 1/4|^{1/2}`) and spatial gradient `g_diss` (`HasGrad (U (liftVec W)) g_diss`), the
box-supported `c`-periodic representative `flatStressCutRep c χ W` satisfies a `1/2`-Hölder
`L²(cellMeasure c)` translation bound in `shiftS` on `Icc (-1 : ℝ) 1` controlled by
`‖U (liftVec W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖`. -/
def PhaseHalfDriftCutoffShiftS : Prop :=
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
          ∫ p, ‖flatStressCutRep c χ W (shiftS h p) -
              flatStressCutRep c χ W p‖ ^ 2 ∂(cellMeasure c) ≤
            (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k *
              (‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 * |h|

/-- **Chart-pullback and cutoff-localisation leaf for transverse (`shiftEta`) in `PartII-a:N05/3/1`
(`PhaseDissipationCutoffShiftEta`, `PartII-a:N05/3/1/2`)**
(source `the November 2 reference manuscript`,
lines 1782–1785): for any `W : HSpace c MeridC` whose phase lift
`U (B0223.liftVec hε hc hP W)` has half-drift `w_hd` and spatial gradient `g_diss`
(`HasGrad (U (liftVec W)) g_diss`, lifting `(Q_ε W, ∂_η W, ε W_r)`), the box-supported
`c`-periodic representative `flatStressCutRep c χ W` satisfies a `1/2`-Hölder
`L²(cellMeasure c)` translation bound in `shiftEta` on `Icc (-1 : ℝ) 1` controlled by
`‖U (liftVec W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖`. -/
def PhaseDissipationCutoffShiftEta : Prop :=
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
          ∫ p, ‖flatStressCutRep c χ W (shiftEta h p) -
              flatStressCutRep c χ W p‖ ^ 2 ∂(cellMeasure c) ≤
            (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k *
              (‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 * |h|

/-- Combined `(shiftS, shiftEta)` chart-pullback and cutoff-localisation predicate for
`PartII-a:N05/3/1`. -/
def PhaseHalfDriftDissipationCutoffShiftSE : Prop :=
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
        (∀ h ∈ Icc (-1 : ℝ) 1,
          ∫ p, ‖flatStressCutRep c χ W (shiftS h p) -
              flatStressCutRep c χ W p‖ ^ 2 ∂(cellMeasure c) ≤
            (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k *
              (‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 * |h|) ∧
        (∀ h ∈ Icc (-1 : ℝ) 1,
          ∫ p, ‖flatStressCutRep c χ W (shiftEta h p) -
              flatStressCutRep c χ W p‖ ^ 2 ∂(cellMeasure c) ≤
            (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k *
              (‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 * |h|)

/-- Combines `PhaseHalfDriftCutoffShiftS` and `PhaseDissipationCutoffShiftEta` into
`PhaseHalfDriftDissipationCutoffShiftSE`. -/
theorem phaseHalfDriftDissipationCutoffShiftSE_of
    (hS : PhaseHalfDriftCutoffShiftS) (hEta : PhaseDissipationCutoffShiftEta) :
    PhaseHalfDriftDissipationCutoffShiftSE := by
  obtain ⟨k_S, C_S, hC_S, hLocS⟩ := hS
  obtain ⟨k_E, C_E, hC_E, hLocE⟩ := hEta
  refine ⟨max k_S k_E, max C_S C_E, le_max_of_le_left hC_S, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM0 hχ hχ1 hm B hB ε hε hε1 P _ hP hP1
    U hU W w_hd g_diss hw_hd hg_diss
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ Gam := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  set X := ‖U (B0223.liftVec hε hc hP W)‖ + ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖
  have hX0 : 0 ≤ X := by
    dsimp only [X]
    have : 0 ≤ ∑ j : Fin 3, ‖g_diss j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith [norm_nonneg (U (B0223.liftVec hε hc hP W)), norm_nonneg w_hd]
  constructor
  · intro h hh
    have h1 := hLocS ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM0 hχ hχ1 hm B hB
      ε hε hε1 P hP hP1 U hU W w_hd g_diss hw_hd hg_diss h hh
    have hle : C_S * Gam ^ k_S * X ≤ max C_S C_E * Gam ^ max k_S k_E * X := by
      apply mul_le_mul_of_nonneg_right _ hX0
      exact mul_le_mul (le_max_left C_S C_E)
        (pow_le_pow_right₀ hG1 (le_max_left k_S k_E)) (pow_nonneg hG0 k_S)
        (le_max_of_le_left hC_S)
    exact h1.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hle 2) (abs_nonneg h))
  · intro h hh
    have h2 := hLocE ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM0 hχ hχ1 hm B hB
      ε hε hε1 P hP hP1 U hU W w_hd g_diss hw_hd hg_diss h hh
    have hle : C_E * Gam ^ k_E * X ≤ max C_S C_E * Gam ^ max k_S k_E * X := by
      apply mul_le_mul_of_nonneg_right _ hX0
      exact mul_le_mul (le_max_right C_S C_E)
        (pow_le_pow_right₀ hG1 (le_max_right k_S k_E)) (pow_nonneg hG0 k_E)
        (le_max_of_le_left hC_S)
    exact h2.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hle 2) (abs_nonneg h))

/-- Conditional assembly of `StressEpsHalfDriftDissipation` from the combined predicate
`PhaseHalfDriftDissipationCutoffShiftSE`. -/
theorem stressEpsHalfDriftDissipation_of_combined (hLeaf : PhaseHalfDriftDissipationCutoffShiftSE) :
    StressEpsHalfDriftDissipation := by
  obtain ⟨C_SD, hC_SD, hSD⟩ := seps_smooth_phaseLift_bounds
  obtain ⟨k_L, C_L, hC_L, hLoc⟩ := hLeaf
  refine ⟨k_L + 3, 2 * C_L * C_SD, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB ε hε hε1 P _ hP hP1 μ hμM hμγ
    Seps hSeps F
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  obtain ⟨U, hU⟩ := N01.phaseLiftExists ε P hε
  set Gam := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ Gam := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ Gam := zero_le_one.trans hG1
  constructor
  · intro h hh
    have hK0 : 0 ≤ (C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * |h| :=
      mul_nonneg (sq_nonneg _) (abs_nonneg h)
    have hext := integral_shift_sub_sq_le_of_testSub_eps hν hε hc hP hσ hσH hχ hm hSeps
      (measurable_shiftS h) (fun f hf _ hsupp => lintegral_shiftS_le c h hf hsupp) hK0
      (fun M_test hM_test x G hx hG => by
        obtain ⟨w_hd, g_diss, hw_hd, hg_diss, hbd⟩ :=
          hSD ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P hP hP1 U hU μ hμM hμγ
            Seps hSeps M_test hM_test x G hx hG
        have hS_leaf := (hLoc ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM0 hχ hχ1 hm B hB
          ε hε hε1 P hP hP1 U hU (Teps hν hε hc hP μ G) w_hd g_diss hw_hd hg_diss).1 h hh
        have hsum_nonneg : 0 ≤ ‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ +
            ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ := by
          have : 0 ≤ ∑ j : Fin 3, ‖g_diss j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
          linarith [norm_nonneg (U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))),
            norm_nonneg w_hd]
        have hprod : C_L * Gam ^ k_L *
            (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
              ∑ j : Fin 3, ‖g_diss j‖) ≤
            C_L * C_SD * Gam ^ (k_L + 3) * ‖x‖ := by
          calc C_L * Gam ^ k_L *
                (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
                  ∑ j : Fin 3, ‖g_diss j‖)
              ≤ C_L * Gam ^ k_L * (C_SD * Gam ^ 3 * ‖x‖) :=
                mul_le_mul_of_nonneg_left hbd (mul_nonneg hC_L (pow_nonneg hG0 k_L))
            _ = C_L * C_SD * Gam ^ (k_L + 3) * ‖x‖ := by ring
        have hsq : (C_L * Gam ^ k_L *
            (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
              ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 ≤
            (C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * ‖x‖ ^ 2 := by
          calc (C_L * Gam ^ k_L *
                (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
                  ∑ j : Fin 3, ‖g_diss j‖)) ^ 2
              ≤ (C_L * C_SD * Gam ^ (k_L + 3) * ‖x‖) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hprod 2
            _ = (C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * ‖x‖ ^ 2 := by ring
        calc ∫ p, ‖flatStressCutRep c χ (Teps hν hε hc hP μ G) (shiftS h p) -
                flatStressCutRep c χ (Teps hν hε hc hP μ G) p‖ ^ 2 ∂(cellMeasure c)
            ≤ (C_L * Gam ^ k_L *
                (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
                  ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 * |h| := hS_leaf
          _ ≤ ((C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * ‖x‖ ^ 2) * |h| :=
              mul_le_mul_of_nonneg_right hsq (abs_nonneg h)
          _ = ((C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * |h|) * ‖x‖ ^ 2 := by ring)
      F
    calc ∫ p, ‖flatStressCutRep c χ (Seps F) (shiftS h p) -
            flatStressCutRep c χ (Seps F) p‖ ^ 2 ∂(cellMeasure c)
        ≤ 2 * (((C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * |h|) * ‖F‖ ^ 2) := hext
      _ ≤ (2 * C_L * C_SD * Gam ^ (k_L + 3) * ‖F‖) ^ 2 * |h| := by
          have : 0 ≤ ‖F‖ ^ 2 * |h| := mul_nonneg (sq_nonneg _) (abs_nonneg h)
          have : 0 ≤ (C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 := sq_nonneg _
          nlinarith
  · intro h hh
    have hK0 : 0 ≤ (C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * |h| :=
      mul_nonneg (sq_nonneg _) (abs_nonneg h)
    have hext := integral_shift_sub_sq_le_of_testSub_eps hν hε hc hP hσ hσH hχ hm hSeps
      (measurable_shiftEta h) (fun f hf _ _ => (lintegral_shiftEta_eq c h hf).le) hK0
      (fun M_test hM_test x G hx hG => by
        obtain ⟨w_hd, g_diss, hw_hd, hg_diss, hbd⟩ :=
          hSD ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P hP hP1 U hU μ hμM hμγ
            Seps hSeps M_test hM_test x G hx hG
        have hE_leaf := (hLoc ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM0 hχ hχ1 hm B hB
          ε hε hε1 P hP hP1 U hU (Teps hν hε hc hP μ G) w_hd g_diss hw_hd hg_diss).2 h hh
        have hsum_nonneg : 0 ≤ ‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ +
            ‖w_hd‖ + ∑ j : Fin 3, ‖g_diss j‖ := by
          have : 0 ≤ ∑ j : Fin 3, ‖g_diss j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
          linarith [norm_nonneg (U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))),
            norm_nonneg w_hd]
        have hprod : C_L * Gam ^ k_L *
            (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
              ∑ j : Fin 3, ‖g_diss j‖) ≤
            C_L * C_SD * Gam ^ (k_L + 3) * ‖x‖ := by
          calc C_L * Gam ^ k_L *
                (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
                  ∑ j : Fin 3, ‖g_diss j‖)
              ≤ C_L * Gam ^ k_L * (C_SD * Gam ^ 3 * ‖x‖) :=
                mul_le_mul_of_nonneg_left hbd (mul_nonneg hC_L (pow_nonneg hG0 k_L))
            _ = C_L * C_SD * Gam ^ (k_L + 3) * ‖x‖ := by ring
        have hsq : (C_L * Gam ^ k_L *
            (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
              ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 ≤
            (C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * ‖x‖ ^ 2 := by
          calc (C_L * Gam ^ k_L *
                (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
                  ∑ j : Fin 3, ‖g_diss j‖)) ^ 2
              ≤ (C_L * C_SD * Gam ^ (k_L + 3) * ‖x‖) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hprod 2
            _ = (C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * ‖x‖ ^ 2 := by ring
        calc ∫ p, ‖flatStressCutRep c χ (Teps hν hε hc hP μ G) (shiftEta h p) -
                flatStressCutRep c χ (Teps hν hε hc hP μ G) p‖ ^ 2 ∂(cellMeasure c)
            ≤ (C_L * Gam ^ k_L *
                (‖U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))‖ + ‖w_hd‖ +
                  ∑ j : Fin 3, ‖g_diss j‖)) ^ 2 * |h| := hE_leaf
          _ ≤ ((C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * ‖x‖ ^ 2) * |h| :=
              mul_le_mul_of_nonneg_right hsq (abs_nonneg h)
          _ = ((C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * |h|) * ‖x‖ ^ 2 := by ring)
      F
    calc ∫ p, ‖flatStressCutRep c χ (Seps F) (shiftEta h p) -
            flatStressCutRep c χ (Seps F) p‖ ^ 2 ∂(cellMeasure c)
        ≤ 2 * (((C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 * |h|) * ‖F‖ ^ 2) := hext
      _ ≤ (2 * C_L * C_SD * Gam ^ (k_L + 3) * ‖F‖) ^ 2 * |h| := by
          have : 0 ≤ ‖F‖ ^ 2 * |h| := mul_nonneg (sq_nonneg _) (abs_nonneg h)
          have : 0 ≤ (C_L * C_SD * Gam ^ (k_L + 3)) ^ 2 := sq_nonneg _
          nlinarith

/-- **Conditional assembly of `StressEpsHalfDriftDissipation` (`PartII-a:N05/3/1`)** from the two
chart-pullback and cutoff-localisation leaves `PhaseHalfDriftCutoffShiftS` (`PartII-a:N05/3/1/1`)
and `PhaseDissipationCutoffShiftEta` (`PartII-a:N05/3/1/2`). -/
theorem stressEpsHalfDriftDissipation_of
    (hS : PhaseHalfDriftCutoffShiftS) (hEta : PhaseDissipationCutoffShiftEta) :
    StressEpsHalfDriftDissipation :=
  stressEpsHalfDriftDissipation_of_combined (phaseHalfDriftDissipationCutoffShiftSE_of hS hEta)

end UnforcedLeray.Short.PartIIa
