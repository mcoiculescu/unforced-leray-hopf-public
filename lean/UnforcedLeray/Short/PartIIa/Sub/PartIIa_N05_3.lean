import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4
import UnforcedLeray.Short.PartIIa.Tasks.F16HalfDrift
import UnforcedLeray.Short.PartIIa.Tasks.N01StressMaps

/-!
# `Sub/PartII-a_N05_3`: Decomposition of `StressEpsLocalH14` (`PartII-a:N05/3`)

Source of record: `the November 2 reference manuscript`,
lines 1752–1756, 1765–1788 (`near:local-smoothing`, `ε > 0` stress case).

## Structure of this file

1. **Unconditional smooth-test and operator bounds for `Seps F`** (`N05_3Aux.epsSmoothBound`,
   `N05_3Aux.stressMap_eps_norm_le`, `N05_3Aux.cellL2Norm_flatStressCutRep_seps_le_gamma`):
   combines `N01.epsSmoothBound_of` (`Sub/N01/Reduction.lean`), the accepted `N01` leaf theorems
   (`Tasks/N01StressMaps.lean`), and density of smooth tensor tests (`N01.testSub_dense`) to prove
   `‖Seps F‖ ≤ 2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖` and hence
   `cellL2Norm c (flatStressCutRep c χ (Seps F)) ≤ 2 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖F‖`.
2. **Unconditional half-drift and dissipation bounds for `Seps F` on smooth tensor tests**
   (`seps_real_halfDrift`, `seps_smooth_halfDrift`, `seps_smooth_dissipation`):
   combines `weakStressHalfDrift` (`Tasks/F16HalfDrift.lean`), `weakStressExists`
   (`Tasks/F14WeakStressExists.lean`), `N01.phaseLift_liftVec_Teps`, `N01.cartLiftNorm`,
   `N01.tensorTestReIm`, `dissipationBound` (`Sub/PartII-a_N05.lean`), and `IsStressMap` to prove
   that for every smooth tensor test `M` (`IsTensorTest c M`) represented by `F : HTSpace c` and
   `G : HSpace c MeridC`, the phase lift `U (B0223.liftVec hε hc hP (Seps F))` belongs to the
   domain of `(FreeStress.phaseC0 P).HasPow (1 / 2)` (`|T - 3/4|^{1/2}`, which conjugates to
   `|S - 1/4|^{1/2}`) with norm `≤ 4 * C_K * ν^{-1/2} * ‖F‖`, and has spatial gradient
   `g : Fin 3 → Yq P 2` (`HasGrad`, lifting `(Q_ε, ∂_η, ε ·_r)`) with
   `∑ j, ‖g j‖ ≤ C_D * Gamma ν c σ H1 L1 M_bound γs χ χ1 * ‖F‖`.
3. **Directional `1/2`-Hölder combination** (`hasCellH14_of_split_holderHalf`):
   combines separate `(shiftS, shiftEta)` and `shiftQ` `1/2`-Hölder `L²(cellMeasure c)` translation
   bounds with `hasCellH14_of_holderHalf` (`Sub/PartII-a_N05.lean`).
4. **Two leaf obligations on `flatStressCutRep c χ (Seps F)` and conditional assembly
   (`stressEpsLocalH14_of`)**:
   * `StressEpsHalfDriftDissipation` (`PartII-a:N05/3/1`): age (`shiftS`) and transverse
     (`shiftEta`) `1/2`-Hölder `L²(cellMeasure c)` translation bounds on
     `flatStressCutRep c χ (Seps F)` from `seps_smooth_halfDrift`, `seps_smooth_dissipation`, and
     smooth tensor density (source lines 1752–1756, 1769–1773, 1782–1785);
   * `StressEpsCommutingFlowShiftQ` (`PartII-a:N05/3/2`): azimuthal (`shiftQ`) `1/2`-Hölder
     `L²(cellMeasure c)` translation bound on `flatStressCutRep c χ (Seps F)` from the commuting
     flow identity for `Q̃_ε = ∂_q - 2ε ∂_x - ε (η ∂_η + 1/2)` in log age `x = log s` (source lines
     1765–1781);
   assembled via `hasCellH14_of_holderHalf` (`Sub/PartII-a_N05.lean`) and composed in
   `PartII-a:N05/3`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete (Chart Ten3)
open UnforcedLeray.Short.PartIIIb.NearInst (tv4 cartLift)

namespace N05_3Aux

/-! ### 1. `Gamma` dominance and `L²(cellMeasure c)` bound on `flatStressCutRep c χ (Seps F)` -/

theorem one_le_gamma_stress {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) : 1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < σ⁻¹ := inv_pos.2 hσ
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]

theorem inv_nu_le_gamma_stress {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) : ν⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < σ⁻¹ := inv_pos.2 hσ
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]

/-- Unconditional `N01.EpsSmoothBound` assembled from the accepted `N01` leaf theorems. -/
theorem epsSmoothBound : N01.EpsSmoothBound :=
  N01.epsSmoothBound_of N01.phaseLiftExists N01.phaseSemigroupConj N01.phaseLerayConj
    N01.phaseDivScale N01.cartLiftRows N01.cartLiftNorm N01.tensorTestReIm

/-- Unconditional `H`-norm bound on any stress map `Seps` of `Teps hν hε hc hP μ` by density of
`N01.testSub c`. -/
theorem stressMap_eps_norm_le {ν ε c P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε)
    (hc : 0 < c) (hP : P = 2 * ε * c) (hP1 : P ≤ 1) {μ : ℂ} (hγ : 0 < μ.re + 1 / 4)
    {Seps : HTSpace c →L[ℂ] HSpace c MeridC}
    (hSeps : IsStressMap c ε (Teps hν hε hc hP μ) Seps) (F : HTSpace c) :
    ‖Seps F‖ ≤ 2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by
  refine isClosed_property (N01.testSub_dense c hc)
    (isClosed_le Seps.continuous.norm (continuous_const.mul continuous_norm)) (fun x => ?_) F
  obtain ⟨M, hM, hFM⟩ := x.2
  let G : HSpace c MeridC :=
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc M hM).toLp _
  have hG : (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) :=
    MemLp.coeFn_toLp _
  show ‖Seps (x : HTSpace c)‖ ≤ 2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖(x : HTSpace c)‖
  rw [hSeps M hM x.1 G hFM hG]
  exact epsSmoothBound ν ε c P hν hε hc hP hP1 μ hγ M hM x.1 G hFM hG

/-- Unconditional `2 * Gamma^3` bound on `cellL2Norm c (flatStressCutRep c χ (Seps F))`. -/
theorem cellL2Norm_flatStressCutRep_seps_le_gamma {ν c σ H1 L1 M γs ε P : ℝ} [Fact (0 < P)]
    (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    (hL1 : 0 ≤ L1) (hγ : 0 < γs) (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    (hε : 0 < ε) (hP : P = 2 * ε * c) (hP1 : P ≤ 1) {μ : ℂ} (hμM : ‖μ‖ ≤ M)
    (hμγ : γs ≤ μ.re + 1 / 4) {Seps : HTSpace c →L[ℂ] HSpace c MeridC}
    (hSeps : IsStressMap c ε (Teps hν hε hc hP μ) Seps) (F : HTSpace c) :
    cellL2Norm c (flatStressCutRep c χ (Seps F)) ≤
      2 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖F‖ := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hνi : 0 < ν⁻¹ := inv_pos.2 hν
  have hci : 0 < c⁻¹ := inv_pos.2 hc
  have hσi : 0 < σ⁻¹ := inv_pos.2 hσ
  have hγi : 0 < γs⁻¹ := inv_pos.2 hγ
  have hG0 : 0 ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have h1H1_G : 1 + H1 ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hcN_G : cNorm8 χ ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγ_G : γs⁻¹ ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hν_G : ν⁻¹ ≤ G := by
    unfold G Gamma GammaBox
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hsqrt_le : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ G := by
    have h1 : (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (Real.sqrt (γs * ν))⁻¹ := by
      refine inv_anti₀ (Real.sqrt_pos.2 (mul_pos hγ hν)) (Real.sqrt_le_sqrt ?_)
      exact mul_le_mul_of_nonneg_right hμγ hν.le
    have h2 : ((Real.sqrt (γs * ν))⁻¹) ^ 2 ≤ G ^ 2 := by
      rw [inv_pow, Real.sq_sqrt (mul_pos hγ hν).le, mul_inv, sq]
      exact mul_le_mul hγ_G hν_G hνi.le hG0
    have h3 : (Real.sqrt (γs * ν))⁻¹ ≤ G :=
      (abs_le_of_sq_le_sq' h2 hG0).2
    exact h1.trans h3
  have hSepsF := stressMap_eps_norm_le hν hε hc hP hP1 (lt_of_lt_of_le hγ hμγ) hSeps F
  have hL2 := N05_4Aux.cellL2Norm_flatStressCutRep_le_mul hc hσ hσH hχ hm (Seps F)
  have hH1_pos : 0 < H1 := lt_of_lt_of_le hσ hσH
  calc cellL2Norm c (flatStressCutRep c χ (Seps F))
      ≤ (1 + H1) * cNorm8 χ * ‖Seps F‖ := hL2
    _ ≤ (1 + H1) * cNorm8 χ * (2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) :=
        mul_le_mul_of_nonneg_left hSepsF (mul_nonneg (by linarith) (cNorm8_nonneg χ))
    _ = 2 * ((1 + H1) * cNorm8 χ * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹) * ‖F‖ := by ring
    _ ≤ 2 * (G * G * G) * ‖F‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (norm_nonneg F)
        refine mul_le_mul (mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0) hsqrt_le
          (by positivity) (mul_nonneg hG0 hG0)
    _ = 2 * G ^ 3 * ‖F‖ := by ring

end N05_3Aux

open N05_3Aux

/-! ### 2. Half-drift (`(FreeStress.phaseC0 P).HasPow (1/2)`) and dissipation bounds on smooth tests -/

/-- Real-test half-drift bound: for a real smooth tensor test `m` with `F =ᵐ tv4 ∘ m` and
`G =ᵐ s • divEps ε (tv4 ∘ m)`, the phase lift of `Teps G` belongs to the domain of
`(FreeStress.phaseC0 P).HasPow (1 / 2)` (`(1 + |T - 3/4|)^{1/2}`, conjugate to
`(1 + |S - 1/4|)^{1/2}`) with norm bounded by `2 * C_K * ν^{-1/2} * ‖F‖`. -/
theorem seps_real_halfDrift {K : Set ℂ} {C_K : ℝ} (hC_K : 0 ≤ C_K)
    (hHD : ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ ∈ K,
      ∀ S : symY2 P →L[ℂ] Yq P 2, IsWeakStressInverse P ν μ S → ∀ T : symY2 P,
        ∃ w : Yq P 2, (FreeStress.phaseC0 P).HasPow (1 / 2) (S T) w ∧
          ‖w‖ ≤ C_K * ν ^ (-(1 / 2 : ℝ)) * ‖(T : Y2Sym P)‖)
    {ν ε c P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (hP1 : P ≤ 1) {μ : ℂ} (hμK : μ ∈ K) (hγ : 0 < μ.re + 1 / 4)
    {U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2} (hU : N01.IsPhaseLift ε P U)
    (m : Chart → Ten3) (hm : IsTensorTest c (fun p => tv4 (m p)))
    (F : HTSpace c) (hF : (F : Profile → TensorVal) =ᵐ[measureHT c] (fun p => tv4 (m p)))
    (G : HSpace c MeridC)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c]
      (fun p => (p.1 : ℂ) • divEps ε (fun q => tv4 (m q)) p)) :
    ∃ w : Yq P 2,
      (FreeStress.phaseC0 P).HasPow (1 / 2)
        (U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))) w ∧
      ‖w‖ ≤ 2 * C_K * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ := by
  obtain ⟨S, hSw, -⟩ := weakStressExists P hP1 ν hν μ hγ
  obtain ⟨X, hX, hEq⟩ :=
    N01.phaseLift_liftVec_Teps N01.phaseSemigroupConj N01.phaseLerayConj N01.phaseDivScale
      N01.cartLiftRows hν hε hc hP hP1 hγ hU S hSw m hm G hG
  obtain ⟨w_X, hw_pow, hw_bd⟩ := hHD P hP1 ν hν μ hμK S hSw X
  set κ : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε)
  have hκ0 : 0 ≤ κ := by dsimp [κ]; positivity
  have hpos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  refine ⟨((κ : ℝ) : ℂ) • w_X, ?_, ?_⟩
  · rw [hEq]
    exact hw_pow.smul ((κ : ℝ) : ℂ)
  · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hκ0]
    have hXn : κ * ‖(X : Y2Sym P)‖ ≤ Real.sqrt 2 * ‖F‖ := by
      have h1 := N01.cartLiftNorm ε c P hε hc hP m hm F hF
      rw [← hX] at h1
      calc κ * ‖(X : Y2Sym P)‖
          = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (P * ε) * ‖(X : Y2Sym P)‖) := by
            dsimp [κ]; ring
        _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi) * Real.sqrt 2 * ‖F‖) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpos.le)
        _ = Real.sqrt 2 * ‖F‖ := by field_simp
    have hs2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hXn' : κ * ‖(X : Y2Sym P)‖ ≤ 2 * ‖F‖ :=
      hXn.trans (mul_le_mul_of_nonneg_right hs2 (norm_nonneg F))
    have hν0 : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
    calc κ * ‖w_X‖ ≤ κ * (C_K * ν ^ (-(1 / 2 : ℝ)) * ‖(X : Y2Sym P)‖) :=
          mul_le_mul_of_nonneg_left hw_bd hκ0
      _ = C_K * ν ^ (-(1 / 2 : ℝ)) * (κ * ‖(X : Y2Sym P)‖) := by ring
      _ ≤ C_K * ν ^ (-(1 / 2 : ℝ)) * (2 * ‖F‖) :=
          mul_le_mul_of_nonneg_left hXn' (mul_nonneg hC_K hν0)
      _ = 2 * C_K * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ := by ring

/-- Complex smooth tensor test half-drift bound for `Seps F` (source lines 1752–1756), derived
from `weakStressHalfDrift` (`Tasks/F16HalfDrift.lean`) and `IsStressMap`. -/
theorem seps_smooth_halfDrift (K : Set ℂ) (hK : IsCompact K) (hKpos : ∀ μ ∈ K, 0 < μ.re + 1 / 4) :
    ∃ C_K : ℝ, 0 ≤ C_K ∧
      ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c)
        (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ μ ∈ K,
      ∀ (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2), N01.IsPhaseLift ε P U →
      ∀ Seps : HTSpace c →L[ℂ] HSpace c MeridC,
        IsStressMap c ε (Teps hν hε hc hP μ) Seps →
      ∀ (M : Profile → TensorVal), IsTensorTest c M →
      ∀ (F : HTSpace c) (G : HSpace c MeridC),
        (F : Profile → TensorVal) =ᵐ[measureHT c] M →
        (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
        ∃ w : Yq P 2,
          (FreeStress.phaseC0 P).HasPow (1 / 2)
            (U (B0223.liftVec hε hc hP (Seps F))) w ∧
          ‖w‖ ≤ C_K * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ := by
  obtain ⟨C₀, hC₀, hHD⟩ := weakStressHalfDrift K hK hKpos
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro ν ε c P _ hν hε hc hP hP1 μ hμK U hU Seps hSeps M hM F G hF hG
  have hγ : 0 < μ.re + 1 / 4 := hKpos μ hμK
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
    seps_real_halfDrift hC₀ hHD hν hε hc hP hP1 hμK hγ hU m₁ hm₁ F₁ hL₁.coeFn_toLp
      G₁ hG₁L.coeFn_toLp
  obtain ⟨w₂, hw₂, hb₂⟩ :=
    seps_real_halfDrift hC₀ hHD hν hε hc hP hP1 hμK hγ hU m₂ hm₂ F₂ hL₂.coeFn_toLp
      G₂ hG₂L.coeFn_toLp
  rw [hGsplit, map_add, map_smul, map_add, map_smul, map_add, map_smul]
  refine ⟨w₁ + Complex.I • w₂, hw₁.add (hw₂.smul Complex.I), ?_⟩
  have hν0 : 0 ≤ ν ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hν.le _
  have hb₁' : ‖w₁‖ ≤ 2 * C₀ * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ :=
    hb₁.trans (mul_le_mul_of_nonneg_left hF₁n (by positivity))
  have hb₂' : ‖w₂‖ ≤ 2 * C₀ * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ :=
    hb₂.trans (mul_le_mul_of_nonneg_left hF₂n (by positivity))
  calc ‖w₁ + Complex.I • w₂‖ ≤ ‖w₁‖ + ‖Complex.I • w₂‖ := norm_add_le _ _
    _ = ‖w₁‖ + ‖w₂‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ 2 * C₀ * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ + 2 * C₀ * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ :=
        add_le_add hb₁' hb₂'
    _ = 4 * C₀ * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ := by ring

/-- Dissipation gradient bound for `Seps F` on smooth tensor tests `M`, derived from
`dissipationBound` (`Sub/PartII-a_N05.lean`) and `IsStressMap`. -/
theorem seps_smooth_dissipation :
    ∃ C_D : ℝ, 0 ≤ C_D ∧
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
          ∃ g : Fin 3 → Yq P 2,
            HasGrad (U (B0223.liftVec hε hc hP (Seps F))) g ∧
            ∑ j : Fin 3, ‖g j‖ ≤ C_D * Gamma ν c σ H1 L1 M_bound γs χ χ1 * ‖F‖ := by
  obtain ⟨C_D, hC_D, hDiss⟩ := dissipationBound
  refine ⟨C_D, hC_D, ?_⟩
  intro ν c σ H1 L1 M_bound γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P _ hP hP1 U hU μ hμM hμγ
    Seps hSeps M hM F G hF hG
  have hM0 : 0 ≤ M_bound := (norm_nonneg μ).trans hμM
  have hμ : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγ hμγ
  have hSeps_eq : Seps F = Teps hν hε hc hP μ G := hSeps M hM F G hF hG
  obtain ⟨g, hg, hgb⟩ := hDiss ν ε c P hν hε hc hP hP1 μ hμ U hU M hM F G hF hG
  refine ⟨g, by rwa [hSeps_eq], ?_⟩
  have hinvG : ν⁻¹ ≤ Gamma ν c σ H1 L1 M_bound γs χ χ1 :=
    inv_nu_le_gamma_stress χ χ1 hν hc hσ hσH hL1 hγ hM0
  calc ∑ j : Fin 3, ‖g j‖ ≤ C_D * ν⁻¹ * ‖F‖ := hgb
    _ ≤ C_D * Gamma ν c σ H1 L1 M_bound γs χ χ1 * ‖F‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinvG hC_D) (norm_nonneg F)

/-! ### 3. Combining directional `1/2`-Hölder bounds into `HasCellH14` -/

/-- Combines a `1/2`-Hölder `L²(cellMeasure c)` translation bound in `(shiftS, shiftEta)` with
constant `A₁` and a `1/2`-Hölder `L²(cellMeasure c)` translation bound in `shiftQ` with constant
`A₂` into `HasCellH14` and `cellH14Norm c u ≤ 7 * (A₁ + A₂)`. -/
theorem hasCellH14_of_split_holderHalf {c σ H1 L1 A₁ A₂ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (U : HSpace c MeridC) (u : Profile → MeridC)
    (hae : (U : Profile → MeridC) =ᵐ[measureH c] u)
    (hper : QPeriodic c u)
    (hsupp : ∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hmem : MemLp u 2 (cellMeasure c))
    (hL2 : cellL2Norm c u ≤ A₁)
    (hms : AEStronglyMeasurable
      (fun h : ℝ => ∫ p, ‖u (shiftS h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)))
    (hme : AEStronglyMeasurable
      (fun h : ℝ => ∫ p, ‖u (shiftEta h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)))
    (hmq : AEStronglyMeasurable
      (fun h : ℝ => ∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c))
      (volume.restrict (Icc (-1 : ℝ) 1)))
    (hhs : ∀ h ∈ Icc (-1 : ℝ) 1,
      ∫ p, ‖u (shiftS h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ A₁ ^ 2 * |h|)
    (hhe : ∀ h ∈ Icc (-1 : ℝ) 1,
      ∫ p, ‖u (shiftEta h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ A₁ ^ 2 * |h|)
    (hhq : ∀ h ∈ Icc (-1 : ℝ) 1,
      ∫ p, ‖u (shiftQ h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤ A₂ ^ 2 * |h|) :
    HasCellH14 c σ H1 L1 U u ∧ cellH14Norm c u ≤ 7 * (A₁ + A₂) := by
  have hA : 0 ≤ A₁ + A₂ := add_nonneg hA₁ hA₂
  have hA₁_sq : A₁ ^ 2 ≤ (A₁ + A₂) ^ 2 := by nlinarith
  have hA₂_sq : A₂ ^ 2 ≤ (A₁ + A₂) ^ 2 := by nlinarith
  refine hasCellH14_of_holderHalf hA U u hae hper hsupp hmem (by linarith) hms hmq hme
    (fun h hh => (hhs h hh).trans (mul_le_mul_of_nonneg_right hA₁_sq (abs_nonneg h)))
    (fun h hh => (hhq h hh).trans (mul_le_mul_of_nonneg_right hA₂_sq (abs_nonneg h)))
    (fun h hh => (hhe h hh).trans (mul_le_mul_of_nonneg_right hA₁_sq (abs_nonneg h)))

/-! ### 4. Leaf obligations for `StressEpsLocalH14` -/

/-- **Leaf 1 (`PartII-a:N05/3/1`) — age (`shiftS`) and transverse (`shiftEta`) `1/2`-Hölder
`L²(cellMeasure c)` translation bounds for `χ S_ε F` from half-drift and dissipation**
(source `the November 2 reference manuscript`,
lines 1752–1756, 1769–1773, 1782–1785): combining `seps_smooth_halfDrift`
(`‖|S - 1/4|^{1/2} Seps M‖_H ≤ C ν^{-1/2} ‖M‖_{H_T}` via unitary conjugation of `T - 3/4` to
`S - 1/4`), `seps_smooth_dissipation` (`‖∂_η Seps M‖_H ≤ C ν⁻¹ ‖M‖_{H_T}`), and smooth tensor
density (`IsStressMap`, `N01.testSub_dense`), for every `F : HTSpace c` the concrete box-supported
`c`-periodic representative `flatStressCutRep c χ (Seps F)` satisfies `1/2`-Hölder `L²`
translation bounds in age (`shiftS`) and transverse (`shiftEta`) directions on `Icc (-1 : ℝ) 1`. -/
def StressEpsHalfDriftDissipation : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (_hm : Measurable χ) (B : ℝ) (_hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
          ∀ Seps : HTSpace c →L[ℂ] HSpace c MeridC,
            IsStressMap c ε (Teps hν hε hc hP μ) Seps →
            ∀ F : HTSpace c,
              (∀ h ∈ Icc (-1 : ℝ) 1,
                ∫ p, ‖flatStressCutRep c χ (Seps F) (shiftS h p) -
                    flatStressCutRep c χ (Seps F) p‖ ^ 2 ∂(cellMeasure c) ≤
                  (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖) ^ 2 * |h|) ∧
              (∀ h ∈ Icc (-1 : ℝ) 1,
                ∫ p, ‖flatStressCutRep c χ (Seps F) (shiftEta h p) -
                    flatStressCutRep c χ (Seps F) p‖ ^ 2 ∂(cellMeasure c) ≤
                  (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖) ^ 2 * |h|)

/-- **Leaf 2 (`PartII-a:N05/3/2`) — azimuthal `shiftQ` `1/2`-Hölder `L²(cellMeasure c)` translation
bound for `χ S_ε F` via the commuting flow identity**
(source `the November 2 reference manuscript`,
lines 1765–1781): in log age `x = log s`, the conjugate of `Q_ε` shifted by `ε` is
`Q̃_ε = ∂_q - 2ε ∂_x - ε (η ∂_η + 1/2)`, whose three constituent flows commute; for a compactly
supported cutoff `f` of `e^{-x/4} b(e^x)`, the unitary flow identity
`‖f(q+h) - f(q)‖_2 ≤ |h| ‖Q̃_ε f‖_2 + C |ε h|^{1/2} ‖|∂_x|^{1/2} f‖_2 + |ε h| ‖(η ∂_η + 1/2) f‖_2`
combined with `seps_smooth_halfDrift` and `seps_smooth_dissipation` gives the `1/2`-Hölder
`L²(cellMeasure c)` translation bound in `shiftQ` on `Icc (-1 : ℝ) 1` for
`flatStressCutRep c χ (Seps F)`. -/
def StressEpsCommutingFlowShiftQ : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (_hm : Measurable χ) (B : ℝ) (_hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
          ∀ Seps : HTSpace c →L[ℂ] HSpace c MeridC,
            IsStressMap c ε (Teps hν hε hc hP μ) Seps →
            ∀ F : HTSpace c,
              ∀ h ∈ Icc (-1 : ℝ) 1,
                ∫ p, ‖flatStressCutRep c χ (Seps F) (shiftQ h p) -
                    flatStressCutRep c χ (Seps F) p‖ ^ 2 ∂(cellMeasure c) ≤
                  (C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k * ‖F‖) ^ 2 * |h|

/-! ### 5. Conditional assembly of `StressEpsLocalH14` -/

/-- **Conditional assembly of `StressEpsLocalH14` (`PartII-a:N05/3`)** from
`StressEpsHalfDriftDissipation` and `StressEpsCommutingFlowShiftQ` via
`hasCellH14_of_holderHalf` (`Sub/PartII-a_N05.lean`). -/
theorem stressEpsLocalH14_of (hSE : StressEpsHalfDriftDissipation)
    (hQ : StressEpsCommutingFlowShiftQ) : StressEpsLocalH14 := by
  obtain ⟨k₁, C₁, hC₁, h1⟩ := hSE
  obtain ⟨k₂, C₂, hC₂, h2⟩ := hQ
  let K := max 3 (max k₁ k₂)
  refine ⟨K, 7 * (2 + C₁ + C₂), by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB ε hε hε1 P _ hP hP1 μ hμM hμγ
    Seps hSeps F
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma_stress χ χ1 hν hc hσ hσH hL1 hγ hM0
  set A : ℝ := (2 + C₁ + C₂) * G ^ K * ‖F‖
  have hA0 : 0 ≤ A := by positivity
  have hA0_le : 2 * G ^ 3 * ‖F‖ ≤ A := by
    have hk : G ^ 3 ≤ G ^ K := pow_le_pow_right₀ hG1 (le_max_left 3 (max k₁ k₂))
    have hC : (2 : ℝ) ≤ 2 + C₁ + C₂ := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hC hk (pow_nonneg (zero_le_one.trans hG1) _) (by positivity))
      (norm_nonneg F)
  have hA1 : C₁ * G ^ k₁ * ‖F‖ ≤ A := by
    have hk : G ^ k₁ ≤ G ^ K :=
      pow_le_pow_right₀ hG1 ((le_max_left k₁ k₂).trans (le_max_right 3 (max k₁ k₂)))
    have hC : C₁ ≤ 2 + C₁ + C₂ := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hC hk (pow_nonneg (zero_le_one.trans hG1) _) (by positivity))
      (norm_nonneg F)
  have hA2 : C₂ * G ^ k₂ * ‖F‖ ≤ A := by
    have hk : G ^ k₂ ≤ G ^ K :=
      pow_le_pow_right₀ hG1 ((le_max_right k₁ k₂).trans (le_max_right 3 (max k₁ k₂)))
    have hC : C₂ ≤ 2 + C₁ + C₂ := by linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hC hk (pow_nonneg (zero_le_one.trans hG1) _) (by positivity))
      (norm_nonneg F)
  obtain ⟨hhs, hhe⟩ :=
    h1 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB ε hε hε1 P hP hP1 μ hμM hμγ
      Seps hSeps F
  have hhq :=
    h2 ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB ε hε hε1 P hP hP1 μ hμM hμγ
      Seps hSeps F
  let u := flatStressCutRep c χ (Seps F)
  have hu_meas : Measurable u := N05_4Aux.measurable_flatStressCutRep c hm (Seps F)
  have hmem : MemLp u 2 (cellMeasure c) := N05_4Aux.memLp_flatStressCutRep hc hσ hσH hχ hm (Seps F)
  have hL2 : cellL2Norm c u ≤ A :=
    (cellL2Norm_flatStressCutRep_seps_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hχ hm hε hP hP1 hμM hμγ
      hSeps F).trans hA0_le
  have hA1_sq : (C₁ * G ^ k₁ * ‖F‖) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA1 2
  have hA2_sq : (C₂ * G ^ k₂ * ‖F‖) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA2 2
  have hcomb := hasCellH14_of_holderHalf hA0 (mulChi (measureH c) χ hm hB (Seps F)) u
    (N05_4Aux.flatStressCutRep_ae_eq hc χ hm hB (Seps F))
    (N05_4Aux.flatStressCutRep_periodic hc hχ (Seps F))
    (N05_4Aux.flatStressCutRep_support hχ (Seps F))
    hmem
    hL2
    (N05_4Aux.aestronglyMeasurable_diff_integral c N05_4Aux.measurable_shiftS_uncurry hu_meas)
    (N05_4Aux.aestronglyMeasurable_diff_integral c N05_4Aux.measurable_shiftQ_uncurry hu_meas)
    (N05_4Aux.aestronglyMeasurable_diff_integral c N05_4Aux.measurable_shiftEta_uncurry hu_meas)
    (fun h hh => (hhs h hh).trans (mul_le_mul_of_nonneg_right hA1_sq (abs_nonneg h)))
    (fun h hh => (hhq h hh).trans (mul_le_mul_of_nonneg_right hA2_sq (abs_nonneg h)))
    (fun h hh => (hhe h hh).trans (mul_le_mul_of_nonneg_right hA1_sq (abs_nonneg h)))
  refine ⟨u, hcomb.1, ?_⟩
  calc cellH14Norm c u
      ≤ 7 * A := hcomb.2
    _ = 7 * (2 + C₁ + C₂) * G ^ K * ‖F‖ := by
      simp only [A]
      ring

end UnforcedLeray.Short.PartIIa
