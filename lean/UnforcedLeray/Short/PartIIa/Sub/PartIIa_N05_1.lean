import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N05_4
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.Sub.N01.Reduction

/-!
# `Sub/PartII-a_N05_1`: Decomposition of `BodyEpsLocalH1` (`PartII-a:N05/1`)

Source of record: `the November 2 reference manuscript`,
lines 1789-1793.

## Structure of this file

1. **Resolvent lift and maximal-domain graph bound (`N05_1Aux.teps_lift_mem_D2_and_graphBound`)**:
   Under the unitary phase lift `U ∘ B0223.liftVec` (`N01.phaseLiftExists`, `N01.phaseSemigroupConj`),
   `Teps hν hε hc hP μ b = RepsVec hν hε hc hP μ (PepsC ε c b)` lifts via `B0223.J_RepsVec` and
   `N01.phaseLift_physRes` to the maximal-domain body resolvent `v ∈ B0411.D P ν 2` solving
   `bodyOp P ν 2 μ v = U (B0223.liftVec hε hc hP (PepsC ε c b))` (`N01.bodyResolvent_bodyOp`).
   Applying `commonBodyGraphBound` (`Tasks/F06GraphBound.lean`) at `r = 2` controls `‖v‖_{Y_2}`,
   the drift `‖T0D v‖_{Y_2}`, and the spatial gradient `∑ j, ‖grad_v j‖_{Y_2}` by
   `C * Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖b‖`.
2. **Unconditional `flatStressCutRep` properties and `cellL2Norm` bound (`N05_1Aux.cellL2Norm_flatStressCutRep_lift_le`)**:
   For any `w : HSpace c MeridC` with `(v : Yq P 2) = U (B0223.liftVec hε hc hP w)`, the box-supported
   `c`-periodic representative `flatStressCutRep c χ w` satisfies `‖w‖ = ‖(v : Yq P 2)‖` and
   `cellL2Norm c (flatStressCutRep c χ w) ≤ Gamma ν c σ H1 L1 M γs χ χ1 ^ 2 * ‖(v : Yq P 2)‖`.
3. **Coordinate-derivative conversion on the observation box (`hasWeakCellH1_of_hasLocalSQE`,
   `cellH1Norm_of_hasLocalSQE_le`)**:
   Using `dsFromS` (`∂_s = s⁻¹ S`), `dqFromSQE` (`∂_q = Q_ε + ε (2 S + η ∂_η + 1)`),
   `norm_dsFromS_le`, and `norm_dqFromSQE_le` from `Sub/PartII-a_N05.lean`, any box-supported
   `(1, S, Q_ε, ∂_η)` representation `(u, Su, Qu, Eu)` on `cellMeasure c` (`HasLocalSQE`)
   automatically satisfies `HasWeakCellH1 c σ H1 L1 U u (dsFromS Su) (dqFromSQE ε u Su Qu Eu) Eu`
   with `cellH1Norm ≤ 3 * Gamma * (cellL2Norm c u + cellL2Norm c Su + cellL2Norm c Qu + cellL2Norm c Eu)`.
4. **Conditional assembly (`bodyEpsLocalH1_of`)**:
   Combines (1), (2), and (3) with the chart-pullback / cutoff localisation leaf `PhaseD2CutoffSQE`
   (`PartII-a:N05/1/1`, composed in `PartII-a:N05/1`) to establish `BodyEpsLocalH1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace N05_1Aux

/-! ### 1. Orthogonal projection bound `‖PepsC ε c b‖ ≤ ‖b‖` -/

/-- The orthogonal Leray projection `PepsC ε c` on `HSpace c MeridC` is contractive. -/
theorem norm_PepsC_apply_le (ε c : ℝ) (b : HSpace c MeridC) :
    ‖PepsC ε c b‖ ≤ ‖b‖ := by
  set p := PepsC ε c b
  have hp : p ∈ solenoidalHC ε c := Submodule.starProjection_apply_mem (solenoidalHC ε c) b
  have hbp : b - p ∈ (solenoidalHC ε c)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (K := solenoidalHC ε c) b
  have horth : inner ℂ p (b - p) = 0 := (Submodule.mem_orthogonal (solenoidalHC ε c) (b - p)).1 hbp p hp
  have hinner : inner ℂ p p = inner ℂ p b := by
    have hsub : inner ℂ p (b - p) = inner ℂ p b - inner ℂ p p := inner_sub_right p b p
    linear_combination -hsub.symm.trans horth
  have hsq : ‖p‖ ^ 2 ≤ ‖p‖ * ‖b‖ := by
    calc ‖p‖ ^ 2 = RCLike.re (inner ℂ p p) := (inner_self_eq_norm_sq p).symm
      _ = RCLike.re (inner ℂ p b) := by rw [hinner]
      _ ≤ ‖inner ℂ p b‖ := RCLike.re_le_norm _
      _ ≤ ‖p‖ * ‖b‖ := norm_inner_le_norm p b
  nlinarith [norm_nonneg p, norm_nonneg b]

/-! ### 2. `Gamma` dominance helpers -/

theorem one_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) : 1 ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  unfold Gamma GammaBox
  have : 0 < ν⁻¹ := inv_pos.2 hν
  have : 0 < c⁻¹ := inv_pos.2 hc
  have : 0 < σ⁻¹ := inv_pos.2 hσ
  have : 0 < γs⁻¹ := inv_pos.2 hγ
  linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]

theorem inv_sqrt_nu_le_gamma {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) : (Real.sqrt ν)⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have h1 : (Real.sqrt ν)⁻¹ ≤ 1 + ν⁻¹ := by
    by_cases hle : 1 ≤ Real.sqrt ν
    · have : (Real.sqrt ν)⁻¹ ≤ 1⁻¹ := inv_anti₀ zero_lt_one hle
      have : 0 < ν⁻¹ := inv_pos.2 hν
      linarith
    · have hle' : Real.sqrt ν ≤ 1 := le_of_not_ge hle
      have hν_le : ν ≤ Real.sqrt ν := by
        calc ν = Real.sqrt ν * Real.sqrt ν := (Real.mul_self_sqrt hν.le).symm
          _ ≤ 1 * Real.sqrt ν := mul_le_mul_of_nonneg_right hle' hsq.le
          _ = Real.sqrt ν := one_mul _
      have : (Real.sqrt ν)⁻¹ ≤ ν⁻¹ := inv_anti₀ hν hν_le
      linarith
  have h2 : 1 + ν⁻¹ ≤ Gamma ν c σ H1 L1 M γs χ χ1 := by
    unfold Gamma GammaBox
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  exact h1.trans h2

theorem body_factor_le_gamma_sq {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    {μ : ℂ} (hμM : ‖μ‖ ≤ M) (hμγ : γs ≤ μ.re + 1 / 4) :
    1 + (1 + ‖μ‖) / (μ.re + gammaR 2) ≤ 2 * Gamma ν c σ H1 L1 M γs χ χ1 ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0
  have h1M : 1 + ‖μ‖ ≤ G := by
    unfold G Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    have : 0 < γs⁻¹ := inv_pos.2 hγ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hγG : γs⁻¹ ≤ G := by
    unfold G Gamma GammaBox
    have : 0 < ν⁻¹ := inv_pos.2 hν
    have : 0 < c⁻¹ := inv_pos.2 hc
    have : 0 < σ⁻¹ := inv_pos.2 hσ
    linarith [cNorm8_nonneg χ, cNorm8_nonneg χ1]
  have hμγ' : γs ≤ μ.re + gammaR 2 := by rw [gammaR_two]; exact hμγ
  have hinv : (μ.re + gammaR 2)⁻¹ ≤ G := (inv_anti₀ hγ hμγ').trans hγG
  have hdiv : (1 + ‖μ‖) / (μ.re + gammaR 2) ≤ G * G := by
    rw [div_eq_mul_inv]
    exact mul_le_mul h1M hinv (inv_nonneg.2 (hγ.le.trans hμγ')) (by linarith)
  have hGG : G ≤ G * G := le_mul_of_one_le_left (by linarith) hG1
  nlinarith

lemma graph_norm_split {nv nl nt ns sqν C₀ G nb : ℝ}
    (hC₀ : 0 ≤ C₀) (hG1 : 1 ≤ G) (hnb : 0 ≤ nb)
    (hnv : 0 ≤ nv) (hnl : 0 ≤ nl) (hnt : 0 ≤ nt) (hns : 0 ≤ ns)
    (hsq : 0 < sqν) (hinvG : sqν⁻¹ ≤ G)
    (hgb : (nv + nl + nt) + sqν * ns ≤ 2 * C₀ * G ^ 2 * nb) :
    nv + nt + ns ≤ 4 * C₀ * G ^ 3 * nb := by
  have hG0 : 0 ≤ G := by linarith
  have hG23 : G ^ 2 ≤ G ^ 3 := pow_le_pow_right₀ hG1 (by norm_num)
  have hvt : nv + nt ≤ 2 * C₀ * G ^ 3 * nb := by
    have h1 : nv + nt ≤ 2 * C₀ * G ^ 2 * nb := by
      linarith [mul_nonneg hsq.le hns]
    have h2 : 2 * C₀ * G ^ 2 * nb ≤ 2 * C₀ * G ^ 3 * nb :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG23 (by positivity)) hnb
    exact h1.trans h2
  have hgrad : ns ≤ 2 * C₀ * G ^ 3 * nb := by
    have h1 : sqν * ns ≤ 2 * C₀ * G ^ 2 * nb := by linarith
    calc ns = sqν⁻¹ * (sqν * ns) := by rw [← mul_assoc, inv_mul_cancel₀ hsq.ne', one_mul]
      _ ≤ G * (2 * C₀ * G ^ 2 * nb) :=
          mul_le_mul hinvG h1 (mul_nonneg hsq.le hns) hG0
      _ = 2 * C₀ * G ^ 3 * nb := by ring
  linarith

/-! ### 3. Phase lift of `Teps` into `D P ν 2` and `commonBodyGraphBound` estimate -/

/-- Under the phase lift `U ∘ B0223.liftVec`, `Teps hν hε hc hP μ b` belongs to the maximal
domain `D P ν 2` and satisfies the `commonBodyGraphBound` estimate controlling `‖v‖_{Y_2}`,
`‖T0D v‖_{Y_2}`, and `∑ j, ‖grad_v j‖_{Y_2}` by `O(Gamma^3 ‖b‖)`. -/
theorem teps_lift_mem_D2_and_graphBound :
    ∃ C_G : ℝ, 0 ≤ C_G ∧
      ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c),
        0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
        ∀ (ε : ℝ) (hε : 0 < ε) (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
        ∀ (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2), N01.IsPhaseLift ε P U →
        ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ b : HSpace c MeridC,
          ∃ (v : D P ν 2) (grad_v : Fin 3 → Yq P 2),
            (v : Yq P 2) = U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ b)) ∧
            bodyOp P ν 2 μ v = U (B0223.liftVec hε hc hP (PepsC ε c b)) ∧
            HasGrad (v : Yq P 2) grad_v ∧
            ‖(v : Yq P 2)‖ + ‖T0D v‖ + ∑ j : Fin 3, ‖grad_v j‖ ≤
              C_G * Gamma ν c σ H1 L1 M γs χ χ1 ^ 3 * ‖b‖ := by
  have h1 : (1 : ℝ≥0∞) < 2 := ENNReal.one_lt_two
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  obtain ⟨C₀, hC₀, hGraph⟩ := commonBodyGraphBound 2 h1 h3
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P _ hP hP1 U hU μ hμM hμγ b
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hμ : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγ hμγ
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hμ
  obtain ⟨Rm, -, hRm⟩ := bodyResolvent_exists 2 h1 h3 P ν hν μ hμ'
  set g : Yq P 2 := U (B0223.liftVec hε hc hP (PepsC ε c b)) with hgdef
  obtain ⟨v, hv, hvb⟩ := N01.bodyResolvent_bodyOp hP1 hν hμ Rm ENNReal.ofNat_ne_top hRm g
  have hv_eq : (v : Yq P 2) = U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ b)) := by
    have hTeps : B0223.liftVec hε hc hP (Teps hν hε hc hP μ b) =
        B0223.physRes hν ε μ (B0223.liftVec hε hc hP (PepsC ε c b)) :=
      B0223.J_RepsVec hν hε hc hP hμ (PepsC ε c b)
    rw [hv, hgdef, hTeps,
      N01.phaseLift_physRes N01.phaseSemigroupConj hν hε hU hμ Rm ENNReal.ofNat_ne_top hRm]
  obtain ⟨grad_v, hgrad, hgb⟩ := hGraph P hP1 ν hν μ hμ' v
  refine ⟨v, grad_v, hv_eq, hvb, hgrad, ?_⟩
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hbody_norm : ‖bodyOp P ν 2 μ v‖ ≤ ‖b‖ := by
    rw [hvb, hgdef, U.norm_map, (B0223.liftVec hε hc hP).norm_map]
    exact norm_PepsC_apply_le ε c b
  have hfac := body_factor_le_gamma_sq χ χ1 hν hc hσ hσH hL1 hγ hμM hμγ
  have hgb' : graphNormD v + Real.sqrt ν * ∑ j, ‖grad_v j‖ ≤ 2 * C₀ * G ^ 2 * ‖b‖ := by
    calc graphNormD v + Real.sqrt ν * ∑ j, ‖grad_v j‖
        ≤ C₀ * (1 + (1 + ‖μ‖) / (μ.re + gammaR 2)) * ‖bodyOp P ν 2 μ v‖ := hgb
      _ ≤ C₀ * (2 * G ^ 2) * ‖b‖ := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hfac hC₀) hbody_norm (norm_nonneg _)
            (mul_nonneg hC₀ (by positivity))
      _ = 2 * C₀ * G ^ 2 * ‖b‖ := by ring
  exact graph_norm_split hC₀ hG1 (norm_nonneg b)
    (norm_nonneg (v : Yq P 2)) (norm_nonneg (nuLapD v)) (norm_nonneg (T0D v))
    (Finset.sum_nonneg fun j _ => norm_nonneg _) (Real.sqrt_pos.2 hν)
    (inv_sqrt_nu_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0) hgb'

/-- Unconditional `Gamma^2` bound on `cellL2Norm c (flatStressCutRep c χ w)` in terms of the
isometric phase lift `v = U (B0223.liftVec hε hc hP w)`. -/
theorem cellL2Norm_flatStressCutRep_lift_le {ν c σ H1 L1 M γs ε P : ℝ} [Fact (0 < P)]
    (χ χ1 : Profile → ℝ) (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1)
    (hL1 : 0 ≤ L1) (hγ : 0 < γs) (hM : 0 ≤ M) (hχ : IsNearCutoff c σ H1 L1 χ) (hm : Measurable χ)
    (hε : 0 < ε) (hP : P = 2 * ε * c) (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2)
    (w : HSpace c MeridC) (v : D P ν 2)
    (hv : (v : Yq P 2) = U (B0223.liftVec hε hc hP w)) :
    cellL2Norm c (flatStressCutRep c χ w) ≤
      Gamma ν c σ H1 L1 M γs χ χ1 ^ 2 * ‖(v : Yq P 2)‖ := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
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
  have hnorm_v : ‖(v : Yq P 2)‖ = ‖w‖ := by
    rw [hv, U.norm_map, (B0223.liftVec hε hc hP).norm_map]
  have hL2 := N05_4Aux.cellL2Norm_flatStressCutRep_le_mul hc hσ hσH hχ hm w
  rw [← hnorm_v] at hL2
  calc cellL2Norm c (flatStressCutRep c χ w)
      ≤ (1 + H1) * cNorm8 χ * ‖(v : Yq P 2)‖ := hL2
    _ ≤ G * G * ‖(v : Yq P 2)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul h1H1_G hcN_G (cNorm8_nonneg χ) hG0
    _ = G ^ 2 * ‖(v : Yq P 2)‖ := by ring

end N05_1Aux

open N05_1Aux

/-! ### 4. Coordinate-derivative conversion `(1, S, Q_ε, ∂_η) ↦ (1, ∂_s, ∂_q, ∂_η)` on the box -/

/-- Box-localised `(1, S, Q_ε, ∂_η)` representation of `U : HSpace c MeridC` on `cellMeasure c`,
prior to converting `(S, Q_ε, ∂_η)` into `(∂_s, ∂_q, ∂_η)` via `dsFromS` and `dqFromSQE`
(source lines 1791-1792). -/
structure HasLocalSQE (c σ H1 L1 ε : ℝ) (U : HSpace c MeridC)
    (u Su Qu Eu : Profile → MeridC) : Prop where
  ae_eq : (U : Profile → MeridC) =ᵐ[measureH c] u
  periodic_u : QPeriodic c u
  periodic_Su : QPeriodic c Su
  periodic_Qu : QPeriodic c Qu
  periodic_Eu : QPeriodic c Eu
  support_u : ∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  support_Su : ∀ p : Profile, Su p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  support_Qu : ∀ p : Profile, Qu p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  support_Eu : ∀ p : Profile, Eu p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1
  memLp_u : MemLp u 2 (cellMeasure c)
  memLp_Su : MemLp Su 2 (cellMeasure c)
  memLp_Qu : MemLp Qu 2 (cellMeasure c)
  memLp_Eu : MemLp Eu 2 (cellMeasure c)
  ibp_s : ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (dsFromS Su p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (u p) (pdS φ p) ∂(cellMeasure c)
  ibp_q : ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (dqFromSQE ε u Su Qu Eu p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (u p) (pdQ φ p) ∂(cellMeasure c)
  ibp_eta : ∀ φ : Profile → MeridC, IsMeridTest c φ →
    ∫ p, inner ℂ (Eu p) (φ p) ∂(cellMeasure c) =
      -∫ p, inner ℂ (u p) (pdEta φ p) ∂(cellMeasure c)

private lemma sqrt_rpow_sq (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

private lemma sq_rpow_half (y : ℝ) (hy : 0 ≤ y) : (y ^ 2) ^ (1 / 2 : ℝ) = y := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hy]

/-- `dsFromS Su` belongs to `L²(cellMeasure c)` when `Su` is supported in `σ ≤ s` (`σ > 0`). -/
theorem memLp_dsFromS {c σ H1 L1 : ℝ} (hσ : 0 < σ) {Su : Profile → MeridC}
    (hsupp : ∀ p : Profile, Su p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hSu : MemLp Su 2 (cellMeasure c)) :
    MemLp (dsFromS Su) 2 (cellMeasure c) := by
  have hm : AEStronglyMeasurable (dsFromS Su) (cellMeasure c) :=
    measurable_fst.inv.aestronglyMeasurable.smul hSu.1
  refine hSu.of_le_mul (c := σ⁻¹) hm (Eventually.of_forall fun p => ?_)
  by_cases h0 : Su p = 0
  · simp [dsFromS, h0]
  · have hpσ : σ ≤ p.1 := (hsupp p h0).1
    have hp0 : 0 < p.1 := lt_of_lt_of_le hσ hpσ
    rw [dsFromS, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hp0.le)]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hσ hpσ) (norm_nonneg _)

/-- `dqFromSQE ε u Su Qu Eu` belongs to `L²(cellMeasure c)` when `Eu` is supported in `|η| ≤ L1`. -/
theorem memLp_dqFromSQE {c σ H1 L1 ε : ℝ} {u Su Qu Eu : Profile → MeridC}
    (hsuppE : ∀ p : Profile, Eu p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hu : MemLp u 2 (cellMeasure c)) (hSu : MemLp Su 2 (cellMeasure c))
    (hQu : MemLp Qu 2 (cellMeasure c)) (hEu : MemLp Eu 2 (cellMeasure c)) :
    MemLp (dqFromSQE ε u Su Qu Eu) 2 (cellMeasure c) := by
  have hηE : MemLp (fun p : Profile => p.2.2 • Eu p) 2 (cellMeasure c) := by
    have hm : AEStronglyMeasurable (fun p : Profile => p.2.2 • Eu p) (cellMeasure c) :=
      (measurable_snd.comp measurable_snd).aestronglyMeasurable.smul hEu.1
    refine hEu.of_le_mul (c := |L1|) hm (Eventually.of_forall fun p => ?_)
    by_cases h0 : Eu p = 0
    · simp [h0]
    · have hpη : |p.2.2| ≤ |L1| := ((hsuppE p h0).2.2).trans (le_abs_self L1)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hpη (norm_nonneg _)
  exact hQu.add (((hSu.const_smul (2 : ℝ)).add hηE).add hu |>.const_smul ε)

/-- `HasLocalSQE` implies `HasWeakCellH1` for `(u, dsFromS Su, dqFromSQE ε u Su Qu Eu, Eu)`. -/
theorem hasWeakCellH1_of_hasLocalSQE {c σ H1 L1 ε : ℝ} (hσ : 0 < σ)
    {U : HSpace c MeridC} {u Su Qu Eu : Profile → MeridC}
    (h : HasLocalSQE c σ H1 L1 ε U u Su Qu Eu) :
    HasWeakCellH1 c σ H1 L1 U u (dsFromS Su) (dqFromSQE ε u Su Qu Eu) Eu where
  ae_eq := h.ae_eq
  periodic_u := h.periodic_u
  periodic_ds := fun p => by simp [dsFromS, h.periodic_Su p]
  periodic_dq := fun p => by
    simp [dqFromSQE, h.periodic_u p, h.periodic_Su p, h.periodic_Qu p, h.periodic_Eu p]
  periodic_deta := h.periodic_Eu
  support_u := h.support_u
  support_ds := fun p hp => h.support_Su p fun h0 => hp (by simp [dsFromS, h0])
  support_dq := fun p hp => by
    by_contra hc
    have hu0 : u p = 0 := by by_contra h0; exact hc (h.support_u p h0)
    have hS0 : Su p = 0 := by by_contra h0; exact hc (h.support_Su p h0)
    have hQ0 : Qu p = 0 := by by_contra h0; exact hc (h.support_Qu p h0)
    have hE0 : Eu p = 0 := by by_contra h0; exact hc (h.support_Eu p h0)
    exact hp (by simp [dqFromSQE, hu0, hS0, hQ0, hE0])
  support_deta := h.support_Eu
  memLp_u := h.memLp_u
  memLp_ds := memLp_dsFromS hσ h.support_Su h.memLp_Su
  memLp_dq := memLp_dqFromSQE h.support_Eu h.memLp_u h.memLp_Su h.memLp_Qu h.memLp_Eu
  memLp_deta := h.memLp_Eu
  ibp_s := h.ibp_s
  ibp_q := h.ibp_q
  ibp_eta := h.ibp_eta

/-- Bound on `cellL2Norm c (dsFromS Su)` on the observation box. -/
theorem cellL2Norm_dsFromS_le {ν c σ H1 L1 M γs : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) {Su : Profile → MeridC}
    (hsupp : ∀ p : Profile, Su p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hSu : MemLp Su 2 (cellMeasure c)) :
    cellL2Norm c (dsFromS Su) ≤ Gamma ν c σ H1 L1 M γs χ χ1 * cellL2Norm c Su := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
  have hG0 : 0 ≤ G := by linarith
  have hds : MemLp (dsFromS Su) 2 (cellMeasure c) := memLp_dsFromS hσ hsupp hSu
  have hpt : ∀ p : Profile, ‖dsFromS Su p‖ ≤ G * ‖Su p‖ := fun p => by
    by_cases h0 : Su p = 0
    · simp [dsFromS, h0]
    · exact norm_dsFromS_le χ χ1 hν hc hσ hσH hL1 hγ hM Su (hsupp p h0).1
  have hint : ∫ p, ‖dsFromS Su p‖ ^ 2 ∂(cellMeasure c) ≤
      (G * cellL2Norm c Su) ^ 2 := by
    have h1 : ∫ p, ‖dsFromS Su p‖ ^ 2 ∂(cellMeasure c) ≤
        ∫ p, G ^ 2 * ‖Su p‖ ^ 2 ∂(cellMeasure c) := by
      refine integral_mono hds.norm.integrable_sq (hSu.norm.integrable_sq.const_mul (G ^ 2)) (fun p => ?_)
      calc ‖dsFromS Su p‖ ^ 2 ≤ (G * ‖Su p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hpt p) 2
        _ = G ^ 2 * ‖Su p‖ ^ 2 := by ring
    have hA : 0 ≤ ∫ p, ‖Su p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun _ => sq_nonneg _
    calc ∫ p, ‖dsFromS Su p‖ ^ 2 ∂(cellMeasure c)
        ≤ ∫ p, G ^ 2 * ‖Su p‖ ^ 2 ∂(cellMeasure c) := h1
      _ = G ^ 2 * ∫ p, ‖Su p‖ ^ 2 ∂(cellMeasure c) := integral_const_mul _ _
      _ = G ^ 2 * (cellL2Norm c Su) ^ 2 := by rw [cellL2Norm, sqrt_rpow_sq _ hA]
      _ = (G * cellL2Norm c Su) ^ 2 := by ring
  unfold cellL2Norm
  calc (∫ p, ‖dsFromS Su p‖ ^ 2 ∂(cellMeasure c)) ^ (1 / 2 : ℝ)
      ≤ ((G * cellL2Norm c Su) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hint (by norm_num)
    _ = G * cellL2Norm c Su := sq_rpow_half _ (mul_nonneg hG0 (cellL2Norm_nonneg c Su))

/-- Bound on `cellL2Norm c (dqFromSQE ε u Su Qu Eu)` on the observation box. -/
theorem cellL2Norm_dqFromSQE_le {ν c σ H1 L1 M γs ε : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {u Su Qu Eu : Profile → MeridC}
    (hsuppU : ∀ p : Profile, u p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hsuppS : ∀ p : Profile, Su p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hsuppQ : ∀ p : Profile, Qu p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hsuppE : ∀ p : Profile, Eu p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hu : MemLp u 2 (cellMeasure c)) (hSu : MemLp Su 2 (cellMeasure c))
    (hQu : MemLp Qu 2 (cellMeasure c)) (hEu : MemLp Eu 2 (cellMeasure c)) :
    cellL2Norm c (dqFromSQE ε u Su Qu Eu) ≤
      2 * Gamma ν c σ H1 L1 M γs χ χ1 *
        (cellL2Norm c Qu + cellL2Norm c Su + cellL2Norm c Eu + cellL2Norm c u) := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
  have hG0 : 0 ≤ G := by linarith
  have hdq : MemLp (dqFromSQE ε u Su Qu Eu) 2 (cellMeasure c) :=
    memLp_dqFromSQE hsuppE hu hSu hQu hEu
  have hpt : ∀ p : Profile,
      ‖dqFromSQE ε u Su Qu Eu p‖ ≤ G * (‖Qu p‖ + ‖Su p‖ + ‖Eu p‖ + ‖u p‖) := fun p => by
    by_cases h0 : Qu p = 0 ∧ Su p = 0 ∧ Eu p = 0 ∧ u p = 0
    · rcases h0 with ⟨hQ0, hS0, hE0, hu0⟩
      simp [dqFromSQE, hQ0, hS0, hE0, hu0]
    · have hpη : |p.2.2| ≤ L1 := by
        by_cases hQ : Qu p = 0
        · by_cases hS : Su p = 0
          · by_cases hE : Eu p = 0
            · have hu' : u p ≠ 0 := fun hu0 => h0 ⟨hQ, hS, hE, hu0⟩
              exact (hsuppU p hu').2.2
            · exact (hsuppE p hE).2.2
          · exact (hsuppS p hS).2.2
        · exact (hsuppQ p hQ).2.2
      exact norm_dqFromSQE_le χ χ1 hν hc hσ hσH hγ hM hε0 hε1 u Su Qu Eu hpη
  have i₁ : Integrable (fun p => ‖Qu p‖ ^ 2) (cellMeasure c) := hQu.norm.integrable_sq
  have i₂ : Integrable (fun p => ‖Su p‖ ^ 2) (cellMeasure c) := hSu.norm.integrable_sq
  have i₃ : Integrable (fun p => ‖Eu p‖ ^ 2) (cellMeasure c) := hEu.norm.integrable_sq
  have i₄ : Integrable (fun p => ‖u p‖ ^ 2) (cellMeasure c) := hu.norm.integrable_sq
  have j12 : Integrable (fun p => ‖Qu p‖ ^ 2 + ‖Su p‖ ^ 2) (cellMeasure c) := i₁.add i₂
  have j123 : Integrable (fun p => ‖Qu p‖ ^ 2 + ‖Su p‖ ^ 2 + ‖Eu p‖ ^ 2) (cellMeasure c) :=
    j12.add i₃
  have j1234 :
      Integrable (fun p => ‖Qu p‖ ^ 2 + ‖Su p‖ ^ 2 + ‖Eu p‖ ^ 2 + ‖u p‖ ^ 2) (cellMeasure c) :=
    j123.add i₄
  have hL : ∫ p, ‖dqFromSQE ε u Su Qu Eu p‖ ^ 2 ∂(cellMeasure c) ≤
      ∫ p, 4 * G ^ 2 * (‖Qu p‖ ^ 2 + ‖Su p‖ ^ 2 + ‖Eu p‖ ^ 2 + ‖u p‖ ^ 2) ∂(cellMeasure c) := by
    refine integral_mono hdq.norm.integrable_sq (j1234.const_mul (4 * G ^ 2)) (fun p => ?_)
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hpt p) 2
    have h2 : (‖Qu p‖ + ‖Su p‖ + ‖Eu p‖ + ‖u p‖) ^ 2 ≤
        4 * (‖Qu p‖ ^ 2 + ‖Su p‖ ^ 2 + ‖Eu p‖ ^ 2 + ‖u p‖ ^ 2) := by
      nlinarith [sq_nonneg (‖Qu p‖ - ‖Su p‖), sq_nonneg (‖Qu p‖ - ‖Eu p‖),
        sq_nonneg (‖Qu p‖ - ‖u p‖), sq_nonneg (‖Su p‖ - ‖Eu p‖),
        sq_nonneg (‖Su p‖ - ‖u p‖), sq_nonneg (‖Eu p‖ - ‖u p‖)]
    calc ‖dqFromSQE ε u Su Qu Eu p‖ ^ 2
        ≤ (G * (‖Qu p‖ + ‖Su p‖ + ‖Eu p‖ + ‖u p‖)) ^ 2 := h1
      _ = G ^ 2 * (‖Qu p‖ + ‖Su p‖ + ‖Eu p‖ + ‖u p‖) ^ 2 := by ring
      _ ≤ G ^ 2 * (4 * (‖Qu p‖ ^ 2 + ‖Su p‖ ^ 2 + ‖Eu p‖ ^ 2 + ‖u p‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg G)
      _ = 4 * G ^ 2 * (‖Qu p‖ ^ 2 + ‖Su p‖ ^ 2 + ‖Eu p‖ ^ 2 + ‖u p‖ ^ 2) := by ring
  have hR : ∫ p, 4 * G ^ 2 * (‖Qu p‖ ^ 2 + ‖Su p‖ ^ 2 + ‖Eu p‖ ^ 2 + ‖u p‖ ^ 2) ∂(cellMeasure c) =
      4 * G ^ 2 * ((∫ p, ‖Qu p‖ ^ 2 ∂(cellMeasure c)) + (∫ p, ‖Su p‖ ^ 2 ∂(cellMeasure c)) +
        (∫ p, ‖Eu p‖ ^ 2 ∂(cellMeasure c)) + (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c))) := by
    rw [integral_const_mul, integral_add j123 i₄, integral_add j12 i₃, integral_add i₁ i₂]
  have hA₁ : 0 ≤ ∫ p, ‖Qu p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun _ => sq_nonneg _
  have hA₂ : 0 ≤ ∫ p, ‖Su p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun _ => sq_nonneg _
  have hA₃ : 0 ≤ ∫ p, ‖Eu p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun _ => sq_nonneg _
  have hA₄ : 0 ≤ ∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun _ => sq_nonneg _
  have hT : (∫ p, ‖Qu p‖ ^ 2 ∂(cellMeasure c)) + (∫ p, ‖Su p‖ ^ 2 ∂(cellMeasure c)) +
      (∫ p, ‖Eu p‖ ^ 2 ∂(cellMeasure c)) + (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c)) ≤
      (cellL2Norm c Qu + cellL2Norm c Su + cellL2Norm c Eu + cellL2Norm c u) ^ 2 := by
    have s1 : (cellL2Norm c Qu) ^ 2 = ∫ p, ‖Qu p‖ ^ 2 ∂(cellMeasure c) := sqrt_rpow_sq _ hA₁
    have s2 : (cellL2Norm c Su) ^ 2 = ∫ p, ‖Su p‖ ^ 2 ∂(cellMeasure c) := sqrt_rpow_sq _ hA₂
    have s3 : (cellL2Norm c Eu) ^ 2 = ∫ p, ‖Eu p‖ ^ 2 ∂(cellMeasure c) := sqrt_rpow_sq _ hA₃
    have s4 : (cellL2Norm c u) ^ 2 = ∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c) := sqrt_rpow_sq _ hA₄
    have t1 := cellL2Norm_nonneg c Qu
    have t2 := cellL2Norm_nonneg c Su
    have t3 := cellL2Norm_nonneg c Eu
    have t4 := cellL2Norm_nonneg c u
    nlinarith [mul_nonneg t1 t2, mul_nonneg t1 t3, mul_nonneg t1 t4,
      mul_nonneg t2 t3, mul_nonneg t2 t4, mul_nonneg t3 t4]
  set R := 2 * G * (cellL2Norm c Qu + cellL2Norm c Su + cellL2Norm c Eu + cellL2Norm c u)
  have hR0 : 0 ≤ R := by
    dsimp [R]
    refine mul_nonneg (mul_nonneg zero_le_two hG0) ?_
    linarith [cellL2Norm_nonneg c Qu, cellL2Norm_nonneg c Su,
      cellL2Norm_nonneg c Eu, cellL2Norm_nonneg c u]
  have hXY : ∫ p, ‖dqFromSQE ε u Su Qu Eu p‖ ^ 2 ∂(cellMeasure c) ≤ R ^ 2 := by
    calc ∫ p, ‖dqFromSQE ε u Su Qu Eu p‖ ^ 2 ∂(cellMeasure c)
        ≤ 4 * G ^ 2 * ((∫ p, ‖Qu p‖ ^ 2 ∂(cellMeasure c)) + (∫ p, ‖Su p‖ ^ 2 ∂(cellMeasure c)) +
            (∫ p, ‖Eu p‖ ^ 2 ∂(cellMeasure c)) + (∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c))) :=
          hL.trans hR.le
      _ ≤ 4 * G ^ 2 * (cellL2Norm c Qu + cellL2Norm c Su + cellL2Norm c Eu + cellL2Norm c u) ^ 2 :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ = R ^ 2 := by dsimp [R]; ring
  calc cellL2Norm c (dqFromSQE ε u Su Qu Eu)
      ≤ (R ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) hXY (by norm_num)
    _ = R := sq_rpow_half R hR0

/-- Total `cellH1Norm` bound for `(u, dsFromS Su, dqFromSQE ε u Su Qu Eu, Eu)` from `HasLocalSQE`. -/
theorem cellH1Norm_of_hasLocalSQE_le {ν c σ H1 L1 M γs ε : ℝ} (χ χ1 : Profile → ℝ)
    (hν : 0 < ν) (hc : 0 < c) (hσ : 0 < σ) (hσH : σ ≤ H1) (hL1 : 0 ≤ L1) (hγ : 0 < γs)
    (hM : 0 ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {U : HSpace c MeridC} {u Su Qu Eu : Profile → MeridC}
    (h : HasLocalSQE c σ H1 L1 ε U u Su Qu Eu) :
    cellH1Norm c u (dsFromS Su) (dqFromSQE ε u Su Qu Eu) Eu ≤
      3 * Gamma ν c σ H1 L1 M γs χ χ1 *
        (cellL2Norm c u + cellL2Norm c Su + cellL2Norm c Qu + cellL2Norm c Eu) := by
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM
  have hds := cellL2Norm_dsFromS_le χ χ1 hν hc hσ hσH hL1 hγ hM h.support_Su h.memLp_Su
  have hdq := cellL2Norm_dqFromSQE_le χ χ1 hν hc hσ hσH hL1 hγ hM hε0 hε1
    h.support_u h.support_Su h.support_Qu h.support_Eu
    h.memLp_u h.memLp_Su h.memLp_Qu h.memLp_Eu
  have hu0 := cellL2Norm_nonneg c u
  have hS0 := cellL2Norm_nonneg c Su
  have hQ0 := cellL2Norm_nonneg c Qu
  have hE0 := cellL2Norm_nonneg c Eu
  unfold cellH1Norm
  nlinarith

/-! ### 5. Leaf obligation: chart pullback of `D P ν 2` and cutoff localisation (`PhaseD2CutoffSQE`) -/

/-- **Leaf (`PartII-a:N05/1/1`) — chart pullback of `D P ν 2` and observation-box cutoff localisation
(`PhaseD2CutoffSQE`)**
(source `the November 2 reference manuscript`,
lines 1789-1793): for any `w ∈ HSpace c MeridC` whose phase lift `v = U (liftVec w)` lies
in the maximal domain `D P ν 2` with spatial gradient `grad_v` (`HasGrad (v : Yq P 2) grad_v`),
since `T - 3/4` conjugates to `S - 1/4` (`T0D v`) and `grad_v` lifts `(Q_ε w, ∂_η w, ε w_r)`,
localising `w` by the smooth observation-box cutoff `χ` (`IsNearCutoff c σ H1 L1 χ`) produces
box-supported `(1, S, Q_ε, ∂_η)` representatives `(u, Su, Qu, Eu)` satisfying `HasLocalSQE` and
bounded in `cellL2Norm c` by `C * Gamma^k * (‖v‖ + ‖T0D v‖ + ∑ j, ‖grad_v j‖)`. -/
def PhaseD2CutoffSQE : Prop :=
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ (ν c σ H1 L1 M γs : ℝ) (χ χ1 : Profile → ℝ), 0 < ν → ∀ (hc : 0 < c),
      0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs → 0 ≤ M →
      IsNearCutoff c σ H1 L1 χ → IsLargerCutoff c χ χ1 →
      ∀ (hm : Measurable χ) (B : ℝ) (hB : ∀ p, |χ p| ≤ B),
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ (P : ℝ) [Fact (0 < P)] (hP : P = 2 * ε * c), P ≤ 1 →
      ∀ (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2), N01.IsPhaseLift ε P U →
      ∀ (w : HSpace c MeridC) (v : D P ν 2) (grad_v : Fin 3 → Yq P 2),
        (v : Yq P 2) = U (B0223.liftVec hε hc hP w) →
        HasGrad (v : Yq P 2) grad_v →
        ∃ u Su Qu Eu : Profile → MeridC,
          HasLocalSQE c σ H1 L1 ε (mulChi (measureH c) χ hm hB w) u Su Qu Eu ∧
          cellL2Norm c u + cellL2Norm c Su + cellL2Norm c Qu + cellL2Norm c Eu ≤
            C * Gamma ν c σ H1 L1 M γs χ χ1 ^ k *
              (‖(v : Yq P 2)‖ + ‖T0D v‖ + ∑ j : Fin 3, ‖grad_v j‖)

/-! ### 6. Conditional assembly of `BodyEpsLocalH1` -/

/-- **Conditional assembly of `BodyEpsLocalH1` (`PartII-a:N05/1`)** from `PhaseD2CutoffSQE`,
`N01.phaseLiftExists`, `N01.phaseSemigroupConj`, `commonBodyGraphBound`, and the box coordinate
conversion lemmas (`dsFromS`, `dqFromSQE`). -/
theorem bodyEpsLocalH1_of (hPull : PhaseD2CutoffSQE) : BodyEpsLocalH1 := by
  obtain ⟨C_G, hC_G, hGraph⟩ := teps_lift_mem_D2_and_graphBound
  obtain ⟨k_L, C_L, hC_L, hLoc⟩ := hPull
  refine ⟨k_L + 4, 3 * C_L * C_G, by positivity, ?_⟩
  intro ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hχ hχ1 hm B hB ε hε hε1 P _ hP hP1 μ hμM hμγ b
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  obtain ⟨U, hU⟩ := N01.phaseLiftExists ε P hε
  obtain ⟨v, grad_v, hv_eq, -, hgrad, hv_bd⟩ :=
    hGraph ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ ε hε P hP hP1 U hU μ hμM hμγ b
  obtain ⟨u, Su, Qu, Eu, hSQE, hSQE_bd⟩ :=
    hLoc ν c σ H1 L1 M γs χ χ1 hν hc hσ hσH hL1 hγ hM0 hχ hχ1 hm B hB ε hε hε1 P hP hP1 U hU
      (Teps hν hε hc hP μ b) v grad_v hv_eq hgrad
  refine ⟨u, dsFromS Su, dqFromSQE ε u Su Qu Eu, Eu,
    hasWeakCellH1_of_hasLocalSQE hσ hSQE, ?_⟩
  set G := Gamma ν c σ H1 L1 M γs χ χ1
  have hG1 : 1 ≤ G := one_le_gamma χ χ1 hν hc hσ hσH hL1 hγ hM0
  have hG0 : 0 ≤ G := by linarith
  have h1 := cellH1Norm_of_hasLocalSQE_le χ χ1 hν hc hσ hσH hL1 hγ hM0 hε.le hε1 hSQE
  calc cellH1Norm c u (dsFromS Su) (dqFromSQE ε u Su Qu Eu) Eu
      ≤ 3 * G * (cellL2Norm c u + cellL2Norm c Su + cellL2Norm c Qu + cellL2Norm c Eu) := h1
    _ ≤ 3 * G * (C_L * G ^ k_L * (‖(v : Yq P 2)‖ + ‖T0D v‖ + ∑ j : Fin 3, ‖grad_v j‖)) :=
        mul_le_mul_of_nonneg_left hSQE_bd (by positivity)
    _ ≤ 3 * G * (C_L * G ^ k_L * (C_G * G ^ 3 * ‖b‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hv_bd (mul_nonneg hC_L (pow_nonneg hG0 k_L))
    _ = 3 * C_L * C_G * G ^ (k_L + 4) * ‖b‖ := by ring

end UnforcedLeray.Short.PartIIa
