import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_1_4
import UnforcedLeray.Short.PartIIa.Tasks.F05bSliceContOfDecay
import UnforcedLeray.Units.B0412
import UnforcedLeray.Lib.LerayLp.Cutoff

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/1/4/2`: cutoff limit `GPCutoffLimit`

Target: `UnforcedLeray.Short.PartIIIb.Concrete.GPCutoffLimit` (parent module, Lemma B).
Source of record: `the November 2 reference manuscript` (cut-off of the
phase-periodic potential; the parent file cites lines 1393-1400, 1409-1412).

Proof outline, with `χ_R = NavierStokesR3.ComparisonCutoffs.cutoff R`, `R = n + 1 ≥ 1`.

* Product rule: `∇(χ σ) = χ ∇σ + σ ∇χ` (`gradT_ofReal_mul_apply`, from `HasFDerivAt.mul`).
  Hence `∇(χ_R σ) - ∇σ = (χ_R - 1) ∇σ + σ · G_R`, with `G_R = gaVec χ_R`.
* Pointwise bounds, uniform in `n` and `τ`: `0 ≤ χ_R ≤ 1` gives `|χ_R - 1| ≤ 1`;
  `|∂ⱼχ_R| ≤ 3 C₀ (1+|y|)⁻¹` for `R ≥ 1` gives `‖G_R‖ ≤ 9 C₀ (1+|y|)⁻¹`; `|σ| ≤ C(1+|y|)⁻²`
  and `|∇σ| ≤ C(1+|y|)⁻³`. So `‖∇(χ_{n+1} σ) - ∇σ‖ ≤ K (1+|y|)^{-3}` with `K` independent of
  `n, τ`, and `(1+|y|)^{-3·11/7} = (1+|y|)^{-33/7}` is integrable on `ℝ³`.
* Pointwise convergence: for `‖y‖ ≤ n+1`, `χ_{n+1}(y) = 1` and `G_{n+1}(y) = 0`, so the
  difference vanishes eventually in `n`.
* Dominated convergence gives `∫⁻ ‖·‖ₑ^{11/7} → 0`, hence `L^{11/7}` convergence, and the
  domination gives the uniform bound.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory Set
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace

/-- The vector `∑ⱼ (∂ⱼ a)(y) eⱼ` of a real function `a` (the second term of the product rule). -/
def gaVec (a : Space → ℝ) (y : Space) : CVec3 :=
  ∑ j : Fin 3, ((UnforcedLeray.spatialTestDerivative j a y : ℝ) : ℂ) •
    EuclideanSpace.single j (1 : ℂ)

/-- The gradient of a smooth `ℂ`-valued function is continuous. -/
theorem continuous_gradT_of_contDiff {φ : ℝ × Space → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (gradT φ) := by
  have hdy : ∀ j : Fin 3, Continuous fun p : ℝ × Space => UnforcedLeray.PhaseSpace.dy j φ p := by
    intro j
    unfold UnforcedLeray.PhaseSpace.dy
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  unfold gradT
  exact continuous_finsetSum _ fun j _ => (hdy j).smul continuous_const

/-- Product rule for the `j`-th derivative of `(a · σ)` with `a` real. -/
theorem dy_ofReal_mul_apply {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) {σ : ℝ × Space → ℂ}
    (hσ : ContDiff ℝ ∞ σ) (j : Fin 3) (p : ℝ × Space) :
    UnforcedLeray.PhaseSpace.dy j (fun z => ((a z.2 : ℝ) : ℂ) * σ z) p =
      ((a p.2 : ℝ) : ℂ) * UnforcedLeray.PhaseSpace.dy j σ p +
        ((UnforcedLeray.spatialTestDerivative j a p.2 : ℝ) : ℂ) * σ p := by
  have hda : Differentiable ℝ a := ha.differentiable (by simp)
  have hdσ : Differentiable ℝ σ := hσ.differentiable (by simp)
  have hc : HasFDerivAt (fun z : ℝ × Space => ((a z.2 : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ a p.2).comp (ContinuousLinearMap.snd ℝ ℝ Space))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p ((hda p.2).hasFDerivAt.comp p hasFDerivAt_snd)
  have hprod := hc.mul (hdσ p).hasFDerivAt
  have key : fderiv ℝ (fun z : ℝ × Space => ((a z.2 : ℝ) : ℂ) * σ z) p =
      ((a p.2 : ℝ) : ℂ) • fderiv ℝ σ p +
        σ p • (Complex.ofRealCLM.comp ((fderiv ℝ a p.2).comp (ContinuousLinearMap.snd ℝ ℝ Space))) :=
    hprod.fderiv
  unfold UnforcedLeray.PhaseSpace.dy
  rw [key]
  simp [UnforcedLeray.spatialTestDerivative]
  ring

/-- Product rule for the gradient: `∇(a σ) = a ∇σ + σ (∇a)`. -/
theorem gradT_ofReal_mul_apply {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) {σ : ℝ × Space → ℂ}
    (hσ : ContDiff ℝ ∞ σ) (p : ℝ × Space) :
    gradT (fun z => ((a z.2 : ℝ) : ℂ) * σ z) p =
      ((a p.2 : ℝ) : ℂ) • gradT σ p + σ p • gaVec a p.2 := by
  unfold gradT
  simp only [dy_ofReal_mul_apply ha hσ, gaVec, Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  module

/-- Norm bound for `gaVec`. -/
theorem norm_gaVec_le (a : Space → ℝ) (y : Space) :
    ‖gaVec a y‖ ≤ ∑ j : Fin 3, |UnforcedLeray.spatialTestDerivative j a y| := by
  unfold gaVec
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, EuclideanSpace.norm_single, norm_one,
    mul_one]

/-- `gaVec` of a cutoff vanishes inside the ball of radius `R`. -/
theorem gaVec_cutoff_eq_zero {R : ℝ} (hR : 0 < R) {y : Space} (hy : ‖y‖ < R) :
    gaVec (NavierStokesR3.ComparisonCutoffs.cutoff R) y = 0 := by
  unfold gaVec
  simp [UnforcedLeray.RieszLp.spatialTestDerivative_cutoff_of_lt hR hy]

/-- `‖gaVec χ_R(y)‖ ≤ 9 C₀ (1+|y|)⁻¹` for `R ≥ 1`. -/
theorem norm_gaVec_cutoff_le {R : ℝ} (hR : 1 ≤ R) (y : Space) :
    ‖gaVec (NavierStokesR3.ComparisonCutoffs.cutoff R) y‖ ≤
      9 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * (1 + ‖y‖)⁻¹ := by
  refine (norm_gaVec_le _ y).trans ?_
  have h := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    UnforcedLeray.RieszLp.abs_spatialTestDerivative_cutoff_le hR y j
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- Pointwise `L^{11/7}` bound: `‖x‖ ≤ b` gives `‖x‖ₑ^{11/7} ≤ ofReal (b^{11/7})`. -/
theorem enorm_rpow_le_of_norm_le {E : Type*} [NormedAddCommGroup E] (x : E) {b : ℝ}
    (hb : 0 ≤ b) (hx : ‖x‖ ≤ b) :
    ‖x‖ₑ ^ (11 / 7 : ℝ) ≤ ENNReal.ofReal (b ^ (11 / 7 : ℝ)) := by
  calc ‖x‖ₑ ^ (11 / 7 : ℝ) = (ENNReal.ofReal ‖x‖) ^ (11 / 7 : ℝ) := by rw [ofReal_norm]
    _ ≤ (ENNReal.ofReal b) ^ (11 / 7 : ℝ) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx) (by norm_num)
    _ = ENNReal.ofReal (b ^ (11 / 7 : ℝ)) := ENNReal.ofReal_rpow_of_nonneg hb (by norm_num)

/-- The exponent computation `(K t^{-3})^{11/7} = K^{11/7} t^{-33/7}`. -/
theorem rpow_cube_mul {K : ℝ} (hK : 0 ≤ K) (t : ℝ) (ht : 0 ≤ t) :
    (K * t ^ (-3 : ℝ)) ^ (11 / 7 : ℝ) = K ^ (11 / 7 : ℝ) * t ^ (-(33 / 7 : ℝ)) := by
  rw [Real.mul_rpow hK (Real.rpow_nonneg ht _), ← Real.rpow_mul ht]
  norm_num

/-- **Lemma B (cutoff limit, uniformly in the phase).** -/
theorem gpCutoffLimit : UnforcedLeray.Short.PartIIIb.Concrete.GPCutoffLimit := by
  intro P _ σ hs
  rcases hs with ⟨hsm, hper, C, hC⟩
  -- the exponent `q₀' = conjExp q₀ = 11/7`
  have hcj : (conjExp UnforcedLeray.B0412.q0E).toReal = 11 / 7 := by
    have hq0gt : (1 : ℝ≥0∞) < UnforcedLeray.B0412.q0E :=
      ENNReal.one_lt_ofReal.2 (by norm_num [UnforcedLeray.B0281.q0])
    have hq0ne : UnforcedLeray.B0412.q0E ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [UnforcedLeray.Short.PartIIa.toReal_conjExp hq0gt hq0ne, UnforcedLeray.B0412.q0E_toReal]
    norm_num
  have hcne : conjExp UnforcedLeray.B0412.q0E ≠ ⊤ := by
    intro h
    have h2 := hcj
    rw [h, ENNReal.toReal_top] at h2
    norm_num at h2
  have hcpos : conjExp UnforcedLeray.B0412.q0E ≠ 0 := by
    have h1 : (1 : ℝ≥0∞) ≤ conjExp UnforcedLeray.B0412.q0E :=
      (inferInstance : Fact (1 ≤ conjExp UnforcedLeray.B0412.q0E)).out
    exact (zero_lt_one.trans_le h1).ne'
  -- bounds on `σ`
  have hsσb : ∀ (τ : ℝ) (y : Space), ‖σ (τ, y)‖ ≤ |C| * (1 + ‖y‖) ^ (-2 : ℝ) := fun τ y =>
    ((hC τ y).1).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hgTb : ∀ (τ : ℝ) (y : Space), ‖gradT σ (τ, y)‖ ≤ |C| * (1 + ‖y‖) ^ (-3 : ℝ) := fun τ y =>
    ((hC τ y).2).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hcs : Continuous (gradT σ) := continuous_gradT_of_contDiff hsm
  have hcutc : ∀ n : ℕ, Continuous (gradT (cutoffMul σ n)) := fun n =>
    continuous_gradT_of_contDiff (isPhaseTest_cutoffMul hsm hper n).smooth
  -- the pointwise product-rule identity
  have hD : ∀ (n : ℕ) (τ : ℝ) (y : Space),
      gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y) =
        ((NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) y - 1 : ℝ) : ℂ) •
          gradT σ (τ, y) +
          σ (τ, y) • gaVec (NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1)) y := by
    intro n τ y
    have h := gradT_ofReal_mul_apply
      (a := NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1))
      (NavierStokesR3.ComparisonCutoffs.cutoff_smooth _) hsm (τ, y)
    unfold cutoffMul
    rw [h]
    dsimp only
    push_cast
    module
  -- the constant `K`
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |C| + 9 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * |C| :=
    ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact add_nonneg (abs_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) (NavierStokesR3.ComparisonCutoffs.derivativeConstant_pos 1).le)
        (abs_nonneg _))
  -- uniform pointwise bound
  have hDb : ∀ (n : ℕ) (τ : ℝ) (y : Space),
      ‖gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y)‖ ≤ K * (1 + ‖y‖) ^ (-3 : ℝ) := by
    intro n τ y
    have hR1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have ht : (0 : ℝ) < 1 + ‖y‖ := by positivity
    have hpow : (1 + ‖y‖) ^ (-2 : ℝ) * (1 + ‖y‖)⁻¹ = (1 + ‖y‖) ^ (-3 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
      norm_num
    have hA : ‖((NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) y - 1 : ℝ) : ℂ) •
        gradT σ (τ, y)‖ ≤ |C| * (1 + ‖y‖) ^ (-3 : ℝ) := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) y - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;>
          linarith [NavierStokesR3.ComparisonCutoffs.cutoff_nonneg ((n : ℝ) + 1) y,
            NavierStokesR3.ComparisonCutoffs.cutoff_le_one ((n : ℝ) + 1) y]
      calc |NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) y - 1| * ‖gradT σ (τ, y)‖
          ≤ 1 * (|C| * (1 + ‖y‖) ^ (-3 : ℝ)) :=
            mul_le_mul h1 (hgTb τ y) (norm_nonneg _) zero_le_one
        _ = |C| * (1 + ‖y‖) ^ (-3 : ℝ) := one_mul _
    have hB : ‖σ (τ, y) • gaVec (NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1)) y‖ ≤
        9 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * |C| * (1 + ‖y‖) ^ (-3 : ℝ) := by
      rw [norm_smul]
      calc ‖σ (τ, y)‖ * ‖gaVec (NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1)) y‖
          ≤ (|C| * (1 + ‖y‖) ^ (-2 : ℝ)) *
              (9 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * (1 + ‖y‖)⁻¹) :=
            mul_le_mul (hsσb τ y) (norm_gaVec_cutoff_le hR1 y) (norm_nonneg _) (by positivity)
        _ = 9 * NavierStokesR3.ComparisonCutoffs.derivativeConstant 1 * |C| *
              (1 + ‖y‖) ^ (-3 : ℝ) := by
            rw [← hpow]
            ring
    rw [hD n τ y]
    refine (norm_add_le _ _).trans ?_
    rw [hK]
    linarith [hA, hB]
  -- pointwise eventual vanishing
  have hev : ∀ (τ : ℝ) (y : Space), ∀ᶠ n : ℕ in atTop,
      gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y) = 0 := by
    intro τ y
    rw [Filter.eventually_atTop]
    refine ⟨⌈‖y‖⌉₊, fun n hn => ?_⟩
    have hy : ‖y‖ < (n : ℝ) + 1 := by
      have h1 : ‖y‖ ≤ (⌈‖y‖⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hc1 : NavierStokesR3.ComparisonCutoffs.cutoff ((n : ℝ) + 1) y = 1 :=
      NavierStokesR3.ComparisonCutoffs.cutoff_eq_one (by positivity) hy.le
    rw [hD n τ y, hc1, gaVec_cutoff_eq_zero (by positivity) hy]
    simp
  -- the dominating function and its integrability
  have hint : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(33 / 7 : ℝ))) volume := by
    apply integrable_one_add_norm
    have hfr : (Module.finrank ℝ Space : ℝ) = 3 := by simp
    rw [hfr]
    norm_num
  obtain ⟨Kr, hKr⟩ : ∃ Kr : ℝ, Kr = K ^ (11 / 7 : ℝ) := ⟨_, rfl⟩
  have hbfin : ∫⁻ y : Space, ENNReal.ofReal (Kr * (1 + ‖y‖) ^ (-(33 / 7 : ℝ))) ≠ ⊤ :=
    ((hint.const_mul Kr).lintegral_lt_top).ne
  have hbnd_pt : ∀ {E : Type} [NormedAddCommGroup E] (x : E) (y : Space),
      ‖x‖ ≤ K * (1 + ‖y‖) ^ (-3 : ℝ) →
      ‖x‖ₑ ^ (11 / 7 : ℝ) ≤ ENNReal.ofReal (Kr * (1 + ‖y‖) ^ (-(33 / 7 : ℝ))) := by
    intro E _ x y hx
    have ht : (0 : ℝ) < 1 + ‖y‖ := by positivity
    have h := enorm_rpow_le_of_norm_le x
      (mul_nonneg hK0 (Real.rpow_nonneg ht.le _)) hx
    rw [rpow_cube_mul hK0 (1 + ‖y‖) ht.le] at h
    rw [hKr]
    exact h
  -- the `L^{11/7}` limit for each phase
  have hτ : ∀ τ : ℝ, Tendsto (fun n : ℕ => eLpNorm
      (fun y => gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y))
      (conjExp UnforcedLeray.B0412.q0E) volume) atTop (𝓝 0) := by
    intro τ
    have hlint : Tendsto (fun n : ℕ =>
        ∫⁻ y, ‖gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y)‖ₑ ^ (11 / 7 : ℝ)) atTop (𝓝 0) := by
      have key := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := atTop)
        (F := fun (n : ℕ) (y : Space) =>
          ‖gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y)‖ₑ ^ (11 / 7 : ℝ))
        (f := fun _ : Space => (0 : ℝ≥0∞))
        (fun y => ENNReal.ofReal (Kr * (1 + ‖y‖) ^ (-(33 / 7 : ℝ))))
        (Filter.Eventually.of_forall fun n =>
          ((ENNReal.continuous_rpow_const (y := (11 / 7 : ℝ))).comp
            (continuous_enorm.comp
              (((hcutc n).comp (Continuous.prodMk continuous_const continuous_id)).sub
                (hcs.comp (Continuous.prodMk continuous_const continuous_id))))).measurable)
        (Filter.Eventually.of_forall fun n => ae_of_all _ fun y => hbnd_pt _ y (hDb n τ y))
        hbfin
        (ae_of_all _ fun y => by
          have h0 : ∀ᶠ n : ℕ in atTop,
              ‖gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y)‖ₑ ^ (11 / 7 : ℝ) = 0 := by
            filter_upwards [hev τ y] with n hn
            rw [hn, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
          exact tendsto_const_nhds.congr' (h0.mono fun n hn => hn.symm))
      simpa only [lintegral_zero] using key
    have hcomp : Tendsto (fun n : ℕ =>
        (∫⁻ y, ‖gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y)‖ₑ ^
            (conjExp UnforcedLeray.B0412.q0E).toReal) ^
          (1 / (conjExp UnforcedLeray.B0412.q0E).toReal)) atTop (𝓝 0) := by
      rw [hcj]
      have h0' : ((0 : ℝ≥0∞) ^ (1 / (11 / 7 : ℝ))) = 0 :=
        ENNReal.zero_rpow_of_pos (by norm_num)
      have h1 : Tendsto (fun n : ℕ =>
          (∫⁻ y, ‖gradT (cutoffMul σ n) (τ, y) - gradT σ (τ, y)‖ₑ ^ (11 / 7 : ℝ)) ^
            (1 / (11 / 7 : ℝ))) atTop (𝓝 ((0 : ℝ≥0∞) ^ (1 / (11 / 7 : ℝ)))) :=
        ((ENNReal.continuous_rpow_const (y := 1 / (11 / 7 : ℝ))).tendsto (0 : ℝ≥0∞)).comp hlint
      rw [h0'] at h1
      exact h1
    exact Tendsto.congr
      (fun n => (eLpNorm_eq_lintegral_rpow_enorm_toReal hcpos hcne).symm) hcomp
  -- the uniform bound through the dominating function
  have hGfin : eLpNorm (fun y : Space => K * (1 + ‖y‖) ^ (-3 : ℝ))
      (conjExp UnforcedLeray.B0412.q0E) volume < ⊤ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hcpos hcne, hcj]
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) hbfin.lt_top
    have ht : (0 : ℝ) < 1 + ‖y‖ := by positivity
    exact hbnd_pt _ y (le_of_eq (Real.norm_of_nonneg
      (mul_nonneg hK0 (Real.rpow_nonneg ht.le _))))
  refine ⟨fun τ _ => hτ τ, ⟨(eLpNorm (fun y : Space => K * (1 + ‖y‖) ^ (-3 : ℝ))
    (conjExp UnforcedLeray.B0412.q0E) volume).toReal, fun n τ _ => ?_⟩⟩
  rw [ENNReal.ofReal_toReal hGfin.ne]
  exact eLpNorm_mono_real fun y => hDb n τ y

end UnforcedLeray.Short.PartIIIb.Concrete
