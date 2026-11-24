import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivRepAE
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.ComplexAdjoint

/-!
# Weighted Causal Flat Adjoint Operator Bounds (`CausalOperator`)

Provides the weighted backward causal integral `causalAdjointRep ν μ β w` and its `L²(measureH c)`
Bochner-integral representation via `B0224.T0adj`, yielding `MemLp` and the resolvent norm bound
`‖toLp (causalAdjointRep ν μ β w)‖ ≤ (μ.re + 1 / 4)⁻¹ * ‖hw.toLp w‖`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0225
  UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

namespace FlatAdjointElemAux

/-! ### 1. Weighted backward causal integral `causalAdjointRep` and `thetaWeight` -/

/-- Weighted backward causal integral with time weight `β : ℝ → ℂ`:
`if 0 < p.1 then ∫ t in Ioi 0, β t • flatAdjointSlice ν μ w t p else 0`. -/
def causalAdjointRep (ν : ℝ) (μ : ℂ) (β : ℝ → ℂ) (w : Profile → MeridC) (p : Profile) : MeridC :=
  if 0 < p.1 then ∫ t : ℝ in Ioi (0 : ℝ), β t • flatAdjointSlice ν μ w t p else 0

/-- Bounded continuous weight `thetaWeight l t = (max 0 (1 - e^{-t}))^l` on `ℝ`, equal to
`(1 - e^{-t})^l` for `t > 0`. -/
def thetaWeight (l : ℕ) (t : ℝ) : ℂ :=
  ((max (0 : ℝ) (1 - Real.exp (-t)) ^ l : ℝ) : ℂ)

theorem thetaWeight_zero : thetaWeight 0 = fun _ => (1 : ℂ) := by
  funext t
  simp [thetaWeight]

theorem causalAdjointRep_thetaWeight_zero (ν : ℝ) (μ : ℂ) (w : Profile → MeridC) :
    causalAdjointRep ν μ (thetaWeight 0) w = flatAdjointRep ν μ w := by
  funext p
  simp [causalAdjointRep, flatAdjointRep, thetaWeight_zero]

theorem continuous_thetaWeight (l : ℕ) : Continuous (thetaWeight l) := by
  unfold thetaWeight
  fun_prop

theorem thetaWeight_of_pos (l : ℕ) {t : ℝ} (ht : 0 < t) :
    thetaWeight l t = (((1 - Real.exp (-t)) ^ l : ℝ) : ℂ) := by
  unfold thetaWeight
  have hexp : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [max_eq_right (by linarith)]

theorem norm_thetaWeight_le (l : ℕ) (t : ℝ) : ‖thetaWeight l t‖ ≤ 1 := by
  unfold thetaWeight
  rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (le_max_left 0 _) l)]
  refine pow_le_one₀ (le_max_left 0 _) ?_
  refine max_le (by norm_num) ?_
  have hexp : 0 < Real.exp (-t) := Real.exp_pos (-t)
  linarith

/-- Multiplication of a profile by `(ν * s)^l`. -/
def nuSMul (ν : ℝ) (l : ℕ) (w : Profile → MeridC) : Profile → MeridC :=
  fun p => (((ν * p.1) ^ l : ℝ) : ℂ) • w p

@[simp]
theorem nuSMul_zero (ν : ℝ) (w : Profile → MeridC) : nuSMul ν 0 w = w := by
  funext p
  simp [nuSMul]

theorem nuSMul_one_apply (ν : ℝ) (w : Profile → MeridC) (p : Profile) :
    nuSMul ν 1 w p = (ν * p.1 : ℝ) • w p := by
  simp only [nuSMul, pow_one]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (ν * p.1) (w p)).symm

/-- Exact commutation of `(ν * p.1 * (e^t - 1))^l` with `flatAdjointSlice` for `t > 0`:
since `ν * p.1 * (e^t - 1) = (1 - e^{-t}) * (ν * (e^t * p.1))`,
`((ν * p.1 * (e^t - 1))^l) • flatAdjointSlice ν μ w t p =
  thetaWeight l t • flatAdjointSlice ν μ (nuSMul ν l w) t p`. -/
theorem heatTimeAdj_pow_smul_flatAdjointSlice (ν : ℝ) (μ : ℂ) (l : ℕ) (w : Profile → MeridC)
    {t : ℝ} (ht : 0 < t) (p : Profile) :
    (((ν * p.1 * (Real.exp t - 1)) ^ l : ℝ) : ℂ) • flatAdjointSlice ν μ w t p =
      thetaWeight l t • flatAdjointSlice ν μ (nuSMul ν l w) t p := by
  rw [thetaWeight_of_pos l ht]
  simp only [flatAdjointSlice, nuSMul]
  rw [t0c_planeHeat_smul_C (ν * p.1 * (Real.exp t - 1))
    (((ν * (Real.exp t * p.1)) ^ l : ℝ) : ℂ) (fun y => w (Real.exp t * p.1, y))]
  rw [smul_comm (Complex.exp _) ((((ν * (Real.exp t * p.1)) ^ l : ℝ) : ℂ)),
    ← mul_smul (((1 - Real.exp (-t)) ^ l : ℝ) : ℂ)]
  congr 1
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h1 : ν * p.1 * (Real.exp t - 1) = (1 - Real.exp (-t)) * (ν * (Real.exp t * p.1)) := by
    linear_combination (ν * p.1) * hexp
  rw [h1, mul_pow]
  push_cast
  rfl

/-! ### 2. Joint measurability and Bochner integrability of `T0adj` -/

/-- Joint representative `(t, p) ↦ t0adjFormula c ν t F p` on `ℝ × Profile`. -/
def jointAdjRep (c ν : ℝ) (F : Profile → MeridC) (x : ℝ × Profile) : MeridC :=
  t0adjFormula c ν x.1 F x.2

theorem jointAdjRep_eq_smul_jointRep (c ν : ℝ) (F : Profile → MeridC) (x : ℝ × Profile) :
    jointAdjRep c ν F x = Real.exp (-x.1 / 2) • B0225.jointRep c (-ν) F (-x.1, x.2) := by
  simp only [jointAdjRep, t0adjFormula, B0225.jointRep, neg_neg]
  have hθ : ν * x.2.1 * (Real.exp x.1 - 1) = -ν * x.2.1 * (1 - Real.exp x.1) := by ring
  rw [hθ]

theorem stronglyMeasurable_jointAdjRep (c ν : ℝ) {F : Profile → MeridC}
    (hF : StronglyMeasurable F) : StronglyMeasurable (jointAdjRep c ν F) := by
  have heq : jointAdjRep c ν F =
      fun x : ℝ × Profile => Real.exp (-x.1 / 2) • B0225.jointRep c (-ν) F (-x.1, x.2) :=
    funext (jointAdjRep_eq_smul_jointRep c ν F)
  rw [heq]
  refine (Continuous.stronglyMeasurable (by fun_prop :
    Continuous fun x : ℝ × Profile => Real.exp (-x.1 / 2))).smul ?_
  exact (B0225.stronglyMeasurable_jointRep c (-ν) hF).comp_measurable
    (measurable_fst.neg.prodMk measurable_snd)

theorem T0adj_ae_jointAdjRep {c : ℝ} (hc : 0 < c) (ν t : ℝ) (W : HSpace c MeridC)
    {w : Profile → MeridC} (hw : StronglyMeasurable w) (hWw : (W : Profile → MeridC) =ᵐ[measureH c] w) :
    (B0224.T0adj hc ν t W : Profile → MeridC) =ᵐ[measureH c] fun p => jointAdjRep c ν w (t, p) :=
  t0adj_rep_ae c ν hc t W w hw hWw

theorem memLp_jointAdjRep {c : ℝ} (hc : 0 < c) (ν t : ℝ) (W : HSpace c MeridC)
    {w : Profile → MeridC} (hw : StronglyMeasurable w) (hWw : (W : Profile → MeridC) =ᵐ[measureH c] w) :
    MemLp (fun p => jointAdjRep c ν w (t, p)) 2 (measureH c) :=
  (Lp.memLp _).ae_eq (T0adj_ae_jointAdjRep hc ν t W hw hWw)

theorem T0adj_path_eq {c : ℝ} (hc : 0 < c) (ν : ℝ) (W : HSpace c MeridC) :
    (fun t => B0224.T0adj hc ν t W) =
      BochnerTime.toPathLq 2 (measureH c) (jointAdjRep c ν (W : Profile → MeridC)) := by
  funext t
  have h := T0adj_ae_jointAdjRep hc ν t W (Lp.stronglyMeasurable W) EventuallyEq.rfl
  have hm := memLp_jointAdjRep hc ν t W (Lp.stronglyMeasurable W) EventuallyEq.rfl
  rw [BochnerTime.toPathLq_of_memLp hm]
  calc B0224.T0adj hc ν t W
      = (Lp.memLp (B0224.T0adj hc ν t W)).toLp (B0224.T0adj hc ν t W) := (Lp.toLp_coeFn _ _).symm
    _ = hm.toLp _ := (MemLp.toLp_eq_toLp_iff _ _).2 h

theorem stronglyMeasurable_T0adj_path {c : ℝ} (hc : 0 < c) (ν : ℝ) (W : HSpace c MeridC) :
    StronglyMeasurable fun t : ℝ => B0224.T0adj hc ν t W := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  rw [T0adj_path_eq]
  exact BochnerTime.stronglyMeasurable_toPathLq
    (stronglyMeasurable_jointAdjRep c ν (Lp.stronglyMeasurable W))

/-- `HSpace c MeridC`-valued Laplace integrand `(e^{-μ̄ t} * β t) • T0adj hc ν t W`. -/
def lapT0adj {c : ℝ} (hc : 0 < c) (ν : ℝ) (μ : ℂ) (β : ℝ → ℂ)
    (W : HSpace c MeridC) (t : ℝ) : HSpace c MeridC :=
  (Complex.exp (-(starRingEnd ℂ μ * t)) * β t) • B0224.T0adj hc ν t W

theorem norm_cexp_neg_conj_mul (μ : ℂ) (t : ℝ) :
    ‖Complex.exp (-(starRingEnd ℂ μ * (t : ℂ)))‖ = Real.exp (-(μ.re * t)) := by
  rw [Infra.ExpSemigroup.norm_cexp_neg_mul, Complex.conj_re]

theorem norm_lapT0adj_le {c : ℝ} (hc : 0 < c) (ν : ℝ) (μ : ℂ) {β : ℝ → ℂ}
    (hβ : ∀ t : ℝ, ‖β t‖ ≤ 1) (W : HSpace c MeridC) (t : ℝ) :
    ‖lapT0adj hc ν μ β W t‖ ≤ ‖W‖ * Real.exp (-(μ.re + 1 / 4) * t) := by
  have hT : ‖(B0224.T0adj hc ν t : HSpace c MeridC →L[ℝ] HSpace c MeridC)‖ ≤ Real.exp (-t / 4) :=
    B0224.norm_T0adj_le hc ν t
  have h1 : ‖B0224.T0adj hc ν t W‖ ≤ Real.exp (-t / 4) * ‖W‖ :=
    (B0224.T0adj hc ν t : HSpace c MeridC →L[ℝ] HSpace c MeridC).le_of_opNorm_le hT W
  rw [lapT0adj, norm_smul, norm_mul, norm_cexp_neg_conj_mul]
  have h2 : Real.exp (-(μ.re * t)) * ‖β t‖ ≤ Real.exp (-(μ.re * t)) * 1 :=
    mul_le_mul_of_nonneg_left (hβ t) (Real.exp_pos _).le
  rw [mul_one] at h2
  calc (Real.exp (-(μ.re * t)) * ‖β t‖) * ‖B0224.T0adj hc ν t W‖
      ≤ Real.exp (-(μ.re * t)) * (Real.exp (-t / 4) * ‖W‖) :=
        mul_le_mul h2 h1 (norm_nonneg _) (Real.exp_pos _).le
    _ = ‖W‖ * Real.exp (-(μ.re + 1 / 4) * t) := by
        rw [show -(μ.re + 1 / 4) * t = -(μ.re * t) + -t / 4 by ring, Real.exp_add]
        ring

theorem integrableOn_lapT0adj {c : ℝ} (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {β : ℝ → ℂ} (hβ_cont : Continuous β) (hβ_le : ∀ t : ℝ, ‖β t‖ ≤ 1) (W : HSpace c MeridC) :
    IntegrableOn (lapT0adj hc ν μ β W) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hμ).const_mul ‖W‖) ?_
    (Eventually.of_forall fun t => norm_lapT0adj_le hc ν μ hβ_le W t)
  exact ((Continuous.stronglyMeasurable (by fun_prop :
    Continuous fun t : ℝ => Complex.exp (-(starRingEnd ℂ μ * t)) * β t)).smul
      (stronglyMeasurable_T0adj_path hc ν W)).aestronglyMeasurable

theorem norm_integral_lapT0adj_le {c : ℝ} (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {β : ℝ → ℂ} (hβ_le : ∀ t : ℝ, ‖β t‖ ≤ 1) (W : HSpace c MeridC) :
    ‖∫ t in Ioi 0, lapT0adj hc ν μ β W t‖ ≤ (μ.re + 1 / 4)⁻¹ * ‖W‖ := by
  refine (norm_integral_le_of_norm_le
    ((exp_neg_integrableOn_Ioi 0 hμ).const_mul ‖W‖)
    (Eventually.of_forall fun t => norm_lapT0adj_le hc ν μ hβ_le W t)).trans (le_of_eq ?_)
  rw [Infra.ExpSemigroup.integral_exp_bound hμ, div_eq_inv_mul]

/-! ### 3. Pointwise identification with `causalAdjointRep` and `L²(measureH c)` bound -/

/-- Joint integrand `(p, t) ↦ (e^{-μ̄ t} * β t) • t0adjFormula c ν t w p` on `Profile × ℝ`. -/
def lapAdjRep (c ν : ℝ) (μ : ℂ) (β : ℝ → ℂ) (w : Profile → MeridC) (x : Profile × ℝ) : MeridC :=
  (Complex.exp (-(starRingEnd ℂ μ * x.2)) * β x.2) • jointAdjRep c ν w (x.2, x.1)

theorem lapAdjRep_eq_flatAdjointSlice {c : ℝ} (ν : ℝ) (μ : ℂ) (β : ℝ → ℂ)
    {w : Profile → MeridC} (hw_per : QPeriodic c w) (p : Profile) (t : ℝ) :
    lapAdjRep c ν μ β w (p, t) = β t • flatAdjointSlice ν μ w t p := by
  unfold lapAdjRep jointAdjRep t0adjFormula flatAdjointSlice
  dsimp only
  rw [B0220.periodize_of_periodic w hw_per]
  have hr : ∀ x : MeridC, (Real.exp (-t / 2) : ℝ) • x = ((Real.exp (-t / 2) : ℝ) : ℂ) • x :=
    fun x => RCLike.real_smul_eq_coe_smul (K := ℂ) (Real.exp (-t / 2)) x
  rw [hr, smul_smul, smul_smul]
  congr 1
  have hexp : Complex.exp (-((starRingEnd ℂ μ + (1 / 2 : ℂ)) * (t : ℂ))) =
      Complex.exp (-(starRingEnd ℂ μ * (t : ℂ))) * ((Real.exp (-t / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

theorem stronglyMeasurable_lapAdjRep (c ν : ℝ) (μ : ℂ) {β : ℝ → ℂ} (hβ_cont : Continuous β)
    {w : Profile → MeridC} (hw : StronglyMeasurable w) :
    StronglyMeasurable (lapAdjRep c ν μ β w) := by
  refine (Continuous.stronglyMeasurable (by fun_prop :
    Continuous fun x : Profile × ℝ => Complex.exp (-(starRingEnd ℂ μ * x.2)) * β x.2)).smul ?_
  exact (stronglyMeasurable_jointAdjRep c ν hw).comp_measurable measurable_swap

theorem integrable_lapAdjRep {c : ℝ} (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {β : ℝ → ℂ} (hβ_cont : Continuous β) (hβ_le : ∀ t : ℝ, ‖β t‖ ≤ 1)
    (W : HSpace c MeridC) {w : Profile → MeridC} (hw : StronglyMeasurable w)
    (hWw : (W : Profile → MeridC) =ᵐ[measureH c] w) {A : Set Profile} (hA : measureH c A < ∞) :
    Integrable (lapAdjRep c ν μ β w)
      (((measureH c).restrict A).prod (volume.restrict (Ioi 0))) := by
  have hK := stronglyMeasurable_lapAdjRep c ν μ hβ_cont hw
  rw [integrable_prod_iff' hK.aestronglyMeasurable]
  set C : ℝ := (measureH c A).toReal ^ (1 - 1 / (2 : ℝ≥0∞).toReal)
  have hC0 : 0 ≤ C := by positivity
  constructor
  · refine Eventually.of_forall fun t => ?_
    have hm := memLp_jointAdjRep hc ν t W hw hWw
    exact (B0225.integrableOn_of_memLp' hm hA).smul (Complex.exp (-(starRingEnd ℂ μ * t)) * β t)
  · refine Integrable.mono'
      ((exp_neg_integrableOn_Ioi 0 hμ).const_mul (C * ‖W‖)) ?_ ?_
    · exact (hK.norm.integral_prod_left' (μ := (measureH c).restrict A)).aestronglyMeasurable
    · refine Eventually.of_forall fun t => ?_
      have h := T0adj_ae_jointAdjRep hc ν t W hw hWw
      have hT : ‖(B0224.T0adj hc ν t : HSpace c MeridC →L[ℝ] HSpace c MeridC)‖ ≤
          Real.exp (-t / 4) := B0224.norm_T0adj_le hc ν t
      have h1 : ‖B0224.T0adj hc ν t W‖ ≤ Real.exp (-t / 4) * ‖W‖ :=
        (B0224.T0adj hc ν t : HSpace c MeridC →L[ℝ] HSpace c MeridC).le_of_opNorm_le hT W
      have h2 : ∫ p in A, ‖lapAdjRep c ν μ β w (p, t)‖ ∂measureH c =
          (Real.exp (-(μ.re * t)) * ‖β t‖) *
            ∫ p in A, ‖(B0224.T0adj hc ν t W : Profile → MeridC) p‖ ∂measureH c := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [h] with p hp
        rw [lapAdjRep, norm_smul, norm_mul, norm_cexp_neg_conj_mul, hp]
      have h3 := B0225.integral_norm_le_Lp (B0224.T0adj hc ν t W) hA
      have hβ1 : Real.exp (-(μ.re * t)) * ‖β t‖ ≤ Real.exp (-(μ.re * t)) := by
        calc Real.exp (-(μ.re * t)) * ‖β t‖ ≤ Real.exp (-(μ.re * t)) * 1 :=
              mul_le_mul_of_nonneg_left (hβ_le t) (Real.exp_pos _).le
          _ = Real.exp (-(μ.re * t)) := mul_one _
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), h2]
      calc (Real.exp (-(μ.re * t)) * ‖β t‖) *
            ∫ p in A, ‖(B0224.T0adj hc ν t W : Profile → MeridC) p‖ ∂measureH c
          ≤ Real.exp (-(μ.re * t)) * (C * (Real.exp (-t / 4) * ‖W‖)) := by
            refine mul_le_mul hβ1 (h3.trans ?_) (integral_nonneg fun _ => norm_nonneg _)
              (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_left h1 hC0
        _ = C * ‖W‖ * Real.exp (-(μ.re + 1 / 4) * t) := by
            rw [show -(μ.re + 1 / 4) * t = -(μ.re * t) + -t / 4 by ring, Real.exp_add]
            ring

/-- Pointwise evaluation of the Bochner integral `∫ t in Ioi 0, lapT0adj hc ν μ β W t` as
`causalAdjointRep ν μ β w`. -/
theorem integral_lapT0adj_ae_eq {c : ℝ} (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {β : ℝ → ℂ} (hβ_cont : Continuous β) (hβ_le : ∀ t : ℝ, ‖β t‖ ≤ 1)
    (W : HSpace c MeridC) {w : Profile → MeridC} (hw : StronglyMeasurable w)
    (hw_per : QPeriodic c w) (hWw : (W : Profile → MeridC) =ᵐ[measureH c] w) :
    ((∫ t in Ioi 0, lapT0adj hc ν μ β W t : HSpace c MeridC) : Profile → MeridC)
      =ᵐ[measureH c] causalAdjointRep ν μ β w := by
  have hae_int : ((∫ t in Ioi 0, lapT0adj hc ν μ β W t : HSpace c MeridC) : Profile → MeridC)
      =ᵐ[measureH c] fun p => ∫ t : ℝ in Ioi 0, lapAdjRep c ν μ β w (p, t) := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
      (fun A _ hA => B0225.integrableOn_of_memLp' (Lp.memLp _) hA)
      (fun A _ hA =>
        (integrable_lapAdjRep hc ν hμ hβ_cont hβ_le W hw hWw hA).integral_prod_left)
      (fun A _ hA => ?_)
    have hint := integrable_lapAdjRep hc ν hμ hβ_cont hβ_le W hw hWw hA
    have hswap := integral_integral_swap (f := fun p t => lapAdjRep c ν μ β w (p, t)) hint
    change ∫ p in A, ((∫ t in Ioi 0, lapT0adj hc ν μ β W t : HSpace c MeridC) :
        Profile → MeridC) p ∂measureH c =
      ∫ p in A, ∫ t in Ioi 0, lapAdjRep c ν μ β w (p, t) ∂volume ∂measureH c
    rw [hswap, ← B0225.setIntL_apply A hA]
    rw [← (B0225.setIntL A hA).integral_comp_comm
      (integrableOn_lapT0adj hc ν hμ hβ_cont hβ_le W)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have h := T0adj_ae_jointAdjRep hc ν t W hw hWw
    change B0225.setIntL A hA (lapT0adj hc ν μ β W t) = _
    rw [lapT0adj, map_smul, B0225.setIntL_apply, ← integral_smul]
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h] with p hp
    rw [lapAdjRep, hp]
  filter_upwards [hae_int, ae_measureH_age_pos c] with p hp hp_pos
  simp only [hp, causalAdjointRep, hp_pos, ↓reduceIte]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  exact lapAdjRep_eq_flatAdjointSlice ν μ β hw_per p t

/-- `MemLp` of `causalAdjointRep ν μ β w` on `measureH c`. -/
theorem memLp_causalAdjointRep {c : ℝ} (hc : 0 < c) (ν : ℝ) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    {β : ℝ → ℂ} (hβ_cont : Continuous β) (hβ_le : ∀ t : ℝ, ‖β t‖ ≤ 1)
    {w : Profile → MeridC} (hw_meas : StronglyMeasurable w) (hw_per : QPeriodic c w)
    (hw : MemLp w 2 (measureH c)) :
    MemLp (causalAdjointRep ν μ β w) 2 (measureH c) :=
  (Lp.memLp (∫ t in Ioi 0, lapT0adj hc ν μ β (hw.toLp w) t)).ae_eq
    (integral_lapT0adj_ae_eq hc ν hμ hβ_cont hβ_le (hw.toLp w) hw_meas hw_per hw.coeFn_toLp)

/-- `L²(measureH c)` norm bound for `causalAdjointRep ν μ β w`. -/
theorem norm_causalAdjointRep_le {c : ℝ} (hc : 0 < c) (ν : ℝ) {γs : ℝ} (hγs : 0 < γs)
    {μ : ℂ} (hμγ : γs ≤ μ.re + 1 / 4)
    {β : ℝ → ℂ} (hβ_cont : Continuous β) (hβ_le : ∀ t : ℝ, ‖β t‖ ≤ 1)
    {w : Profile → MeridC} (hw_meas : StronglyMeasurable w) (hw_per : QPeriodic c w)
    (hw : MemLp w 2 (measureH c)) :
    ‖(memLp_causalAdjointRep hc ν (hγs.trans_le hμγ) hβ_cont hβ_le hw_meas hw_per hw).toLp
      (causalAdjointRep ν μ β w)‖ ≤ γs⁻¹ * ‖hw.toLp w‖ := by
  have hμ : 0 < μ.re + 1 / 4 := hγs.trans_le hμγ
  set m := memLp_causalAdjointRep hc ν hμ hβ_cont hβ_le hw_meas hw_per hw
  set I : HSpace c MeridC := ∫ t in Ioi 0, lapT0adj hc ν μ β (hw.toLp w) t
  have heq : m.toLp (causalAdjointRep ν μ β w) = I := by
    apply Lp.ext
    exact m.coeFn_toLp.trans
      (integral_lapT0adj_ae_eq hc ν hμ hβ_cont hβ_le (hw.toLp w) hw_meas hw_per hw.coeFn_toLp).symm
  rw [heq]
  calc ‖I‖ ≤ (μ.re + 1 / 4)⁻¹ * ‖hw.toLp w‖ :=
        norm_integral_lapT0adj_le hc ν hμ hβ_le (hw.toLp w)
    _ ≤ γs⁻¹ * ‖hw.toLp w‖ :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hγs hμγ) (norm_nonneg _)

end FlatAdjointElemAux

end UnforcedLeray.Short.PartIIa
