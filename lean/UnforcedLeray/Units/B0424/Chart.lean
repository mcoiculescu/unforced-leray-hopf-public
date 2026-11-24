import UnforcedLeray.Lib.PhaseSpace.Charts
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# B0424, part 1: the two coordinate changes of the fixed-window estimate

Blueprint unit B0424 (`eq:free-stress-13`, `-14`, `-15`), `paper/main.tex` lines 7479–7517.
The proof (tex 7485–7510) passes from the phase variables `(τ, y)` to the variables `(t, x)`,
`τ = τ₀ + t`, `x = e^{t/2} y`, and then to `(θ, x)`, `θ = e^t`; "all coordinate Jacobians and
scalar factors are bounded above and below on this fixed window" (tex 7502–7503). This file
proves the two Jacobian identities as identities of measures on `ℝ × ℝ³`:

* `map_dilChart`: the spatial dilation `D(t, y) = (t, e^{t/2} y)` carries
  `e^{3t/2} dt dy` to `dt dx` (`dx = e^{3t/2} dy`);
* `map_expChart`: the time change `E(t, x) = (e^t, x)` carries `e^t dt dx` to `dθ dx`
  restricted to `θ > 0` (`dθ = e^t dt`).

Consequences for Bochner integrals, lower integrals and integrability (`integral_dilChart`,
`lintegral_dilChart'`, `integrable_dilChart_iff`, `integral_expChart`, `lintegral_expChart'`,
`integrable_expChart_iff`) hold without integrability hypotheses, since both maps are
measurable embeddings.

Status: infrastructure for `Units/B0424.lean`. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.B0424

open UnforcedLeray.PhaseSpace

/-! ### The spatial dilation `D(t, y) = (t, e^{t/2} y)` -/

/-- The dilation chart `D(t, y) = (t, e^{t/2} y)` (tex 7486: `x = e^{t/2} y`). -/
def dilChart (p : ℝ × Space) : ℝ × Space := (p.1, Real.exp (p.1 / 2) • p.2)

/-- Its inverse `(t, x) ↦ (t, e^{-t/2} x)`. -/
def dilChartInv (p : ℝ × Space) : ℝ × Space := (p.1, Real.exp (-(p.1 / 2)) • p.2)

theorem measurable_dilChart : Measurable dilChart := by
  unfold dilChart; fun_prop

theorem measurable_dilChartInv : Measurable dilChartInv := by
  unfold dilChartInv; fun_prop

/-- `D` as a measurable equivalence. -/
def dilEquiv : (ℝ × Space) ≃ᵐ (ℝ × Space) where
  toFun := dilChart
  invFun := dilChartInv
  left_inv p := by
    simp only [dilChart, dilChartInv, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_smul]
  right_inv p := by
    simp only [dilChart, dilChartInv, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      one_smul]
  measurable_toFun := measurable_dilChart
  measurable_invFun := measurable_dilChartInv

theorem dilEquiv_apply (p : ℝ × Space) : dilEquiv p = dilChart p := rfl

/-- The density `e^{3t/2}` of the dilation chart. -/
def rhoD (p : ℝ × Space) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (3 * p.1 / 2))

theorem measurable_rhoD : Measurable rhoD := by
  unfold rhoD; fun_prop

theorem exp_half_pow_three (t : ℝ) : Real.exp (t / 2) ^ 3 = Real.exp (3 * t / 2) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- `∫ e^{3t/2} G(t, e^{t/2} y) dt dy = ∫ G(t, x) dt dx` for measurable `G ≥ 0`. -/
theorem lintegral_dilChart (G : ℝ × Space → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ p, rhoD p * G (dilChart p) = ∫⁻ p, G p := by
  rw [Measure.volume_eq_prod, lintegral_prod (fun p => rhoD p * G (dilChart p))
    ((measurable_rhoD.mul (hG.comp measurable_dilChart)).aemeasurable),
    lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun t => ?_
  simp only [dilChart, rhoD]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h := lintegral_comp_affine (fun x => G (t, x)) (Real.exp_pos (t / 2)).ne' 0
  simp only [add_zero] at h
  rw [h, ← mul_assoc, exp_half_pow_three, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    abs_of_pos (inv_pos.2 (Real.exp_pos _)), mul_inv_cancel₀ (Real.exp_pos _).ne',
    ENNReal.ofReal_one, one_mul]

/-- **The Jacobian of `D`** (tex 7502): the image of `e^{3t/2} dt dy` under `D` is `dt dx`. -/
theorem map_dilChart : Measure.map dilChart (volume.withDensity rhoD) = volume := by
  ext s hs
  rw [Measure.map_apply measurable_dilChart hs, withDensity_apply _ (measurable_dilChart hs),
    ← lintegral_indicator (measurable_dilChart hs), ← lintegral_indicator_one hs,
    ← lintegral_dilChart _ (measurable_one.indicator hs)]
  refine lintegral_congr fun p => ?_
  by_cases hp : dilChart p ∈ s
  · simp [Set.indicator, hp, Set.mem_preimage]
  · simp [Set.indicator, hp, Set.mem_preimage]

/-- `∫ k = ∫ e^{3t/2} k(t, e^{t/2} y) dt dy` for every `k` (no integrability needed). -/
theorem integral_dilChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℝ × Space → E) :
    ∫ p, k p = ∫ p, Real.exp (3 * p.1 / 2) • k (dilChart p) := by
  conv_lhs => rw [← map_dilChart]
  rw [show (dilChart : ℝ × Space → ℝ × Space) = dilEquiv from rfl, integral_map_equiv,
    show rhoD = fun p => ((Real.exp (3 * p.1 / 2)).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul (by fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, dilEquiv_apply]

/-- Lower integrals: `∫⁻ G = ∫⁻ e^{3t/2} G(t, e^{t/2} y)` for every `G`. -/
theorem lintegral_dilChart' (G : ℝ × Space → ℝ≥0∞) :
    ∫⁻ p, G p = ∫⁻ p, rhoD p * G (dilChart p) := by
  conv_lhs => rw [← map_dilChart]
  rw [show (dilChart : ℝ × Space → ℝ × Space) = dilEquiv from rfl, lintegral_map_equiv,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ measurable_rhoD
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rfl

/-- Integrability through `D`. -/
theorem integrable_dilChart_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℝ × Space → E) :
    Integrable k ↔ Integrable (fun p => Real.exp (3 * p.1 / 2) • k (dilChart p)) := by
  conv_lhs => rw [← map_dilChart]
  rw [show (dilChart : ℝ × Space → ℝ × Space) = dilEquiv from rfl,
    dilEquiv.measurableEmbedding.integrable_map_iff,
    show rhoD = fun p => ((Real.exp (3 * p.1 / 2)).toNNReal : ℝ≥0∞) from rfl,
    integrable_withDensity_iff_integrable_smul (by fun_prop)]
  refine integrable_congr (Eventually.of_forall fun p => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, Function.comp_apply]

/-! ### The time change `E(t, x) = (e^t, x)` -/

/-- The time chart `E(t, x) = (e^t, x)` (tex 7493: `θ = e^t`). -/
def expChart (p : ℝ × Space) : ℝ × Space := (Real.exp p.1, p.2)

theorem measurable_expChart : Measurable expChart := by
  unfold expChart; fun_prop

theorem range_expChart : range expChart = Ioi (0 : ℝ) ×ˢ (univ : Set Space) := by
  ext ⟨θ, x⟩
  simp only [mem_range, expChart, Prod.mk.injEq, mem_prod, mem_Ioi, mem_univ, and_true]
  constructor
  · rintro ⟨⟨t, y⟩, h1, -⟩
    rw [← h1]; exact Real.exp_pos t
  · intro h
    exact ⟨⟨Real.log θ, x⟩, Real.exp_log h, rfl⟩

theorem measurableEmbedding_expChart : MeasurableEmbedding expChart := by
  refine MeasurableEmbedding.of_measurable_inverse (g := fun p : ℝ × Space => (Real.log p.1, p.2))
    measurable_expChart ?_ (by fun_prop) ?_
  · rw [range_expChart]; exact measurableSet_Ioi.prod MeasurableSet.univ
  · intro p; simp [expChart]

/-- The density `e^t` of the time chart. -/
def rhoE (p : ℝ × Space) : ℝ≥0∞ := ENNReal.ofReal (Real.exp p.1)

theorem measurable_rhoE : Measurable rhoE := by
  unfold rhoE; fun_prop

/-- `∫ e^t G(e^t, x) dt dx = ∫_{θ > 0} G(θ, x) dθ dx` for measurable `G ≥ 0`. -/
theorem lintegral_expChart (G : ℝ × Space → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ p, rhoE p * G (expChart p) = ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set Space), G p := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod (fun p => rhoE p * G (expChart p))
      ((measurable_rhoE.mul (hG.comp measurable_expChart)).aemeasurable),
    lintegral_prod _ hG.aemeasurable]
  set k : ℝ → ℝ≥0∞ := fun θ => ∫⁻ x, G (θ, x) with hk
  have hL : ∀ t : ℝ, ∫⁻ x, rhoE (t, x) * G (expChart (t, x)) =
      ENNReal.ofReal |Real.exp t| * k (Real.exp t) := by
    intro t
    simp only [rhoE, expChart, hk]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_of_pos (Real.exp_pos t)]
  simp_rw [hL]
  have h1 := lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn k
  rw [image_univ, Real.range_exp, Measure.restrict_univ] at h1
  rw [← h1]

/-- **The Jacobian of `E`** (tex 7502): the image of `e^t dt dx` under `E` is `dθ dx` on
`θ > 0`. -/
theorem map_expChart :
    Measure.map expChart (volume.withDensity rhoE) =
      volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) := by
  ext s hs
  rw [Measure.map_apply measurable_expChart hs, withDensity_apply _ (measurable_expChart hs),
    ← lintegral_indicator (measurable_expChart hs), ← lintegral_indicator_one hs,
    ← lintegral_expChart _ (measurable_one.indicator hs)]
  refine lintegral_congr fun p => ?_
  by_cases hp : expChart p ∈ s
  · simp [Set.indicator, hp, Set.mem_preimage]
  · simp [Set.indicator, hp, Set.mem_preimage]

/-- `∫_{θ>0} k = ∫ e^t k(e^t, x) dt dx` for every `k`. -/
theorem integral_expChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℝ × Space → E) :
    ∫ p in Ioi (0 : ℝ) ×ˢ (univ : Set Space), k p = ∫ p, Real.exp p.1 • k (expChart p) := by
  rw [← map_expChart, measurableEmbedding_expChart.integral_map,
    show rhoE = fun p => ((Real.exp p.1).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul (by fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le]

/-- Lower integrals through `E`. -/
theorem lintegral_expChart' (G : ℝ × Space → ℝ≥0∞) :
    ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set Space), G p = ∫⁻ p, rhoE p * G (expChart p) := by
  rw [← map_expChart, measurableEmbedding_expChart.lintegral_map,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ measurable_rhoE
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rfl

/-- Integrability through `E`. -/
theorem integrable_expChart_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℝ × Space → E) :
    IntegrableOn k (Ioi (0 : ℝ) ×ˢ (univ : Set Space)) ↔
      Integrable (fun p => Real.exp p.1 • k (expChart p)) := by
  rw [IntegrableOn, ← map_expChart, measurableEmbedding_expChart.integrable_map_iff,
    show rhoE = fun p => ((Real.exp p.1).toNNReal : ℝ≥0∞) from rfl,
    integrable_withDensity_iff_integrable_smul (by fun_prop)]
  refine integrable_congr (Eventually.of_forall fun p => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, Function.comp_apply]

/-! ### Phase translation -/

theorem shift_eq (τ₀ : ℝ) :
    (fun p : ℝ × Space => ((τ₀, 0) : ℝ × Space) + p) = fun p => (τ₀ + p.1, p.2) := by
  funext p; ext <;> simp

/-- Translation in the first variable preserves `dt dy`. -/
theorem integral_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (τ₀ : ℝ)
    (k : ℝ × Space → E) : ∫ p : ℝ × Space, k (τ₀ + p.1, p.2) = ∫ p, k p := by
  rw [Measure.volume_eq_prod]
  have h := integral_add_left_eq_self (μ := ((volume : Measure ℝ).prod (volume : Measure Space)))
    k ((τ₀, 0) : ℝ × Space)
  rw [← h]
  exact congrArg (fun F => ∫ p, k (F p) ∂((volume : Measure ℝ).prod volume)) (shift_eq τ₀).symm

theorem lintegral_shift (τ₀ : ℝ) (G : ℝ × Space → ℝ≥0∞) :
    ∫⁻ p : ℝ × Space, G (τ₀ + p.1, p.2) = ∫⁻ p, G p := by
  rw [Measure.volume_eq_prod]
  have h := lintegral_add_left_eq_self (μ := ((volume : Measure ℝ).prod (volume : Measure Space)))
    G ((τ₀, 0) : ℝ × Space)
  rw [← h]
  exact congrArg (fun F => ∫⁻ p, G (F p) ∂((volume : Measure ℝ).prod volume)) (shift_eq τ₀).symm

theorem integrable_shift_iff {E : Type*} [NormedAddCommGroup E] (τ₀ : ℝ)
    (k : ℝ × Space → E) : Integrable (fun p : ℝ × Space => k (τ₀ + p.1, p.2)) ↔ Integrable k := by
  rw [Measure.volume_eq_prod]
  have hmp := measurePreserving_add_left ((volume : Measure ℝ).prod (volume : Measure Space))
    ((τ₀, 0) : ℝ × Space)
  have h := hmp.integrable_comp_emb (measurableEmbedding_addLeft _) (g := k)
  rw [Function.comp_def] at h
  have e : (fun p : ℝ × Space => k (τ₀ + p.1, p.2)) = fun x => k ((τ₀, 0) + x) := by
    funext p; exact congrArg k (congrFun (shift_eq τ₀) p).symm
  rw [e]; exact h

end UnforcedLeray.B0424
