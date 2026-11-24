import UnforcedLeray.Loc.L10Nonlinear
import UnforcedLeray.Lib.HeatR3

/-!
# `H-Residual`, helpers: weights and `L²` bounds

Support for `Loc/Hyp/ResidualForce.lean` (the hypothesis `ResidualForce` of
`Loc/L10Nonlinear.lean`, `paper/main.tex` lines 474–491, blueprint unit B0722).

With `p = 1 + |y|`, `q = 1 + δ²|y|` (`δ = e^{τ/4}`, so `δ² = e^{τ/2} = √t`), the products of
the profiles `H`, `K_loc` and their derivatives are bounded by the weight
`ψ_δ = 2δ²p⁻² + δ⁵q⁻³` (this file, `Product.lean`). The two facts proved here are:

* the elementary inequality `δ⁴/(pq²) ≤ δ²/p³ + δ⁵/q³` (split at `δp = q`), which replaces the
  inner-ball/outer-region split of lines 479–484 by one pointwise bound;
* `‖ψ_δ‖_{L²(ℝ³)} ≤ cPsi · δ²` (`psi_L2`): `∫ p⁻⁴ < ∞`, `∫ q⁻⁶ = δ⁻⁶ ∫ p⁻⁶` by the scaling
  `y = δ⁻²x`. This is the source of the factor `e^{τ/2}` in `loc:eq:force-bound`.

Main declarations: `memLp_l2Norm_le_of_sq`, `case_bound`, `psi_L2`, `psi_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.ResidualForceHyp

open UnforcedLeray.Blueprint

/-! ## `L²` from a pointwise square bound -/

/-- If `|f|² ≤ g` with `g ∈ L¹`, then `f ∈ L²` and `‖f‖_{L²} ≤ (∫ g)^{1/2}`. -/
theorem memLp_l2Norm_le_of_sq {f : SpatialField} {g : Space → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : Integrable g) (hb : ∀ y, ‖f y‖ ^ 2 ≤ g y) :
    MemLp f 2 volume ∧ l2Norm f ≤ Real.sqrt (∫ y, g y) := by
  have hint : Integrable (fun y => ‖f y‖ ^ 2) :=
    hg.mono' (hf.norm.pow 2) (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hb y)
  have hmem : MemLp f 2 volume := (memLp_two_iff_integrable_sq_norm hf).mpr hint
  refine ⟨hmem, ?_⟩
  unfold l2Norm
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [h2]
  have hI : ∫ a : Space, ‖f a‖ ^ (2 : ℝ) = ∫ a : Space, ‖f a‖ ^ 2 := by
    congr 1
    funext a
    exact Real.rpow_two _
  rw [hI]
  have hI0 : 0 ≤ ∫ a : Space, ‖f a‖ ^ 2 := integral_nonneg fun a => sq_nonneg _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI0 _), Real.sqrt_eq_rpow,
    show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  exact Real.rpow_le_rpow hI0 (integral_mono hint hg hb) (by norm_num)

/-! ## Weights -/

theorem finrank_space : Module.finrank ℝ Space = 3 := by simp [Space]

/-- `(1 + |y|)^{-n}` is integrable on `ℝ³` for `n > 3`. -/
theorem integrable_inv_pow {n : ℕ} (hn : 3 < n) :
    Integrable (fun y : Space => 1 / (1 + ‖y‖) ^ n) := by
  have h := integrable_one_add_norm (E := Space) (μ := volume) (r := (n : ℝ))
    (by rw [finrank_space]; exact_mod_cast hn)
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, one_div]

/-- `∫ (1 + c|y|)^{-n} dy = c^{-3} ∫ (1 + |x|)^{-n} dx` (`c > 0`). -/
theorem integral_inv_pow_scaled (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ y : Space, 1 / (1 + c * ‖y‖) ^ n = (c ^ 3)⁻¹ * ∫ x : Space, 1 / (1 + ‖x‖) ^ n := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
    (fun x : Space => 1 / (1 + ‖x‖) ^ n) c (hR := hc.le)
  rw [finrank_space] at h
  simp only [norm_smul, Real.norm_of_nonneg hc.le, smul_eq_mul] at h
  exact h

theorem integrable_inv_pow_scaled {n : ℕ} (hn : 3 < n) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : Space => 1 / (1 + c * ‖y‖) ^ n) := by
  have h := (integrable_inv_pow hn).comp_smul hc.ne'
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [norm_smul, Real.norm_of_nonneg hc.le]

/-- `∫ (1 + |x|)^{-4}`. -/
def c4 : ℝ := ∫ x : Space, 1 / (1 + ‖x‖) ^ 4

/-- `∫ (1 + |x|)^{-6}`. -/
def c6 : ℝ := ∫ x : Space, 1 / (1 + ‖x‖) ^ 6

theorem c4_nonneg : 0 ≤ c4 := integral_nonneg fun x => by positivity
theorem c6_nonneg : 0 ≤ c6 := integral_nonneg fun x => by positivity

/-- The constant of `psi_L2`. -/
def cPsi : ℝ := Real.sqrt (2 * (4 * c4 + c6))

theorem cPsi_nonneg : 0 ≤ cPsi := Real.sqrt_nonneg _

/-! ## The pointwise inequality -/

/-- `δ⁴/(pq²) ≤ δ²/p³ + δ⁵/q³` for positive `δ, p, q`: split at `δp = q`. -/
theorem case_bound {δ p q : ℝ} (hδ : 0 < δ) (hp : 0 < p) (hq : 0 < q) :
    δ ^ 4 / (p * q ^ 2) ≤ δ ^ 2 / p ^ 3 + δ ^ 5 / q ^ 3 := by
  rcases le_or_gt (δ * p) q with h | h
  · have h2 : (δ * p) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) h 2
    have h' : δ ^ 4 / (p * q ^ 2) ≤ δ ^ 2 / p ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : δ ^ 2 * p * (δ * p) ^ 2 ≤ δ ^ 2 * p * q ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith [h3]
    have : 0 ≤ δ ^ 5 / q ^ 3 := by positivity
    linarith
  · have h' : δ ^ 4 / (p * q ^ 2) ≤ δ ^ 5 / q ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 : δ ^ 4 * q ^ 2 * q ≤ δ ^ 4 * q ^ 2 * (δ * p) :=
        mul_le_mul_of_nonneg_left h.le (by positivity)
      nlinarith [h3]
    have : 0 ≤ δ ^ 2 / p ^ 3 := by positivity
    linarith

/-- The weight `ψ_δ(y) = 2δ²(1+|y|)⁻² + δ⁵(1+δ²|y|)⁻³`. -/
def psi (δ : ℝ) (y : Space) : ℝ := 2 * δ ^ 2 / (1 + ‖y‖) ^ 2 + δ ^ 5 / (1 + δ ^ 2 * ‖y‖) ^ 3

theorem psi_nonneg {δ : ℝ} (hδ : 0 < δ) (y : Space) : 0 ≤ psi δ y := by
  unfold psi; positivity

/-- `δ²(1 + |y|) ≤ 1 + δ²|y|` for `δ ≤ 1`. -/
theorem sq_mul_le_q {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (y : Space) :
    δ ^ 2 * (1 + ‖y‖) ≤ 1 + δ ^ 2 * ‖y‖ := by
  have : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  nlinarith [norm_nonneg y]

/-- `ψ_δ ≤ 3(1 + |y|)⁻²` for `0 < δ ≤ 1`. -/
theorem psi_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (y : Space) :
    psi δ y ≤ 3 / (1 + ‖y‖) ^ 2 := by
  unfold psi
  set p := 1 + ‖y‖ with hp
  set q := 1 + δ ^ 2 * ‖y‖ with hq
  have hp0 : 0 < p := by positivity
  have hq1 : 1 ≤ q := by have := norm_nonneg y; nlinarith [sq_nonneg δ]
  have hq0 : 0 < q := by linarith
  have hδ2 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hdq : δ ^ 2 * p ≤ q := sq_mul_le_q hδ hδ1 y
  have h1 : 2 * δ ^ 2 / p ^ 2 ≤ 2 / p ^ 2 := by gcongr; linarith
  have h2 : δ ^ 5 / q ^ 3 ≤ 1 / p ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- `δ⁵ p² ≤ q³`: `δ⁴p² ≤ q²` and `δ ≤ 1 ≤ q`
    have h3 : (δ ^ 2 * p) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) hdq 2
    have h4 : δ * q ^ 2 ≤ q * q ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [h3, h4, pow_pos hδ 4, pow_pos hp0 2]
  have : 2 / p ^ 2 + 1 / p ^ 2 = 3 / p ^ 2 := by ring
  linarith

/-- **`‖ψ_δ‖_{L²} ≤ cPsi δ²`.** If `|f| ≤ A ψ_δ` pointwise then `f ∈ L²` and
`‖f‖_{L²} ≤ A · cPsi · δ²`. -/
theorem psi_L2 {f : SpatialField} (hf : AEStronglyMeasurable f volume) {A δ : ℝ} (hA : 0 ≤ A)
    (hδ : 0 < δ) (hb : ∀ y, ‖f y‖ ≤ A * psi δ y) :
    MemLp f 2 volume ∧ l2Norm f ≤ A * cPsi * δ ^ 2 := by
  set g : Space → ℝ := fun y => 2 * A ^ 2 * (4 * δ ^ 4 * (1 / (1 + ‖y‖) ^ 4) +
    δ ^ 10 * (1 / (1 + δ ^ 2 * ‖y‖) ^ 6)) with hgdef
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hg : Integrable g :=
    (((integrable_inv_pow (n := 4) (by norm_num)).const_mul (4 * δ ^ 4)).add
      ((integrable_inv_pow_scaled (n := 6) (by norm_num) hδ2).const_mul (δ ^ 10))).const_mul
      (2 * A ^ 2)
  have hsq : ∀ y, ‖f y‖ ^ 2 ≤ g y := by
    intro y
    have h0 : 0 ≤ ‖f y‖ := norm_nonneg _
    have h1 := hb y
    unfold psi at h1
    set a := 2 * δ ^ 2 / (1 + ‖y‖) ^ 2 with ha
    set b := δ ^ 5 / (1 + δ ^ 2 * ‖y‖) ^ 3 with hb'
    have ha2 : a ^ 2 = 4 * δ ^ 4 * (1 / (1 + ‖y‖) ^ 4) := by rw [ha]; field_simp; ring
    have hb2 : b ^ 2 = δ ^ 10 * (1 / (1 + δ ^ 2 * ‖y‖) ^ 6) := by rw [hb']; field_simp
    have hsq1 : ‖f y‖ ^ 2 ≤ (A * (a + b)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have hsq2 : (A * (a + b)) ^ 2 ≤ 2 * A ^ 2 * (a ^ 2 + b ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg A]
    rw [hgdef]
    simp only
    rw [← ha2, ← hb2]
    linarith
  obtain ⟨hmem, hle⟩ := memLp_l2Norm_le_of_sq hf hg hsq
  refine ⟨hmem, hle.trans (le_of_eq ?_)⟩
  have hI : ∫ y, g y = (A * δ ^ 2) ^ 2 * (2 * (4 * c4 + c6)) := by
    rw [hgdef]
    simp only
    rw [integral_const_mul, integral_add ((integrable_inv_pow (n := 4) (by norm_num)).const_mul _)
      ((integrable_inv_pow_scaled (n := 6) (by norm_num) hδ2).const_mul _),
      integral_const_mul, integral_const_mul, integral_inv_pow_scaled 6 hδ2]
    unfold c4 c6
    field_simp
  rw [hI, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), cPsi]
  ring

end UnforcedLeray.ResidualForceHyp
