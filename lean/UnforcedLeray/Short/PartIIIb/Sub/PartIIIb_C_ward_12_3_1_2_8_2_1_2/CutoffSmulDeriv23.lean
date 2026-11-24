import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements

/-!
# `cutoffSmulDeriv23`: second and third derivatives of a cut-off field

Proves `CutoffSmulDeriv23` (`Statements.lean`), source lines 1446-1455 (diffusion commutators
`O(R⁻¹)`, `O(R⁻²)` on the escaping annulus). With `f = χ_R - 1`, `g = f • b`, Leibniz gives
`D²g` and `D³g` as sums of `D^i f · D^{k-i} b`. The derivatives of `f` vanish on `|y| < R` and for
`i ≥ 1` on `|y| > 2R`, and on the annulus `R ≤ |y| ≤ 2R` they obey `|D^i f| ≤ c_i R^{-i}`.
Writing `p = (1+|y|)⁻¹`, every term is `≤ C M p²`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

theorem cs23_powWeight_two (y : Space) : powWeight 2 y = ((1 + ‖y‖) ^ 2)⁻¹ := by
  unfold powWeight
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

/-- `D^i (χ_R - 1) = D^i χ_R` for `i ≥ 1`. -/
theorem cs23_fderiv_eq (R : ℝ) (i : ℕ) (hi : 1 ≤ i) :
    iteratedFDeriv ℝ i (fun x : Space => cutoff R x - 1) = iteratedFDeriv ℝ i (cutoff R) := by
  have hc : ContDiff ℝ i (cutoff R) := (cutoff_smooth R).of_le (by simp)
  have h1 : ContDiff ℝ i (fun _ : Space => (1 : ℝ)) := contDiff_const
  have hne : i ≠ 0 := by omega
  rw [show (fun x : Space => cutoff R x - 1) = cutoff R - fun _ => (1 : ℝ) from rfl,
    iteratedFDeriv_sub hc h1, iteratedFDeriv_const_of_ne hne (1 : ℝ), sub_zero]

/-- The `i`-th derivative of `χ_R` vanishes on `2R < |y|`. -/
theorem cs23_zero_out {R : ℝ} (hR0 : 0 < R) {y : Space} (hy : 2 * R < ‖y‖) (i : ℕ) (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (cutoff R) y‖ = 0 := by
  have hopen : {x : Space | 2 * R < ‖x‖} ∈ 𝓝 y :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hy
  have hev : cutoff R =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [hopen] with x hx
    exact cutoff_eq_zero hR0 (le_of_lt (show 2 * R < ‖x‖ from hx))
  have h2 : iteratedFDeriv ℝ i (cutoff R) =ᶠ[𝓝 y] iteratedFDeriv ℝ i (fun _ : Space => (0 : ℝ)) :=
    hev.iteratedFDeriv ℝ i
  rw [iteratedFDeriv_const_of_ne (by omega : i ≠ 0)] at h2
  rw [h2.eq_of_nhds]
  simp

/-- The `i`-th derivative of `(χ_R - 1) • b` vanishes on `|y| < R`. -/
theorem cs23_zero_in {R : ℝ} (hR0 : 0 < R) {y : Space} (hy : ‖y‖ < R) (b : Space → Space)
    (i : ℕ) (hi : 1 ≤ i) :
    iteratedFDeriv ℝ i (fun x => (cutoff R x - 1) • b x) y = 0 := by
  have hopen : {x : Space | ‖x‖ < R} ∈ 𝓝 y :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hy
  have hev : (fun x => (cutoff R x - 1) • b x) =ᶠ[𝓝 y] fun _ => (0 : Space) := by
    filter_upwards [hopen] with x hx
    rw [cutoff_eq_one hR0 (le_of_lt (show ‖x‖ < R from hx)), sub_self, zero_smul]
  have h2 : iteratedFDeriv ℝ i (fun x => (cutoff R x - 1) • b x) =ᶠ[𝓝 y]
      iteratedFDeriv ℝ i (fun _ : Space => (0 : Space)) := hev.iteratedFDeriv ℝ i
  rw [iteratedFDeriv_const_of_ne (by omega : i ≠ 0)] at h2
  rw [h2.eq_of_nhds]
  simp

/-- Leibniz for `D²(F • b)` with the factors kept abstract. -/
theorem cs23_expand2 (F : Space → ℝ) (b : Space → Space) (hF : ContDiff ℝ ∞ F)
    (hb : ContDiff ℝ ∞ b) (y : Space) :
    ‖iteratedFDeriv ℝ 2 (fun x => F x • b x) y‖ ≤
      ‖iteratedFDeriv ℝ 0 F y‖ * ‖iteratedFDeriv ℝ 2 b y‖ +
        2 * ‖iteratedFDeriv ℝ 1 F y‖ * ‖iteratedFDeriv ℝ 1 b y‖ +
        ‖iteratedFDeriv ℝ 2 F y‖ * ‖iteratedFDeriv ℝ 0 b y‖ := by
  have h := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hF hb y (n := 2) (by simp)
  refine h.trans (le_of_eq ?_)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- Leibniz for `D³(F • b)` with the factors kept abstract. -/
theorem cs23_expand3 (F : Space → ℝ) (b : Space → Space) (hF : ContDiff ℝ ∞ F)
    (hb : ContDiff ℝ ∞ b) (y : Space) :
    ‖iteratedFDeriv ℝ 3 (fun x => F x • b x) y‖ ≤
      ‖iteratedFDeriv ℝ 0 F y‖ * ‖iteratedFDeriv ℝ 3 b y‖ +
        3 * ‖iteratedFDeriv ℝ 1 F y‖ * ‖iteratedFDeriv ℝ 2 b y‖ +
        3 * ‖iteratedFDeriv ℝ 2 F y‖ * ‖iteratedFDeriv ℝ 1 b y‖ +
        ‖iteratedFDeriv ℝ 3 F y‖ * ‖iteratedFDeriv ℝ 0 b y‖ := by
  have h := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) hF hb y (n := 3) (by simp)
  refine h.trans (le_of_eq ?_)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem cutoffSmulDeriv23 : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.CutoffSmulDeriv23 := by
  have hc1 := derivativeConstant_pos 1
  have hc2 := derivativeConstant_pos 2
  have hc3 := derivativeConstant_pos 3
  refine ⟨1 + 7 * derivativeConstant 1 + 9 * derivativeConstant 2 + 3 * derivativeConstant 3,
    by linarith, ?_⟩
  intro b hb M hM hbM R hR y
  have hR1 : (1 : ℝ) ≤ R := hR
  have hR0 : (0 : ℝ) < R := by linarith
  have hfc : ContDiff ℝ ∞ (fun x : Space => cutoff R x - 1) :=
    (cutoff_smooth R).sub contDiff_const
  have hCnn : 0 ≤ 1 + 7 * derivativeConstant 1 + 9 * derivativeConstant 2 +
      3 * derivativeConstant 3 := by linarith
  -- the inverse weight `p = (1+|y|)⁻¹`
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, (1 + ‖y‖)⁻¹ = p := ⟨_, rfl⟩
  have hnorm0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hx : (0 : ℝ) < 1 + ‖y‖ := by linarith
  have hxp : (1 + ‖y‖) * p = 1 := by rw [← hpdef]; exact mul_inv_cancel₀ hx.ne'
  have hp0 : 0 ≤ p := by rw [← hpdef]; exact inv_nonneg.mpr hx.le
  have hp1 : p ≤ 1 := by
    rw [← hpdef]
    exact inv_le_one_of_one_le₀ (by linarith)
  have htp : ‖y‖ * p ≤ 1 := by linarith [hxp, hp0]
  have hpw2 : powWeight 2 y = p ^ 2 := by
    rw [cs23_powWeight_two, ← inv_pow, hpdef]
  -- bounds on the derivatives of `b`
  have hbk : ∀ k : ℕ, k ≤ 3 → ‖iteratedFDeriv ℝ k b y‖ ≤ M * p ^ (k + 1) := by
    intro k hk
    have h' := hbM y k hk
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, powWeight_natCast,
      ← inv_pow, hpdef] at h'
    exact h'
  have hb0 : ‖b y‖ ≤ M * p := by simpa using hbk 0 (by norm_num)
  have hb1 : ‖iteratedFDeriv ℝ 1 b y‖ ≤ M * p ^ 2 := by simpa using hbk 1 (by norm_num)
  have hb2 : ‖iteratedFDeriv ℝ 2 b y‖ ≤ M * p ^ 3 := by simpa using hbk 2 (by norm_num)
  have hb3 : ‖iteratedFDeriv ℝ 3 b y‖ ≤ M * p ^ 4 := by simpa using hbk 3 (by norm_num)
  have hpM : 0 ≤ M * p ^ 2 := mul_nonneg hM (by positivity)
  have hp3 : p ^ 3 ≤ p ^ 2 := pow_le_pow_of_le_one hp0 hp1 (by norm_num)
  have hp4 : p ^ 4 ≤ p ^ 2 := pow_le_pow_of_le_one hp0 hp1 (by norm_num)
  -- Leibniz expansions of `D²g`, `D³g`
  have e2 : ‖iteratedFDeriv ℝ 2 (fun x => (cutoff R x - 1) • b x) y‖ ≤
      ‖iteratedFDeriv ℝ 0 (fun x : Space => cutoff R x - 1) y‖ * ‖iteratedFDeriv ℝ 2 b y‖ +
        2 * ‖iteratedFDeriv ℝ 1 (fun x : Space => cutoff R x - 1) y‖ *
          ‖iteratedFDeriv ℝ 1 b y‖ +
        ‖iteratedFDeriv ℝ 2 (fun x : Space => cutoff R x - 1) y‖ * ‖iteratedFDeriv ℝ 0 b y‖ :=
    cs23_expand2 (fun x : Space => cutoff R x - 1) b hfc hb y
  have e3 : ‖iteratedFDeriv ℝ 3 (fun x => (cutoff R x - 1) • b x) y‖ ≤
      ‖iteratedFDeriv ℝ 0 (fun x : Space => cutoff R x - 1) y‖ * ‖iteratedFDeriv ℝ 3 b y‖ +
        3 * ‖iteratedFDeriv ℝ 1 (fun x : Space => cutoff R x - 1) y‖ *
          ‖iteratedFDeriv ℝ 2 b y‖ +
        3 * ‖iteratedFDeriv ℝ 2 (fun x : Space => cutoff R x - 1) y‖ *
          ‖iteratedFDeriv ℝ 1 b y‖ +
        ‖iteratedFDeriv ℝ 3 (fun x : Space => cutoff R x - 1) y‖ * ‖iteratedFDeriv ℝ 0 b y‖ :=
    cs23_expand3 (fun x : Space => cutoff R x - 1) b hfc hb y
  rw [cs23_fderiv_eq R 1 le_rfl, cs23_fderiv_eq R 2 (by norm_num)] at e2
  rw [cs23_fderiv_eq R 1 le_rfl, cs23_fderiv_eq R 2 (by norm_num),
    cs23_fderiv_eq R 3 (by norm_num)] at e3
  simp only [norm_iteratedFDeriv_zero] at e2 e3
  have hX : ‖cutoff R y - 1‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [cutoff_nonneg R y, cutoff_le_one R y]
  rcases le_or_gt R ‖y‖ with hRt | hRt
  · -- the annulus-and-outside case: `1 - χ_{R/2}(y) = 1`
    have hcut : cutoff (R / 2) y = 0 := cutoff_eq_zero (by linarith) (by linarith)
    have hcut' : (1 - cutoff (R / 2) y) = 1 := by rw [hcut]; ring
    rw [hcut', hpw2]
    have ha1 := cutoff_iteratedFDeriv_le hR0 1 y
    have ha2 := cutoff_iteratedFDeriv_le hR0 2 y
    have ha3 := cutoff_iteratedFDeriv_le hR0 3 y
    have hA1 : ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ ≤ derivativeConstant 1 := by
      refine ha1.trans ?_
      rw [pow_one]
      exact div_le_self hc1.le hR1
    have hA2 : ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ ≤ derivativeConstant 2 :=
      ha2.trans (div_le_self hc2.le (one_le_pow₀ hR1))
    have K1 : ‖y‖ * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ ≤ 2 * derivativeConstant 1 := by
      by_cases h2R : 2 * R < ‖y‖
      · rw [cs23_zero_out hR0 h2R 1 le_rfl]
        simp only [mul_zero]
        linarith
      · have hle : ‖y‖ ≤ 2 * R := not_lt.mp h2R
        have ha1' : ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ ≤ derivativeConstant 1 / R := by
          refine ha1.trans (le_of_eq ?_)
          rw [pow_one]
        calc ‖y‖ * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖
            ≤ (2 * R) * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ :=
              mul_le_mul_of_nonneg_right hle (norm_nonneg _)
          _ ≤ (2 * R) * (derivativeConstant 1 / R) :=
              mul_le_mul_of_nonneg_left ha1' (by positivity)
          _ = 2 * derivativeConstant 1 := by field_simp
    have K4 : ‖y‖ * ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * (1 + ‖y‖) ≤
        6 * derivativeConstant 2 := by
      by_cases h2R : 2 * R < ‖y‖
      · rw [cs23_zero_out hR0 h2R 2 (by norm_num)]
        simp only [mul_zero, zero_mul]
        linarith
      · have hle : ‖y‖ ≤ 2 * R := not_lt.mp h2R
        have ha2' : ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * R ^ 2 ≤ derivativeConstant 2 :=
          (le_div_iff₀ (by positivity)).mp ha2
        calc ‖y‖ * ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * (1 + ‖y‖)
            ≤ (2 * R) * ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * (3 * R) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right hle (norm_nonneg _))
              · linarith
              · positivity
              · positivity
          _ = 6 * (‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * R ^ 2) := by ring
          _ ≤ 6 * derivativeConstant 2 := by linarith
    have K5 : ‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * (1 + ‖y‖) ≤ 3 * derivativeConstant 3 := by
      by_cases h2R : 2 * R < ‖y‖
      · rw [cs23_zero_out hR0 h2R 3 (by norm_num)]
        simp only [zero_mul]
        linarith
      · have ha3' : ‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * R ^ 3 ≤ derivativeConstant 3 :=
          (le_div_iff₀ (by positivity)).mp ha3
        have hle : ‖y‖ ≤ 2 * R := not_lt.mp h2R
        have hR3 : R ≤ R ^ 3 := le_self_pow₀ hR1 (by norm_num)
        calc ‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * (1 + ‖y‖)
            ≤ ‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * (3 * R) :=
              mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
          _ ≤ ‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * (3 * R ^ 3) :=
              mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
          _ = 3 * (‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * R ^ 3) := by ring
          _ ≤ 3 * derivativeConstant 3 := by linarith
    -- the second derivative
    have T0 : ‖y‖ * (‖cutoff R y - 1‖ * ‖iteratedFDeriv ℝ 2 b y‖) ≤ M * p ^ 2 := by
      calc ‖y‖ * (‖cutoff R y - 1‖ * ‖iteratedFDeriv ℝ 2 b y‖)
          ≤ ‖y‖ * ‖iteratedFDeriv ℝ 2 b y‖ :=
            mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hX) hnorm0
        _ ≤ ‖y‖ * (M * p ^ 3) := mul_le_mul_of_nonneg_left hb2 hnorm0
        _ = M * p ^ 2 * (‖y‖ * p) := by ring
        _ ≤ M * p ^ 2 * 1 := mul_le_mul_of_nonneg_left htp hpM
        _ = M * p ^ 2 := mul_one _
    have T1 : ‖y‖ * (2 * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 1 b y‖) ≤
        4 * derivativeConstant 1 * (M * p ^ 2) := by
      calc ‖y‖ * (2 * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 1 b y‖)
          = (‖y‖ * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖) * (2 * ‖iteratedFDeriv ℝ 1 b y‖) := by ring
        _ ≤ (2 * derivativeConstant 1) * (2 * ‖iteratedFDeriv ℝ 1 b y‖) :=
            mul_le_mul_of_nonneg_right K1 (by positivity)
        _ ≤ (2 * derivativeConstant 1) * (2 * (M * p ^ 2)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        _ = 4 * derivativeConstant 1 * (M * p ^ 2) := by ring
    have T2 : ‖y‖ * (‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * ‖b y‖) ≤
        6 * derivativeConstant 2 * (M * p ^ 2) := by
      calc ‖y‖ * (‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * ‖b y‖)
          = (‖y‖ * ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * (1 + ‖y‖)) * (p * ‖b y‖) := by
            linear_combination (-(‖y‖ * ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * ‖b y‖)) * hxp
        _ ≤ (6 * derivativeConstant 2) * (p * ‖b y‖) :=
            mul_le_mul_of_nonneg_right K4 (mul_nonneg hp0 (norm_nonneg _))
        _ ≤ (6 * derivativeConstant 2) * (p * (M * p)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb0 hp0) (by linarith)
        _ = 6 * derivativeConstant 2 * (M * p ^ 2) := by ring
    -- the third derivative
    have U0 : ‖cutoff R y - 1‖ * ‖iteratedFDeriv ℝ 3 b y‖ ≤ M * p ^ 2 := by
      calc ‖cutoff R y - 1‖ * ‖iteratedFDeriv ℝ 3 b y‖
          ≤ ‖iteratedFDeriv ℝ 3 b y‖ := mul_le_of_le_one_left (norm_nonneg _) hX
        _ ≤ M * p ^ 4 := hb3
        _ = M * p ^ 4 := rfl
        _ ≤ M * p ^ 2 := mul_le_mul_of_nonneg_left hp4 hM
    have U1 : 3 * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 2 b y‖ ≤
        3 * derivativeConstant 1 * (M * p ^ 2) := by
      calc 3 * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 2 b y‖
          ≤ 3 * derivativeConstant 1 * ‖iteratedFDeriv ℝ 2 b y‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA1 (by norm_num))
              (norm_nonneg _)
        _ ≤ 3 * derivativeConstant 1 * (M * p ^ 3) :=
            mul_le_mul_of_nonneg_left hb2 (by linarith)
        _ ≤ 3 * derivativeConstant 1 * (M * p ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp3 hM) (by linarith)
    have U2 : 3 * ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 1 b y‖ ≤
        3 * derivativeConstant 2 * (M * p ^ 2) := by
      calc 3 * ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 1 b y‖
          ≤ 3 * derivativeConstant 2 * ‖iteratedFDeriv ℝ 1 b y‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA2 (by norm_num))
              (norm_nonneg _)
        _ ≤ 3 * derivativeConstant 2 * (M * p ^ 2) :=
            mul_le_mul_of_nonneg_left hb1 (by linarith)
    have U3 : ‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * ‖b y‖ ≤ 3 * derivativeConstant 3 * (M * p ^ 2) := by
      calc ‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * ‖b y‖
          = (‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * (1 + ‖y‖)) * (p * ‖b y‖) := by
            linear_combination (-(‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * ‖b y‖)) * hxp
        _ ≤ (3 * derivativeConstant 3) * (p * ‖b y‖) :=
            mul_le_mul_of_nonneg_right K5 (mul_nonneg hp0 (norm_nonneg _))
        _ ≤ (3 * derivativeConstant 3) * (p * (M * p)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb0 hp0) (by linarith)
        _ = 3 * derivativeConstant 3 * (M * p ^ 2) := by ring
    constructor
    · -- `‖y‖ ‖D²g‖ ≤ C M p²`
      have hmain : ‖y‖ * ‖iteratedFDeriv ℝ 2 (fun x => (cutoff R x - 1) • b x) y‖ ≤
          ‖y‖ * (‖cutoff R y - 1‖ * ‖iteratedFDeriv ℝ 2 b y‖ +
            2 * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 1 b y‖ +
            ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * ‖b y‖) :=
        mul_le_mul_of_nonneg_left e2 hnorm0
      have hsplit : ‖y‖ * (‖cutoff R y - 1‖ * ‖iteratedFDeriv ℝ 2 b y‖ +
            2 * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 1 b y‖ +
            ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * ‖b y‖) =
          ‖y‖ * (‖cutoff R y - 1‖ * ‖iteratedFDeriv ℝ 2 b y‖) +
            ‖y‖ * (2 * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 1 b y‖) +
            ‖y‖ * (‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * ‖b y‖) := by ring
      have hfinal : ‖y‖ * ‖iteratedFDeriv ℝ 2 (fun x => (cutoff R x - 1) • b x) y‖ ≤
          (1 + 7 * derivativeConstant 1 + 9 * derivativeConstant 2 +
            3 * derivativeConstant 3) * M * (1 * p ^ 2) := by
        linarith [hmain, hsplit, T0, T1, T2, mul_nonneg hc1.le hpM, mul_nonneg hc2.le hpM,
          mul_nonneg hc3.le hpM]
      exact hfinal
    · -- `‖D³g‖ ≤ C M p²`
      have hmain3 : ‖iteratedFDeriv ℝ 3 (fun x => (cutoff R x - 1) • b x) y‖ ≤
          ‖cutoff R y - 1‖ * ‖iteratedFDeriv ℝ 3 b y‖ +
            3 * ‖iteratedFDeriv ℝ 1 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 2 b y‖ +
            3 * ‖iteratedFDeriv ℝ 2 (cutoff R) y‖ * ‖iteratedFDeriv ℝ 1 b y‖ +
            ‖iteratedFDeriv ℝ 3 (cutoff R) y‖ * ‖b y‖ := e3
      have hfinal3 : ‖iteratedFDeriv ℝ 3 (fun x => (cutoff R x - 1) • b x) y‖ ≤
          (1 + 7 * derivativeConstant 1 + 9 * derivativeConstant 2 +
            3 * derivativeConstant 3) * M * (1 * p ^ 2) := by
        linarith [hmain3, U0, U1, U2, U3, mul_nonneg hc1.le hpM, mul_nonneg hc2.le hpM,
          mul_nonneg hc3.le hpM]
      exact hfinal3
  · -- the inner case `|y| < R`: the product vanishes near `y`
    have hRHS : 0 ≤ (1 + 7 * derivativeConstant 1 + 9 * derivativeConstant 2 +
        3 * derivativeConstant 3) * M * ((1 - cutoff (R / 2) y) * powWeight 2 y) :=
      mul_nonneg (mul_nonneg hCnn hM)
        (mul_nonneg (by linarith [cutoff_le_one (R / 2) y]) (powWeight_nonneg _ _))
    constructor
    · rw [cs23_zero_in hR0 hRt b 2 (by norm_num)]
      simp only [norm_zero, mul_zero]
      exact hRHS
    · rw [cs23_zero_in hR0 hRt b 3 (by norm_num)]
      simp only [norm_zero]
      exact hRHS

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
