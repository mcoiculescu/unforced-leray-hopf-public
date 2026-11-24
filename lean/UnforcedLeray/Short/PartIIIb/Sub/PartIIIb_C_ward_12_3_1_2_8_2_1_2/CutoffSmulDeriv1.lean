import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements

/-!
# `cutoffSmulDeriv1`: first derivative of a cut-off field

Proves `CutoffSmulDeriv1` (`Statements.lean`), source lines 1446-1455, 1464-1466.
For `|y| < R` the field `(χ_R - 1) b` vanishes near `y`, so its derivative is `0`.
For `|y| ≥ R` the weight `1 - χ_{R/2}(y)` equals `1`, and
`D((χ_R - 1) b) = (χ_R - 1) Db + (Dχ_R) ⊗ b` with `|Dχ_R| ≤ K / R`, `Dχ_R = 0` for `|y| > 2R`,
and `1 / R ≤ 4 / (1 + |y|)` on `R ≤ |y| ≤ 2R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.RieszLp
open UnforcedLeray.Cons.C03.Concrete
open NavierStokesR3.ComparisonCutoffs

theorem cutoffSmulDeriv1 : UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.CutoffSmulDeriv1 := by
  refine ⟨4 * derivativeConstant 1 + 1, ?_, ?_⟩
  · have := derivativeConstant_pos 1
    linarith
  intro b hb M hM hbd R hR y
  have hK0 : 0 < derivativeConstant 1 := derivativeConstant_pos 1
  have hR0 : 0 < R := by linarith
  have hb0 : ∀ x : Space, ‖b x‖ ≤ M * powWeight 1 x := by
    intro x
    have h := hbd x 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at h
    simpa using h
  have hd1 : ∀ x : Space, ‖fderiv ℝ b x‖ ≤ M * powWeight 2 x := by
    intro x
    have h := hbd x 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h
    norm_num at h
    exact h
  have hC0 : (0 : ℝ) ≤ 4 * derivativeConstant 1 + 1 := by linarith
  have hcut1 : 0 ≤ 1 - cutoff (R / 2) y := by linarith [cutoff_le_one (R / 2) y]
  have hRHS0 : 0 ≤ (4 * derivativeConstant 1 + 1) * M * ((1 - cutoff (R / 2) y) * powWeight 2 y) :=
    mul_nonneg (mul_nonneg hC0 hM) (mul_nonneg hcut1 (powWeight_nonneg 2 y))
  by_cases hy : ‖y‖ < R
  · -- the field vanishes near y
    have hzero : (fun x : Space => (cutoff R x - 1) • b x) =ᶠ[𝓝 y] fun _ => (0 : Space) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with x hx
      have hx' : ‖x‖ ≤ R := le_of_lt hx
      simp [cutoff_eq_one hR0 hx']
    rw [norm_iteratedFDeriv_one, hzero.fderiv_eq]
    simpa using hRHS0
  · push Not at hy
    have hw : cutoff (R / 2) y = 0 :=
      NavierStokesR3.ComparisonCutoffs.cutoff_eq_zero (by linarith) (by linarith)
    have hRHS : (4 * derivativeConstant 1 + 1) * M * ((1 - cutoff (R / 2) y) * powWeight 2 y)
        = (4 * derivativeConstant 1 + 1) * M * powWeight 2 y := by
      rw [hw]; ring
    rw [hRHS, norm_iteratedFDeriv_one]
    have hc : DifferentiableAt ℝ (fun x : Space => cutoff R x - 1) y :=
      ((cutoff_smooth R).differentiable (by simp) y).sub_const 1
    have hfb : DifferentiableAt ℝ b y := (hb.differentiable (by simp)) y
    have hderiv : fderiv ℝ (fun x : Space => (cutoff R x - 1) • b x) y =
        (cutoff R y - 1) • fderiv ℝ b y + (fderiv ℝ (cutoff R) y).smulRight (b y) := by
      have hsm : fderiv ℝ (fun x : Space => (cutoff R x - 1) • b x) y =
          (cutoff R y - 1) • fderiv ℝ b y +
            (fderiv ℝ (fun x : Space => cutoff R x - 1) y).smulRight (b y) :=
        fderiv_smul hc hfb
      rw [hsm, fderiv_sub_const]
    rw [hderiv]
    -- first term
    have hT1 : ‖(cutoff R y - 1) • fderiv ℝ b y‖ ≤ M * powWeight 2 y := by
      rw [norm_smul, Real.norm_eq_abs]
      have habs : |cutoff R y - 1| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [cutoff_nonneg R y]
        · linarith [cutoff_le_one R y]
      have hd := hd1 y
      calc |cutoff R y - 1| * ‖fderiv ℝ b y‖ ≤ 1 * (M * powWeight 2 y) :=
            mul_le_mul habs hd (norm_nonneg _) zero_le_one
        _ = M * powWeight 2 y := one_mul _
    -- second term
    have hT2 : ‖(fderiv ℝ (cutoff R) y).smulRight (b y)‖ ≤
        4 * derivativeConstant 1 * M * powWeight 2 y := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      by_cases hy2 : 2 * R < ‖y‖
      · have hz : fderiv ℝ (cutoff R) y = 0 := by
          have hev : (cutoff R) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
            filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy2] with x hx
            exact NavierStokesR3.ComparisonCutoffs.cutoff_eq_zero hR0 (le_of_lt hx)
          rw [hev.fderiv_eq]
          simp
        rw [hz]
        simp only [norm_zero, zero_mul]
        have := mul_nonneg (mul_nonneg hK0.le hM) (powWeight_nonneg 2 y)
        linarith
      · push Not at hy2
        have hpw1 : powWeight 1 y = (1 + ‖y‖)⁻¹ := by
          have := powWeight_natCast 1 y
          simpa using this
        have hpw2 : powWeight 2 y = ((1 + ‖y‖) ^ 2)⁻¹ := by
          have := powWeight_natCast 2 y
          norm_num at this
          exact this
        have hp : 0 < 1 + ‖y‖ := by positivity
        have hkey : (1 : ℝ) / R ≤ 4 * (1 + ‖y‖)⁻¹ := by
          rw [show (4 : ℝ) * (1 + ‖y‖)⁻¹ = 4 / (1 + ‖y‖) by ring,
            div_le_div_iff₀ hR0 hp]
          nlinarith
        calc ‖fderiv ℝ (cutoff R) y‖ * ‖b y‖
            ≤ (derivativeConstant 1 / R) * (M * powWeight 1 y) :=
              mul_le_mul (cutoff_fderiv_le hR0 y) (hb0 y) (norm_nonneg _)
                (div_nonneg hK0.le hR0.le)
          _ = derivativeConstant 1 * M * ((1 : ℝ) / R * (1 + ‖y‖)⁻¹) := by
              rw [hpw1]; ring
          _ ≤ derivativeConstant 1 * M * (4 * (1 + ‖y‖)⁻¹ * (1 + ‖y‖)⁻¹) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK0.le hM)
              exact mul_le_mul_of_nonneg_right hkey (by positivity)
          _ = 4 * derivativeConstant 1 * M * powWeight 2 y := by
              rw [hpw2, ← inv_pow]; ring
    have htri := norm_add_le ((cutoff R y - 1) • fderiv ℝ b y)
      ((fderiv ℝ (cutoff R) y).smulRight (b y))
    have hM2 : 0 ≤ M * powWeight 2 y := mul_nonneg hM (powWeight_nonneg 2 y)
    have hKM : 0 ≤ derivativeConstant 1 * M * powWeight 2 y :=
      mul_nonneg (mul_nonneg hK0.le hM) (powWeight_nonneg 2 y)
    nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
