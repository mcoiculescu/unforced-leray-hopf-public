import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4.HalfPlane

/-!
# `SlicesChange` (`PartIII-b:C/near/masked/14/2/3/1/4`; source 2683, 3996-4011)

Self-similar substitution: first `η = √s z` in the inner integral, then `s = R²/ρ²` in the outer one.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- Scaling of the Lebesgue integral: `∫ g(η/c) dη = c ∫ g`, for `c > 0`. -/
lemma lintegral_div_scale (g : ℝ → ℝ≥0∞) (hg : Measurable g) (c : ℝ) (hc : 0 < c) :
    ∫⁻ η : ℝ, g (η / c) = ENNReal.ofReal c * ∫⁻ z : ℝ, g z := by
  have h1 : (fun η : ℝ => g (η / c)) = fun η => g (η * c⁻¹) := by
    funext η
    rw [div_eq_mul_inv]
  rw [h1]
  have hm : Measurable (fun x : ℝ => x * c⁻¹) := measurable_mul_const c⁻¹
  rw [← lintegral_map hg hm, Real.map_volume_mul_right (inv_ne_zero hc.ne'), inv_inv,
    abs_of_pos hc, lintegral_smul_measure, smul_eq_mul]

/-- `s^{-5/2} √s = s^{-2}` for `s > 0`. -/
lemma rpow_mul_sqrt_aux (s : ℝ) (hs : 0 < s) :
    s ^ (-5 / 2 : ℝ) * Real.sqrt s = s ^ (-2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs]
  norm_num

lemma hasDerivAt_quot_aux (R x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => R ^ 2 / y ^ 2) (-(2 * R ^ 2) / x ^ 3) x := by
  have h := (hasDerivAt_const x (R ^ 2)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)
  have e : (0 * x ^ 2 - R ^ 2 * (((2 : ℕ) : ℝ) * x ^ (2 - 1))) / (x ^ 2) ^ 2
      = -(2 * R ^ 2) / x ^ 3 := by
    rw [show (2 : ℕ) - 1 = 1 from rfl]
    field_simp
    ring
  exact h.congr_deriv e

theorem slicesChange : SlicesChange := by
  intro R hR F hF
  have hG : ∀ ρ : ℝ, Measurable (fun z : ℝ => F ρ z) :=
    fun ρ => hF.comp (measurable_const.prodMk measurable_id)
  -- inner `η`-integral
  have hinner : ∀ s ∈ Ioi (0 : ℝ),
      ∫⁻ η : ℝ, ENNReal.ofReal (s ^ (-5 / 2 : ℝ)) * F (R / Real.sqrt s) (η / Real.sqrt s)
        = ENNReal.ofReal (s ^ (-2 : ℝ)) * ∫⁻ z : ℝ, F (R / Real.sqrt s) z := by
    intro s hs
    have hs' : 0 < s := hs
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_div_scale (fun z : ℝ => F (R / Real.sqrt s) z) (hG _) (Real.sqrt s)
        (Real.sqrt_pos.2 hs'),
      ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs'.le _), rpow_mul_sqrt_aux s hs']
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner]
  -- right-hand side: pull the `z`-integral against `ρ`
  have hR' : ∀ ρ : ℝ, ∫⁻ z : ℝ, ENNReal.ofReal ρ * F ρ z
      = ENNReal.ofReal ρ * ∫⁻ z : ℝ, F ρ z :=
    fun ρ => lintegral_const_mul _ (hG ρ)
  simp_rw [hR']
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- substitution `s = R²/ρ²` on `ρ > 0`
  have himg : (fun ρ : ℝ => R ^ 2 / ρ ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext s
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      have hρ' : 0 < ρ := hρ
      show (0 : ℝ) < R ^ 2 / ρ ^ 2
      positivity
    · intro hs
      have hs' : 0 < s := hs
      refine ⟨R / Real.sqrt s, div_pos hR (Real.sqrt_pos.2 hs'), ?_⟩
      have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs'.le
      show R ^ 2 / (R / Real.sqrt s) ^ 2 = s
      rw [div_pow, hsq]
      field_simp
  have hinj : Set.InjOn (fun ρ : ℝ => R ^ 2 / ρ ^ 2) (Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    have ha' : 0 < a := ha
    have hb' : 0 < b := hb
    simp only at hab
    rw [div_eq_div_iff (pow_ne_zero 2 ha'.ne') (pow_ne_zero 2 hb'.ne')] at hab
    have h3 : R ^ 2 * (a ^ 2 - b ^ 2) = 0 := by linear_combination -hab
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd h4 (pow_ne_zero 2 hR.ne')
    · have h5 : (a - b) * (a + b) = 0 := by linear_combination h4
      rcases mul_eq_zero.1 h5 with h6 | h6
      · linarith
      · linarith
  have hlhs := lintegral_image_eq_lintegral_abs_deriv_mul (f := fun ρ : ℝ => R ^ 2 / ρ ^ 2)
    (f' := fun ρ : ℝ => -(2 * R ^ 2) / ρ ^ 3) measurableSet_Ioi
    (fun x hx => (hasDerivAt_quot_aux R x hx.ne').hasDerivWithinAt) hinj
    (fun s => ENNReal.ofReal (s ^ (-2 : ℝ)) * ∫⁻ z : ℝ, F (R / Real.sqrt s) z)
  rw [himg] at hlhs
  rw [hlhs]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
  have hρ' : 0 < ρ := hρ
  have hsq : Real.sqrt (R ^ 2 / ρ ^ 2) = R / ρ := by
    rw [show R ^ 2 / ρ ^ 2 = (R / ρ) ^ 2 by rw [div_pow], Real.sqrt_sq (div_pos hR hρ').le]
  have hback : R / Real.sqrt (R ^ 2 / ρ ^ 2) = ρ := by
    rw [hsq]
    field_simp
  have habs : |-(2 * R ^ 2) / ρ ^ 3| = 2 * R ^ 2 / ρ ^ 3 := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * R ^ 2),
      abs_of_pos (by positivity : (0 : ℝ) < ρ ^ 3)]
  have hpw : (R ^ 2 / ρ ^ 2) ^ (-2 : ℝ) = ((R ^ 2 / ρ ^ 2) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [hback, habs, hpw]
  have hk : ENNReal.ofReal (2 * R ^ 2 / ρ ^ 3) * ENNReal.ofReal (((R ^ 2 / ρ ^ 2) ^ 2)⁻¹)
      = ENNReal.ofReal (2 / R ^ 2 * ρ) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [← mul_assoc, hk, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
