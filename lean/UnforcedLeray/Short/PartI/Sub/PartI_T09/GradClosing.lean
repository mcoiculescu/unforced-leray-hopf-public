import UnforcedLeray.Short.PartI.Sub.PartI_T09

/-!
# Part I, task `PartI:T09/9`: proof of the leaf `GradClosing`

Source of record: `the November 2 reference manuscript`, line 355.
With `x = βc²/a ≥ 0` one has `a⁻¹ = x/(βc²)`, so
`C ν⁻¹ a⁻³ e^{-x} = a⁻² · (Cν⁻¹/(βc²)) · (x e^{-x})`, and `x e^{-x} ≤ 1`.
The factor `Cν⁻¹/(βc²) ≤ 1/2` once `νc² ≥ R := 2C/β + 1`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem gradClosing_proof : GradClosing := by
  intro C β hC hβ
  refine ⟨2 * C / β + 1, by positivity, ?_⟩
  intro ν c a hν ha1 hac hR
  have ha0 : 0 < a := by linarith
  have hc2 : 0 < c ^ 2 := lt_of_lt_of_le ha0 hac
  have hβc : 0 < β * c ^ 2 := mul_pos hβ hc2
  -- exponent variable
  have hx0 : 0 ≤ β * c ^ 2 / a := div_nonneg hβc.le ha0.le
  -- a^(-3) = (a^2)⁻¹ * (1/a)
  have h3 : a ^ (3 : ℝ) = a ^ 3 := by exact_mod_cast Real.rpow_natCast a 3
  have hpow : a ^ (-(3 : ℝ)) = (a ^ 2)⁻¹ * (1 / a) := by
    rw [Real.rpow_neg ha0.le, h3, one_div, ← mul_inv]
    congr 1
  -- 1/a = x/(βc²)
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc2
    norm_num at hc2
  have hinv : 1 / a = (β * c ^ 2 / a) / (β * c ^ 2) := by
    rw [div_div, div_eq_div_iff ha0.ne' (mul_ne_zero ha0.ne' hβc.ne')]
    ring
  -- x e^{-x} ≤ 1
  have hxe : (β * c ^ 2 / a) * Real.exp (-(β * c ^ 2 / a)) ≤ 1 := by
    have hE : 0 < Real.exp (β * c ^ 2 / a) := Real.exp_pos _
    have hadd := Real.add_one_le_exp (β * c ^ 2 / a)
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hE]
    linarith
  -- M := Cν⁻¹/(βc²) ≤ 1/2
  have hM : C * ν⁻¹ / (β * c ^ 2) ≤ 1 / 2 := by
    have h1 : 2 * C / β + 1 ≤ ν * c ^ 2 := hR
    have h2 : (2 * C / β + 1) * β ≤ ν * c ^ 2 * β :=
      mul_le_mul_of_nonneg_right h1 hβ.le
    have h3' : (2 * C / β + 1) * β = 2 * C + β := by
      field_simp
    have h4 : 2 * C ≤ ν * c ^ 2 * β := by linarith
    have hCν : C * ν⁻¹ = C / ν := by ring
    rw [div_le_iff₀ hβc, hCν, div_le_iff₀ hν]
    nlinarith
  have hM0 : 0 ≤ C * ν⁻¹ / (β * c ^ 2) := by
    apply div_nonneg _ hβc.le
    exact mul_nonneg hC.le (inv_nonneg.mpr hν.le)
  have hb : (C * ν⁻¹ / (β * c ^ 2)) * ((β * c ^ 2 / a) * Real.exp (-(β * c ^ 2 / a)))
      ≤ 1 / 2 :=
    (mul_le_of_le_one_right hM0 hxe).trans hM
  have hA0 : 0 ≤ (a ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg a)
  have hkey : C * ν⁻¹ * a ^ (-(3 : ℝ)) * Real.exp (-(β * c ^ 2 / a))
      = (a ^ 2)⁻¹ * ((C * ν⁻¹ / (β * c ^ 2)) *
          ((β * c ^ 2 / a) * Real.exp (-(β * c ^ 2 / a)))) := by
    rw [hpow, hinv]
    ring
  rw [hkey]
  calc (a ^ 2)⁻¹ * ((C * ν⁻¹ / (β * c ^ 2)) *
          ((β * c ^ 2 / a) * Real.exp (-(β * c ^ 2 / a))))
      ≤ (a ^ 2)⁻¹ * (1 / 2) := mul_le_mul_of_nonneg_left hb hA0
    _ = (a ^ 2)⁻¹ / 2 := by ring

end UnforcedLeray.Short.PartI
