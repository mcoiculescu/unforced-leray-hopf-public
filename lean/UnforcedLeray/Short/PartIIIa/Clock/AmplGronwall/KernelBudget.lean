import UnforcedLeray.Short.PartIIIa.Sub.T21_c4

/-!
# Part III-a, task `PartIII-a:T21/c4/2`: the closed amplitude kernel budget

Source: `the November 2 reference manuscript` lines 2998-3001 (`δ = Cν³/θ`,
`c = C(θ⁻¹+δ)`, `η = C(1+ν³)/θ`) and 3011-3015 (the budget).

With `A = clockA ν r = 1 + νr`, `θ = (νA)⁻¹`, the integrand reduces to
`Cν⁴/A + C³ν²(1+Cν³)(1+ν³) ≤ K₀ν²` with `K₀ = C + 2C³(1+C)`; integrating over `(t,s]`
and using `b ≤ θ(s)` gives `K₀ν²(s-t) ≤ K₀/b`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem amplKernelBudget : UnforcedLeray.Short.IIIa.AmplKernelBudget := by
  unfold AmplKernelBudget
  intro C hC
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = C + 2 * C ^ 3 * (1 + C) := ⟨_, rfl⟩
  have hK0nn : 0 ≤ K0 := by
    rw [hK0]
    have h3 : 0 ≤ C ^ 3 := pow_nonneg hC.le 3
    have h1 : 0 ≤ 2 * C ^ 3 * (1 + C) := mul_nonneg (mul_nonneg (by norm_num) h3) (by linarith)
    linarith
  refine ⟨K0, fun b hb ν hν t s ht hts hθ => ?_⟩
  have hν0 : 0 < ν := hν.1
  have hν1 : ν ≤ 1 := hν.2
  have hb0 : 0 < b := by linarith
  have hs0 : 0 ≤ s := ht.trans hts
  -- pointwise bound on the integrand
  have hpt : ∀ r ∈ Ioc t s,
      ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) +
        ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) *
          ENNReal.ofReal (C * (C * (1 + ν ^ 3) / clockTheta ν r))) ≤
      ENNReal.ofReal (K0 * ν ^ 2) := by
    intro r hr
    have hr0 : 0 ≤ r := ht.trans hr.1.le
    have hA0 : 0 < clockA ν r := by
      unfold clockA
      linarith [mul_nonneg hν0.le hr0]
    have hA1 : 1 ≤ clockA ν r := by
      unfold clockA
      linarith [mul_nonneg hν0.le hr0]
    have hθr : clockTheta ν r = (ν * clockA ν r)⁻¹ := rfl
    have hθpos : 0 < clockTheta ν r := by
      rw [hθr]
      exact inv_pos.mpr (mul_pos hν0 hA0)
    have hν' : ν ≠ 0 := hν0.ne'
    have hA' : clockA ν r ≠ 0 := hA0.ne'
    have h13 : 0 ≤ 1 + ν ^ 3 := by
      have := pow_pos hν0 3
      linarith
    have hX : 0 ≤ C * ν ^ 3 / clockTheta ν r :=
      div_nonneg (mul_nonneg hC.le (pow_nonneg hν0.le 3)) hθpos.le
    have hY : 0 ≤ C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r) :=
      mul_nonneg hC.le (add_nonneg (div_nonneg zero_le_one hθpos.le) hX)
    have hZ : 0 ≤ C * (C * (1 + ν ^ 3) / clockTheta ν r) :=
      mul_nonneg hC.le (div_nonneg (mul_nonneg hC.le h13) hθpos.le)
    have hYZ : 0 ≤ C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r) *
        (C * (C * (1 + ν ^ 3) / clockTheta ν r)) := mul_nonneg hY hZ
    have hA2 : 0 ≤ (clockA ν r) ^ (-2 : ℝ) := Real.rpow_nonneg hA0.le _
    -- exact identity for the real integrand
    have hid : (clockA ν r) ^ (-2 : ℝ) * (C * ν ^ 3 / clockTheta ν r +
        C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r) *
          (C * (C * (1 + ν ^ 3) / clockTheta ν r))) =
        C * ν ^ 4 / clockA ν r + C ^ 3 * ν ^ 2 * ((1 + C * ν ^ 3) * (1 + ν ^ 3)) := by
      rw [hθr, Real.rpow_neg hA0.le, Real.rpow_two]
      field_simp
    -- first term
    have hν2 : ν ^ 2 ≤ 1 := by nlinarith
    have hν4 : ν ^ 4 ≤ ν ^ 2 := by
      calc ν ^ 4 = ν ^ 2 * ν ^ 2 := by ring
        _ ≤ ν ^ 2 * 1 := mul_le_mul_of_nonneg_left hν2 (sq_nonneg ν)
        _ = ν ^ 2 := mul_one _
    have hb1 : C * ν ^ 4 / clockA ν r ≤ C * ν ^ 2 := by
      rw [div_le_iff₀ hA0]
      have h2 : C * ν ^ 2 ≤ C * ν ^ 2 * clockA ν r :=
        le_mul_of_one_le_right (mul_nonneg hC.le (sq_nonneg ν)) hA1
      have h3 : C * ν ^ 4 ≤ C * ν ^ 2 := mul_le_mul_of_nonneg_left hν4 hC.le
      linarith
    -- second term
    have hν3 : ν ^ 3 ≤ 1 := pow_le_one₀ hν0.le hν1
    have hp1 : 1 + C * ν ^ 3 ≤ 1 + C := by
      have := mul_le_of_le_one_right hC.le hν3
      linarith
    have hp2 : 1 + ν ^ 3 ≤ 2 := by linarith
    have hp : (1 + C * ν ^ 3) * (1 + ν ^ 3) ≤ (1 + C) * 2 :=
      mul_le_mul hp1 hp2 h13 (by linarith)
    have hb2 : C ^ 3 * ν ^ 2 * ((1 + C * ν ^ 3) * (1 + ν ^ 3)) ≤
        C ^ 3 * ν ^ 2 * ((1 + C) * 2) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (pow_nonneg hC.le 3) (sq_nonneg ν))
    have hreal : (clockA ν r) ^ (-2 : ℝ) * (C * ν ^ 3 / clockTheta ν r +
        C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r) *
          (C * (C * (1 + ν ^ 3) / clockTheta ν r))) ≤ K0 * ν ^ 2 := by
      rw [hid, hK0]
      nlinarith [hb1, hb2]
    have hconv : ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ)) * (ENNReal.ofReal (C * ν ^ 3 / clockTheta ν r) +
        ENNReal.ofReal (C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)) *
          ENNReal.ofReal (C * (C * (1 + ν ^ 3) / clockTheta ν r))) =
        ENNReal.ofReal ((clockA ν r) ^ (-2 : ℝ) * (C * ν ^ 3 / clockTheta ν r +
          C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r) *
            (C * (C * (1 + ν ^ 3) / clockTheta ν r)))) := by
      rw [ENNReal.ofReal_mul hA2, ENNReal.ofReal_add hX hYZ, ENNReal.ofReal_mul hY]
    rw [hconv]
    exact ENNReal.ofReal_le_ofReal hreal
  -- the endpoint budget
  have hAs : 0 < clockA ν s := by
    unfold clockA
    linarith [mul_nonneg hν0.le hs0]
  have hνA : 0 < ν * clockA ν s := mul_pos hν0 hAs
  have hθ2 : b ≤ (ν * clockA ν s)⁻¹ := hθ
  have hbA : b * (ν * clockA ν s) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hθ2 hνA.le
    rwa [inv_mul_cancel₀ hνA.ne'] at h
  have hX2 : ν ^ 2 * (s - t) ≤ ν * clockA ν s := by
    unfold clockA
    nlinarith [mul_nonneg (sq_nonneg ν) ht]
  have h1 : ν ^ 2 * (s - t) * b ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hX2 hb0.le
    nlinarith [hbA, h]
  have hK0ν2 : 0 ≤ K0 * ν ^ 2 := mul_nonneg hK0nn (sq_nonneg ν)
  have hfin : K0 * ν ^ 2 * (s - t) ≤ K0 / b := by
    rw [le_div_iff₀ hb0]
    have h2 := mul_le_mul_of_nonneg_left h1 hK0nn
    nlinarith [h2]
  have hconst : ∫⁻ _ in Ioc t s, ENNReal.ofReal (K0 * ν ^ 2) ≤ ENNReal.ofReal (K0 / b) := by
    rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul hK0ν2]
    exact ENNReal.ofReal_le_ofReal hfin
  exact le_trans (setLIntegral_mono' measurableSet_Ioc hpt) hconst

end UnforcedLeray.Short.IIIa
