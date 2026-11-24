import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_3
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# `PartIII-b:C/inst/9/3` leaf 3: uniform Gaussian integral (source 5063-5079)

For `a ∈ [1, 2.1]`, `(1+r)⁴ e^{-(3/8) r/a} ≤ C e^{-(γ/2) r}` with `r = |y|²`, `γ = 5/28 = 3/(8·2.1)`,
and `∫_{ℝ²} e^{-(γ/2)|y|²} dy < ∞` (product of one-dimensional Gaussians).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fAcGaussInt : FAcGaussInt := by
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 5 / 28 := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; norm_num
  have hγne : γ ≠ 0 := hγ0.ne'
  obtain ⟨K4, hK4⟩ : ∃ K : ℝ, K = 256 * (2 / γ) ^ 4 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 8 * (1 + K4) := ⟨_, rfl⟩
  have hK40 : 0 ≤ K4 := by rw [hK4]; positivity
  have hC0 : 0 ≤ C := by rw [hC]; linarith
  -- x^4 ≤ 256 e^x for x ≥ 0
  have hEx : ∀ x : ℝ, 0 ≤ x → x ^ 4 ≤ 256 * Real.exp x := by
    intro x hx
    have h1 : x / 4 + 1 ≤ Real.exp (x / 4) := by
      linarith [Real.add_one_le_exp (x / 4)]
    have h2 : (x / 4) ^ 4 ≤ Real.exp (x / 4) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h3 : Real.exp x = Real.exp (x / 4) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h4 : x ^ 4 = 256 * (x / 4) ^ 4 := by ring
    rw [h3]
    linarith
  -- pointwise bound
  have hpt : ∀ a : ℝ, 1 ≤ a → a ≤ 21 / 10 → ∀ y : ℝ × ℝ,
      fAcG a y ≤ C * Real.exp (-(γ / 2) * sq2 y) := by
    intro a ha1 ha2 y
    have ha0 : 0 < a := by linarith
    unfold fAcG
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = sq2 y := ⟨_, rfl⟩
    rw [← hr]
    have hr0 : 0 ≤ r := by rw [hr]; unfold sq2; positivity
    have hE : Real.exp (-(3 / 8) * r / a) ≤ Real.exp (-(γ * r)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_mul, neg_div]
      apply neg_le_neg
      rw [le_div_iff₀ ha0]
      have hγr : γ * r * (21 / 10) = 3 / 8 * r := by rw [hγ]; ring
      have hh := mul_le_mul_of_nonneg_left ha2 (mul_nonneg hγ0.le hr0)
      linarith
    have hu : γ * r / 2 * (2 / γ) = r := by field_simp
    have e1 : r ^ 4 = (γ * r / 2) ^ 4 * (2 / γ) ^ 4 := by
      rw [← mul_pow, hu]
    have hx := hEx (γ * r / 2) (by positivity)
    have hr4 : r ^ 4 ≤ K4 * Real.exp (γ * r / 2) := by
      rw [e1, hK4]
      have := mul_le_mul_of_nonneg_right hx (show (0 : ℝ) ≤ (2 / γ) ^ 4 by positivity)
      linarith
    have he1 : 1 ≤ Real.exp (γ * r / 2) := Real.one_le_exp (by positivity)
    have hp1 : (1 + r) ^ 4 ≤ 8 * (1 + r ^ 4) := by
      nlinarith [mul_nonneg (sq_nonneg (r - 1)) (by positivity : (0 : ℝ) ≤ 7 * r ^ 2 + 10 * r + 7)]
    have hp : (1 + r) ^ 4 ≤ C * Real.exp (γ * r / 2) := by
      rw [hC]
      nlinarith [hp1, hr4, he1]
    calc (1 + r) ^ 4 * Real.exp (-(3 / 8) * r / a)
        ≤ (1 + r) ^ 4 * Real.exp (-(γ * r)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ (C * Real.exp (γ * r / 2)) * Real.exp (-(γ * r)) :=
          mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = C * Real.exp (-(γ / 2) * r) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  -- integrability of the Gaussian on the plane
  have hb : 0 < γ / 2 := by positivity
  have hint : Integrable (fun y : ℝ × ℝ => Real.exp (-(γ / 2) * sq2 y))
      (volume : Measure (ℝ × ℝ)) := by
    have h1 : Integrable (fun z : ℝ × ℝ => Real.exp (-(γ / 2) * z.1 ^ 2) *
        Real.exp (-(γ / 2) * z.2 ^ 2)) (volume : Measure (ℝ × ℝ)) := by
      rw [Measure.volume_eq_prod]
      exact (integrable_exp_neg_mul_sq hb).mul_prod (integrable_exp_neg_mul_sq hb)
    have e : (fun y : ℝ × ℝ => Real.exp (-(γ / 2) * sq2 y)) = fun z : ℝ × ℝ =>
        Real.exp (-(γ / 2) * z.1 ^ 2) * Real.exp (-(γ / 2) * z.2 ^ 2) := by
      funext y
      rw [← Real.exp_add]
      congr 1
      unfold sq2
      ring
    rw [e]
    exact h1
  have hI : ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(γ / 2) * sq2 y))
      ∂(volume : Measure (ℝ × ℝ)) < ⊤ :=
    hint.lintegral_lt_top
  refine ⟨C * (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(γ / 2) * sq2 y))
      ∂(volume : Measure (ℝ × ℝ))).toReal,
    mul_nonneg hC0 ENNReal.toReal_nonneg, ?_⟩
  intro a ha1 ha2
  calc ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (fAcG a y) ∂(volume : Measure (ℝ × ℝ))
      ≤ ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (C * Real.exp (-(γ / 2) * sq2 y))
          ∂(volume : Measure (ℝ × ℝ)) :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpt a ha1 ha2 y)
    _ = ENNReal.ofReal C * ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(γ / 2) * sq2 y))
          ∂(volume : Measure (ℝ × ℝ)) := by
        simp_rw [ENNReal.ofReal_mul hC0]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (C * (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Real.exp (-(γ / 2) * sq2 y))
          ∂(volume : Measure (ℝ × ℝ))).toReal) := by
        rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_toReal hI.ne]

end UnforcedLeray.Short.PartIIIb.Concrete
