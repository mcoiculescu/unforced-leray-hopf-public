import UnforcedLeray.Short.PartIIa.StatementsNear

/-!
# Part II-a, task `PartII-a:N02/4/1` helper: the `L²` bound from a pointwise bound

If `‖h p‖ ≤ M (u₁ p + u₂ p + u₃ p + u₄ p)` with `u_i` square integrable, then the `L²(μ)` norm of
`h` is at most `2 M Σ_i (∫ u_i²)^{1/2}`. This is the Minkowski step behind `near:leray-test`
(the sums `∫ (|η|^j)² ‖S^a g‖²` are the moments of `nearLerayRhs`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

lemma nzco_sqrt_rpow_sq (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

lemma nzco_sq_rpow_half (y : ℝ) (hy : 0 ≤ y) : (y ^ 2) ^ (1 / 2 : ℝ) = y := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hy]

lemma nzco_l2_le {μ : Measure Profile} (h : Profile → MeridC) (hh : MemLp h 2 μ) (M : ℝ)
    (hM : 0 ≤ M) (u₁ u₂ u₃ u₄ : Profile → ℝ)
    (i₁ : Integrable (fun p => u₁ p ^ 2) μ) (i₂ : Integrable (fun p => u₂ p ^ 2) μ)
    (i₃ : Integrable (fun p => u₃ p ^ 2) μ) (i₄ : Integrable (fun p => u₄ p ^ 2) μ)
    (hpt : ∀ p, ‖h p‖ ≤ M * (u₁ p + u₂ p + u₃ p + u₄ p)) :
    ‖hh.toLp h‖ ≤ 2 * M * ((∫ p, u₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
      (∫ p, u₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
  have hA₁ : 0 ≤ ∫ p, u₁ p ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg _
  have hA₂ : 0 ≤ ∫ p, u₂ p ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg _
  have hA₃ : 0 ≤ ∫ p, u₃ p ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg _
  have hA₄ : 0 ≤ ∫ p, u₄ p ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg _
  have hN : 0 ≤ ∫ p, ‖h p‖ ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg _
  -- the `L²` norm as the square root of the integral of `‖h‖²`
  have hnorm : ‖hh.toLp h‖ = (∫ p, ‖h p‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hh,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun p =>
        Real.rpow_nonneg (norm_nonneg _) _) _)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]
  -- integrability of the two sides of the pointwise comparison
  have j12 : Integrable (fun p => u₁ p ^ 2 + u₂ p ^ 2) μ := i₁.add i₂
  have j123 : Integrable (fun p => u₁ p ^ 2 + u₂ p ^ 2 + u₃ p ^ 2) μ := j12.add i₃
  have j1234 : Integrable (fun p => u₁ p ^ 2 + u₂ p ^ 2 + u₃ p ^ 2 + u₄ p ^ 2) μ := j123.add i₄
  have hL : ∫ p, ‖h p‖ ^ 2 ∂μ ≤ ∫ p, 4 * M ^ 2 * (u₁ p ^ 2 + u₂ p ^ 2 + u₃ p ^ 2 + u₄ p ^ 2) ∂μ := by
    refine integral_mono hh.norm.integrable_sq (j1234.const_mul (4 * M ^ 2)) ?_
    intro p
    have h1 : ‖h p‖ ^ 2 ≤ (M * (u₁ p + u₂ p + u₃ p + u₄ p)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hpt p) 2
    have h2 : (u₁ p + u₂ p + u₃ p + u₄ p) ^ 2 ≤
        4 * (u₁ p ^ 2 + u₂ p ^ 2 + u₃ p ^ 2 + u₄ p ^ 2) := by
      nlinarith [sq_nonneg (u₁ p - u₂ p), sq_nonneg (u₁ p - u₃ p), sq_nonneg (u₁ p - u₄ p),
        sq_nonneg (u₂ p - u₃ p), sq_nonneg (u₂ p - u₄ p), sq_nonneg (u₃ p - u₄ p)]
    calc ‖h p‖ ^ 2 ≤ (M * (u₁ p + u₂ p + u₃ p + u₄ p)) ^ 2 := h1
      _ = M ^ 2 * (u₁ p + u₂ p + u₃ p + u₄ p) ^ 2 := by ring
      _ ≤ M ^ 2 * (4 * (u₁ p ^ 2 + u₂ p ^ 2 + u₃ p ^ 2 + u₄ p ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg M)
      _ = 4 * M ^ 2 * (u₁ p ^ 2 + u₂ p ^ 2 + u₃ p ^ 2 + u₄ p ^ 2) := by ring
  have hR : ∫ p, 4 * M ^ 2 * (u₁ p ^ 2 + u₂ p ^ 2 + u₃ p ^ 2 + u₄ p ^ 2) ∂μ =
      4 * M ^ 2 * ((∫ p, u₁ p ^ 2 ∂μ) + (∫ p, u₂ p ^ 2 ∂μ) + (∫ p, u₃ p ^ 2 ∂μ) +
        (∫ p, u₄ p ^ 2 ∂μ)) := by
    have e1 := integral_add j123 i₄
    have e2 := integral_add j12 i₃
    have e3 := integral_add i₁ i₂
    rw [integral_const_mul, e1, e2, e3]
  -- the sum of the four moments is at most the square of the sum of their square roots
  have hT : (∫ p, u₁ p ^ 2 ∂μ) + (∫ p, u₂ p ^ 2 ∂μ) + (∫ p, u₃ p ^ 2 ∂μ) + (∫ p, u₄ p ^ 2 ∂μ) ≤
      ((∫ p, u₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
        (∫ p, u₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
    have s1 := nzco_sqrt_rpow_sq _ hA₁
    have s2 := nzco_sqrt_rpow_sq _ hA₂
    have s3 := nzco_sqrt_rpow_sq _ hA₃
    have s4 := nzco_sqrt_rpow_sq _ hA₄
    have t1 : 0 ≤ (∫ p, u₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA₁ _
    have t2 : 0 ≤ (∫ p, u₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA₂ _
    have t3 : 0 ≤ (∫ p, u₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA₃ _
    have t4 : 0 ≤ (∫ p, u₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA₄ _
    nlinarith [mul_nonneg t1 t2, mul_nonneg t1 t3, mul_nonneg t1 t4, mul_nonneg t2 t3,
      mul_nonneg t2 t4, mul_nonneg t3 t4]
  have hY : 0 ≤ 2 * M * ((∫ p, u₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
      (∫ p, u₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
    have t1 : 0 ≤ (∫ p, u₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA₁ _
    have t2 : 0 ≤ (∫ p, u₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA₂ _
    have t3 : 0 ≤ (∫ p, u₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA₃ _
    have t4 : 0 ≤ (∫ p, u₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA₄ _
    exact mul_nonneg (mul_nonneg two_pos.le hM) (by linarith)
  have hXY : ∫ p, ‖h p‖ ^ 2 ∂μ ≤ (2 * M * ((∫ p, u₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
      (∫ p, u₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
      (∫ p, u₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ))) ^ 2 := by
    have h4 : 4 * M ^ 2 * ((∫ p, u₁ p ^ 2 ∂μ) + (∫ p, u₂ p ^ 2 ∂μ) + (∫ p, u₃ p ^ 2 ∂μ) +
        (∫ p, u₄ p ^ 2 ∂μ)) ≤ 4 * M ^ 2 * ((∫ p, u₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
        (∫ p, u₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
        (∫ p, u₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    calc ∫ p, ‖h p‖ ^ 2 ∂μ
        ≤ 4 * M ^ 2 * ((∫ p, u₁ p ^ 2 ∂μ) + (∫ p, u₂ p ^ 2 ∂μ) + (∫ p, u₃ p ^ 2 ∂μ) +
          (∫ p, u₄ p ^ 2 ∂μ)) := hL.trans hR.le
      _ ≤ _ := h4
      _ = _ := by ring
  rw [hnorm]
  calc (∫ p, ‖h p‖ ^ 2 ∂μ) ^ (1 / 2 : ℝ)
      ≤ ((2 * M * ((∫ p, u₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
          (∫ p, u₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ))) ^ 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hN hXY (by norm_num)
    _ = _ := nzco_sq_rpow_half _ hY

end UnforcedLeray.Short.PartIIa

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- Difference form of `nzco_l2_le`: `‖toLp F - toLp G‖` is bounded by the `L²` moments of the
pointwise bound. -/
lemma nzco_l2_moment {μ : Measure Profile} (F G : Profile → MeridC) (hF : MemLp F 2 μ)
    (hG : MemLp G 2 μ) (M : ℝ) (hM : 0 ≤ M) (u₁ u₂ u₃ u₄ : Profile → ℝ)
    (i₁ : Integrable (fun p => u₁ p ^ 2) μ) (i₂ : Integrable (fun p => u₂ p ^ 2) μ)
    (i₃ : Integrable (fun p => u₃ p ^ 2) μ) (i₄ : Integrable (fun p => u₄ p ^ 2) μ)
    (hpt : ∀ p, ‖F p - G p‖ ≤ M * (u₁ p + u₂ p + u₃ p + u₄ p)) :
    ‖hF.toLp F - hG.toLp G‖ ≤ 2 * M * ((∫ p, u₁ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
      (∫ p, u₂ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) + (∫ p, u₃ p ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
      (∫ p, u₄ p ^ 2 ∂μ) ^ (1 / 2 : ℝ)) := by
  rw [← MemLp.toLp_sub]
  exact nzco_l2_le (F - G) (hF.sub hG) M hM u₁ u₂ u₃ u₄ i₁ i₂ i₃ i₄ hpt

end UnforcedLeray.Short.PartIIa
