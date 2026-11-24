import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b
import UnforcedLeray.Lib.Gaussian.PeriodizationCell

/-!
# Part III-a, helper for `PartIII-a:T21/c1/b/2`: uniform decay of the planar cross integrals

For planar kernels with `|λ(y)| ≲ (1+|y|₁+|y|₂)^{-2}` and `|e(y)| ≲ exp(-|y|²/8)`, the cross
integral `∫ λ_i(y) e_j(y₁ + a, y₂) dy` is bounded by `K/(1+|a|)²` uniformly in `a`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.IIIa

/-- Gaussian shifted in the first variable: integrable on the plane. -/
theorem integrable_shift_gauss (c : ℝ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ × ℝ => Real.exp (-((y.1 + c) ^ 2 + y.2 ^ 2) / (4 * t))) := by
  have h := (UnforcedLeray.Gaussian.integrable_gauss_plane ht).comp_add_right (c, 0)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp

/-- The integral of the shifted Gaussian is the unshifted one, `4π t`. -/
theorem integral_shift_gauss (c : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ y : ℝ × ℝ, Real.exp (-((y.1 + c) ^ 2 + y.2 ^ 2) / (4 * t)) = 4 * Real.pi * t := by
  calc ∫ y : ℝ × ℝ, Real.exp (-((y.1 + c) ^ 2 + y.2 ^ 2) / (4 * t))
      = ∫ y : ℝ × ℝ, Real.exp (-((y + (c, 0)).1 ^ 2 + (y + (c, 0)).2 ^ 2) / (4 * t)) := by
        congr 1; funext y; simp
    _ = ∫ z : ℝ × ℝ, Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * t)) :=
        integral_add_right_eq_self (μ := (volume : Measure (ℝ × ℝ)))
          (fun z : ℝ × ℝ => Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (4 * t))) (c, 0)
    _ = 4 * Real.pi * t := UnforcedLeray.Gaussian.integral_gauss_plane ht

/-- Pointwise splitting of the weight `(1+|y₁|+|y₂|)^{-2}` against the shifted Gaussian. -/
theorem gram_pt (a y1 y2 : ℝ) :
    (1 + |y1| + |y2|)⁻¹ ^ 2 * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) ≤
      4 / (1 + |a|) ^ 2 * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 4)) := by
  have hE8 : 0 ≤ Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) := (Real.exp_pos _).le
  have hE16 : 0 ≤ Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 4)) := (Real.exp_pos _).le
  have hEa : 0 ≤ Real.exp (-a ^ 2 / (4 * 16)) := (Real.exp_pos _).le
  have hs0 : 0 ≤ |y1| + |y2| := by positivity
  rcases le_total |a| (2 * (|y1| + |y2|)) with h | h
  · have h1 : (1 + |a|) / 2 ≤ 1 + |y1| + |y2| := by linarith
    have hpos : 0 < (1 + |a|) / 2 := by positivity
    have h2 : (1 + |y1| + |y2|)⁻¹ ^ 2 ≤ 4 / (1 + |a|) ^ 2 := by
      have hsq := pow_le_pow_left₀ hpos.le h1 2
      calc (1 + |y1| + |y2|)⁻¹ ^ 2 = 1 / (1 + |y1| + |y2|) ^ 2 := by rw [inv_pow, one_div]
        _ ≤ 1 / ((1 + |a|) / 2) ^ 2 := one_div_le_one_div_of_le (by positivity) hsq
        _ = 4 / (1 + |a|) ^ 2 := by field_simp <;> norm_num
    have hm := mul_le_mul_of_nonneg_right h2 hE8
    have hnn : 0 ≤ Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 4)) :=
      mul_nonneg hEa hE16
    linarith
  · have hz : |a| / 2 ≤ |y1 + a| := by
      have hA : |a| ≤ |y1 + a| + |y1| := by
        calc |a| = |(y1 + a) - y1| := by congr 1; ring
          _ ≤ |y1 + a| + |y1| := abs_sub _ _
      have h1 : |y1| ≤ |a| / 2 := by linarith [abs_nonneg y2]
      linarith
    have hsq : a ^ 2 / 4 ≤ (y1 + a) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hz 2
      have hsa : (|a| / 2) ^ 2 = a ^ 2 / 4 := by rw [div_pow, sq_abs]; ring
      have hsy : |y1 + a| ^ 2 = (y1 + a) ^ 2 := sq_abs _
      linarith
    have hexp : Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) ≤
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 4)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg y2]
    have hP : (1 + |y1| + |y2|)⁻¹ ^ 2 ≤ 1 := by
      have h1' : 1 ≤ 1 + |y1| + |y2| := by linarith [abs_nonneg y1, abs_nonneg y2]
      exact pow_le_one₀ (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ h1')
    have hm := mul_le_mul_of_nonneg_right hP hE8
    have hnn : 0 ≤ 4 / (1 + |a|) ^ 2 * Real.exp (-((y1 + a) ^ 2 + y2 ^ 2) / (4 * 2)) := by
      positivity
    linarith

/-- The Gaussian weight `e^{-a²/64}` against `(1+|a|)²`. -/
theorem exp_neg_sq_mul_le (a : ℝ) :
    Real.exp (-a ^ 2 / (4 * 16)) * (1 + |a|) ^ 2 ≤ 128 := by
  have h := Real.add_one_le_exp (a ^ 2 / (4 * 16))
  have hEF : Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (a ^ 2 / (4 * 16)) = 1 := by
    rw [← Real.exp_add, show -a ^ 2 / (4 * 16) + a ^ 2 / (4 * 16) = 0 by ring, Real.exp_zero]
  have hE : 0 < Real.exp (-a ^ 2 / (4 * 16)) := Real.exp_pos _
  have hq : (1 + |a|) ^ 2 ≤ 128 * Real.exp (a ^ 2 / (4 * 16)) := by
    nlinarith [sq_abs a, sq_nonneg (|a| - 1), abs_nonneg a]
  calc Real.exp (-a ^ 2 / (4 * 16)) * (1 + |a|) ^ 2
      ≤ Real.exp (-a ^ 2 / (4 * 16)) * (128 * Real.exp (a ^ 2 / (4 * 16))) :=
        mul_le_mul_of_nonneg_left hq hE.le
    _ = 128 := by linear_combination 128 * hEF

/-- **Uniform cross bound.** For planar kernels with the decay of `PlanarFrameKernels`, there is
`K` with `‖∫ λ_i(y) e_j(y₁ + a, y₂) dy‖ ≤ K/(1+|a|)²` for all `i, j, a`. -/
theorem gramCross_bound (κ : PlanarFrameKernels) :
    ∃ K : ℝ, ∀ (i j : Fin 2) (a : ℝ),
      ‖∫ y : ℝ × ℝ, κ.lamP i y * κ.e j (y.1 + a, y.2)‖ ≤ K / (1 + |a|) ^ 2 := by
  obtain ⟨C1, hC1⟩ := κ.lamP_decay
  obtain ⟨C2, hC2⟩ := κ.e_decay
  refine ⟨|C1| * |C2| * (2080 * Real.pi), fun i j a => ?_⟩
  have hA : 0 ≤ |C1| * |C2| := by positivity
  have hpt : ∀ y : ℝ × ℝ, ‖κ.lamP i y * κ.e j (y.1 + a, y.2)‖ ≤
      (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) := by
    intro y
    rw [norm_mul]
    have h1 : ‖κ.lamP i y‖ ≤ |C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2 :=
      (hC1 i y).trans (mul_le_mul_of_nonneg_right (le_abs_self C1) (by positivity))
    have h2 : ‖κ.e j (y.1 + a, y.2)‖ ≤
        |C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by
      have h := hC2 j (y.1 + a, y.2)
      have e8 : (8 : ℝ) = 4 * 2 := by norm_num
      have hh : Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / 8) =
          Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) := by norm_num
      refine h.trans ?_
      dsimp only
      rw [hh]
      exact mul_le_mul_of_nonneg_right (le_abs_self C2) (Real.exp_pos _).le
    calc ‖κ.lamP i y‖ * ‖κ.e j (y.1 + a, y.2)‖
        ≤ (|C1| * (1 + |y.1| + |y.2|)⁻¹ ^ 2) * (|C2| * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = (|C1| * |C2|) * ((1 + |y.1| + |y.2|)⁻¹ ^ 2 *
            Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2))) := by ring
      _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
          mul_le_mul_of_nonneg_left (gram_pt a y.1 y.2) hA
  have G8 := integrable_shift_gauss (c := a) (t := 2) (by norm_num)
  have G16 := integrable_shift_gauss (c := a) (t := 4) (by norm_num)
  have hint : Integrable (fun y : ℝ × ℝ => (|C1| * |C2|) *
      (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
        Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4)))) :=
    ((G8.const_mul (4 / (1 + |a|) ^ 2)).add (G16.const_mul (Real.exp (-a ^ 2 / (4 * 16))))).const_mul _
  have hE := exp_neg_sq_mul_le a
  have hE' : Real.exp (-a ^ 2 / (4 * 16)) ≤ 128 / (1 + |a|) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc ‖∫ y : ℝ × ℝ, κ.lamP i y * κ.e j (y.1 + a, y.2)‖
      ≤ ∫ y : ℝ × ℝ, (|C1| * |C2|) *
          (4 / (1 + |a|) ^ 2 * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 2)) +
            Real.exp (-a ^ 2 / (4 * 16)) * Real.exp (-((y.1 + a) ^ 2 + y.2 ^ 2) / (4 * 4))) :=
        norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hpt)
    _ = (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          Real.exp (-a ^ 2 / (4 * 16)) * (4 * Real.pi * 4)) := by
        rw [integral_const_mul, integral_add (G8.const_mul _) (G16.const_mul _),
          integral_const_mul, integral_const_mul,
          integral_shift_gauss (c := a) (t := 2) (by norm_num),
          integral_shift_gauss (c := a) (t := 4) (by norm_num)]
    _ ≤ (|C1| * |C2|) * (4 / (1 + |a|) ^ 2 * (4 * Real.pi * 2) +
          128 / (1 + |a|) ^ 2 * (4 * Real.pi * 4)) := by
        gcongr
    _ = |C1| * |C2| * (2080 * Real.pi) / (1 + |a|) ^ 2 := by ring

end UnforcedLeray.Short.IIIa
