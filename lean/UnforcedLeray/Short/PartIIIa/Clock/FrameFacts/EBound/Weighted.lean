import UnforcedLeray.Short.PartIIIa.Defs
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Part III-a, helper for `PartIII-a:T21/c1/b/3`: Gaussian-dominated `X_{m,d}` norms (SP 2894-2897)

If `‖f(x)‖ ≤ M e^{-|x|²/16}` on the centred cell `B0579.cell d`, then `‖f‖_{X_{m,d}} ≤ M K_m` with
`K_m` independent of `d` (the weight `(1+|x|²)^m` is absorbed by the Gaussian on all of `ℝ²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa


/-- Every nonnegative power moment of a one-dimensional Gaussian is integrable. -/
theorem integrable_sq_rpow_mul_gaussian {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    Integrable (fun x : ℝ => (x ^ 2) ^ p * Real.exp (-b * x ^ 2)) := by
  have ht : b / 2 ≠ 0 := ne_of_gt (by positivity)
  have hpos : Integrable (fun x : ℝ => Real.exp ((-b + b / 2) * x ^ 2)) := by
    convert integrable_exp_neg_mul_sq (by positivity : 0 < b / 2) using 1 <;> congr 1 <;> ring
  have hneg : Integrable (fun x : ℝ => Real.exp ((-b - b / 2) * x ^ 2)) := by
    convert integrable_exp_neg_mul_sq (by positivity : 0 < b + b / 2) using 1 <;> congr 1 <;> ring
  exact ProbabilityTheory.integrable_rpow_mul_exp_of_integrable_exp_mul
    (μ := (volume : Measure ℝ)) (X := fun x : ℝ => x ^ 2) (v := -b) (t := b / 2)
    ht hpos hneg hp

/-- The axial polynomial weight times a Gaussian remains integrable for arbitrary real `m≥0`. -/
theorem integrable_axialGaussianWeight {b m : ℝ} (hb : 0 < b) (hm : 0 ≤ m) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ (m / 2) * Real.exp (-b * x ^ 2)) := by
  let α := m / 2
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hzero : Integrable (fun x : ℝ => Real.exp (-b * x ^ 2)) := integrable_exp_neg_mul_sq hb
  have hmoment := integrable_sq_rpow_mul_gaussian hb hα
  have hsum : Integrable (fun x : ℝ =>
      Real.exp (-b * x ^ 2) + (x ^ 2) ^ α * Real.exp (-b * x ^ 2)) := hzero.add hmoment
  have hmajor : Integrable (fun x : ℝ => 2 ^ α *
      (Real.exp (-b * x ^ 2) + (x ^ 2) ^ α * Real.exp (-b * x ^ 2))) := by
    simpa [mul_comm] using hsum.const_mul (2 ^ α)
  refine hmajor.mono' ?_ ?_
  · fun_prop
  · filter_upwards [] with x
    have ht : 0 ≤ x ^ 2 := sq_nonneg x
    have hbase : 1 + x ^ 2 ≤ 2 * max 1 (x ^ 2) := by
      have h1 := le_max_left (1 : ℝ) (x ^ 2)
      have h2 := le_max_right (1 : ℝ) (x ^ 2)
      nlinarith
    have hweight : (1 + x ^ 2) ^ α ≤ 2 ^ α * (1 + (x ^ 2) ^ α) := by
      calc
        (1 + x ^ 2) ^ α ≤ (2 * max 1 (x ^ 2)) ^ α :=
          Real.rpow_le_rpow (by positivity) hbase hα
        _ = 2 ^ α * (max 1 (x ^ 2)) ^ α := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        _ ≤ 2 ^ α * (1 + (x ^ 2) ^ α) := by
          have hmax : (max 1 (x ^ 2)) ^ α = max 1 ((x ^ 2) ^ α) := by
            have h := Real.rpow_max (x := (1 : ℝ)) (y := x ^ 2) (p := α)
              (by norm_num) ht hα
            simpa using h
          rw [hmax]
          have hy : 0 ≤ (x ^ 2) ^ α := Real.rpow_nonneg ht α
          have hle : max 1 ((x ^ 2) ^ α) ≤ 1 + (x ^ 2) ^ α :=
            max_le (by linarith [hy]) (by linarith)
          exact mul_le_mul_of_nonneg_left hle (by positivity)
    have hn : 0 ≤ (1 + x ^ 2) ^ α * Real.exp (-b * x ^ 2) :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
    have hmj : 0 ≤ 2 ^ α *
        (Real.exp (-b * x ^ 2) + (x ^ 2) ^ α * Real.exp (-b * x ^ 2)) := by
      positivity
    calc
      ‖(1 + x ^ 2) ^ α * Real.exp (-b * x ^ 2)‖ =
          (1 + x ^ 2) ^ α * Real.exp (-b * x ^ 2) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hn]
      _ ≤ 2 ^ α * (1 + (x ^ 2) ^ α) * Real.exp (-b * x ^ 2) :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = 2 ^ α *
          (Real.exp (-b * x ^ 2) + (x ^ 2) ^ α * Real.exp (-b * x ^ 2)) := by ring

/-- The planar weighted Gaussian `⟨x⟩^{2m} e^{-|x|²/8}` is integrable for `m ≥ 0`. -/
theorem integrable_jb_gauss {m : ℝ} (hm : 0 ≤ m) :
    Integrable (fun x : ℝ × ℝ => B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by
  have hg : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (2 * m / 2) * Real.exp (-(1 / 8) * t ^ 2)) :=
    integrable_axialGaussianWeight (by norm_num) (by linarith)
  have hg' : Integrable (fun t : ℝ => (1 + t ^ 2) ^ m * Real.exp (-(1 / 8) * t ^ 2)) := by
    simpa [mul_div_cancel_left₀] using hg
  have h := hg'.mul_prod hg'
  refine Integrable.mono' h ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have : Continuous (fun x : ℝ × ℝ => B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8)) := by
      unfold B0579.jb
      refine Continuous.mul (Continuous.rpow_const (by fun_prop) fun x => Or.inr hm) (by fun_prop)
    exact this.aestronglyMeasurable
  · have h1 : 0 ≤ B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) :=
      mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg h1]
    have h2 : B0579.jb x ^ m ≤ (1 + x.1 ^ 2) ^ m * (1 + x.2 ^ 2) ^ m := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      refine Real.rpow_le_rpow (B0579.jb_pos x).le ?_ hm
      unfold B0579.jb
      nlinarith [sq_nonneg x.1, sq_nonneg x.2, mul_nonneg (sq_nonneg x.1) (sq_nonneg x.2)]
    have h3 : Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) =
        Real.exp (-(1 / 8) * x.1 ^ 2) * Real.exp (-(1 / 8) * x.2 ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h3]
    calc B0579.jb x ^ m * (Real.exp (-(1 / 8) * x.1 ^ 2) * Real.exp (-(1 / 8) * x.2 ^ 2))
        ≤ ((1 + x.1 ^ 2) ^ m * (1 + x.2 ^ 2) ^ m) *
            (Real.exp (-(1 / 8) * x.1 ^ 2) * Real.exp (-(1 / 8) * x.2 ^ 2)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = ((1 + x.1 ^ 2) ^ m * Real.exp (-(1 / 8) * x.1 ^ 2)) *
            ((1 + x.2 ^ 2) ^ m * Real.exp (-(1 / 8) * x.2 ^ 2)) := by ring

/-- **Gaussian domination in `X_{m,d}`**: a pointwise bound `M e^{-|x|²/16}` on the cell gives
`‖f‖_{X_{m,d}} ≤ M K_m` with `K_m` independent of `d` and `f`. -/
theorem xNorm_le_of_gauss {m : ℝ} (hm : 0 ≤ m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (d M : ℝ) (f : ℝ × ℝ → ℂ), 0 ≤ M →
      (∀ x ∈ B0579.cell d, ‖f x‖ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) →
        xNorm d m f ≤ ENNReal.ofReal (M * K) := by
  set J : ℝ × ℝ → ℝ := fun x => B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8) with hJ
  have hJi : Integrable J := integrable_jb_gauss hm
  have hJ0 : ∀ x, 0 ≤ J x := fun x =>
    mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (Real.exp_pos _).le
  set I : ℝ := ∫ x, J x with hI
  have hI0 : 0 ≤ I := integral_nonneg hJ0
  refine ⟨Real.sqrt I, Real.sqrt_nonneg _, fun d M f hM hf => ?_⟩
  unfold xNorm
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  set G : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (M ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 8))
    with hG
  have hGm : Measurable G := by
    refine ENNReal.measurable_ofReal.comp ?_
    fun_prop
  have hae : ∀ᵐ x ∂(B0579.cellMeasure d m), ‖f x‖ₑ ^ (2 : ℝ) ≤ G x := by
    refine B0579.cellMeasure_ac d m ?_
    refine (ae_restrict_iff' (measurableSet_Ico.prod MeasurableSet.univ)).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : x ∈ B0579.cell d := hx
    have hb := hf x hx'
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hn : 0 ≤ ‖f x‖ := norm_nonneg _
    have hs : ‖f x‖ ^ (2 : ℝ) ≤ (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 16)) ^ 2 := by
      rw [Real.rpow_two]
      exact pow_le_pow_left₀ hn hb 2
    refine hs.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast; ring
  have hstep : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure d m) ≤ ENNReal.ofReal (M ^ 2 * I) := by
    calc ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure d m) ≤ ∫⁻ x, G x ∂(B0579.cellMeasure d m) :=
          lintegral_mono_ae hae
      _ = ∫⁻ x, (B0579.density m x : ℝ≥0∞) * G x ∂(volume.restrict (B0579.cell d)) := by
          unfold B0579.cellMeasure
          exact lintegral_withDensity_eq_lintegral_mul _
            (B0579.measurable_density m).coe_nnreal_ennreal hGm
      _ ≤ ∫⁻ x, (B0579.density m x : ℝ≥0∞) * G x := lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ∫⁻ x, ENNReal.ofReal (M ^ 2 * J x) := by
          refine lintegral_congr fun x => ?_
          have : (B0579.density m x : ℝ≥0∞) = ENNReal.ofReal (B0579.jb x ^ m) := by
            unfold B0579.density; rfl
          rw [this, hG, ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le _)]
          congr 1
          simp only [hJ]; ring
      _ = ENNReal.ofReal (M ^ 2 * I) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hJi.const_mul (M ^ 2))
            (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg M) (hJ0 x)),
            integral_const_mul]
  calc (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure d m)) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (M ^ 2 * I)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hstep (by norm_num)
    _ = ENNReal.ofReal ((M ^ 2 * I) ^ (1 / (2 : ℝ))) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ = ENNReal.ofReal (M * Real.sqrt I) := by
        congr 1
        rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM]

end UnforcedLeray.Short.IIIa
