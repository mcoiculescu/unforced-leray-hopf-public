import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayGradPerp.Deriv

/-!
# Pointwise bounds for the cut-off gradients (helper for `LerayGradPerp`)

* `norm_cvec_pair_le`: `‖cvec ![χa, χb + e]‖ ≤ ‖cvec ![a, b]‖ + |e|` for `0 ≤ χ ≤ 1`.
* `errFn`: the integrable majorant `3CB 1_{[s0,s1]}(s) (1 + η²)^{-1/2}` of the error term
  `u · chi'(N⁻¹η) N⁻¹`, which is supported where `2 ≤ (N⁻¹η)² ≤ 3`, so `N⁻¹ ≤ 3 (1+η²)^{-1/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.GradPerpCut

theorem sq_norm_cvec (w : Fin 2 → ℝ) : ‖cvec w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  simp [cvec, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_cvec_pair_le {χ a b e : ℝ} (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) :
    ‖cvec ![χ * a, χ * b + e]‖ ≤ ‖cvec ![a, b]‖ + |e| := by
  set R := ‖cvec ![a, b]‖ with hRdef
  have hR0 : 0 ≤ R := norm_nonneg _
  have hR2 : R ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hRdef, sq_norm_cvec]
    simp
  have hb : |b| ≤ R := by
    nlinarith [sq_abs b, abs_nonneg b, sq_nonneg a]
  have hx2 : (χ * a) ^ 2 ≤ a ^ 2 := by
    have : χ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg a]
  have hy : |χ * b + e| ≤ |b| + |e| := by
    calc |χ * b + e| ≤ |χ * b| + |e| := abs_add_le _ _
      _ ≤ |b| + |e| := by
        rw [abs_mul, abs_of_nonneg hχ0]
        nlinarith [abs_nonneg b, abs_nonneg e]
  have hy2 : (χ * b + e) ^ 2 ≤ (|b| + |e|) ^ 2 := by
    rw [← sq_abs (χ * b + e)]
    exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hX2 : ‖cvec ![χ * a, χ * b + e]‖ ^ 2 ≤ (R + |e|) ^ 2 := by
    rw [sq_norm_cvec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [sq_abs b, sq_abs e, abs_nonneg e, abs_nonneg b, mul_nonneg (abs_nonneg e) hR0,
      mul_le_mul_of_nonneg_right hb (abs_nonneg e)]
  nlinarith [norm_nonneg (cvec ![χ * a, χ * b + e]), abs_nonneg e]

/-- The integrable majorant `3CB 1_{[s0,s1]}(s) (1 + η²)^{-1/2}` of the error term. -/
def errFn (s0 s1 K : ℝ) : Chart → ℝ := fun p =>
  (Icc s0 s1).indicator (fun _ => K) p.1 * (Real.sqrt (1 + p.2.2 ^ 2))⁻¹

theorem errFn_nonneg {s0 s1 K : ℝ} (hK : 0 ≤ K) (p : Chart) : 0 ≤ errFn s0 s1 K p := by
  unfold errFn
  apply mul_nonneg
  · exact Set.indicator_nonneg (fun _ _ => hK) _
  · exact inv_nonneg.2 (Real.sqrt_nonneg _)

theorem abs_e_le_errFn {s0 s1 C B N : ℝ} (hN : 1 ≤ N) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hB' : ∀ t : ℝ, |deriv chi t| ≤ B) {u : Chart → ℝ} (p : Chart) (hup : |u p| ≤ C)
    (hband : u p ≠ 0 → p.1 ∈ Icc s0 s1) :
    |u p * (deriv chi (N⁻¹ * p.2.2) * N⁻¹)| ≤ errFn s0 s1 (3 * C * B) p := by
  have hK : 0 ≤ 3 * C * B := mul_nonneg (mul_nonneg (by norm_num) hC) hB
  have hnn := errFn_nonneg (s0 := s0) (s1 := s1) hK p
  have hN0 : 0 < N := by linarith
  by_cases hu0 : u p = 0
  · rw [hu0, zero_mul, abs_zero]
    exact hnn
  by_cases hd0 : deriv chi (N⁻¹ * p.2.2) = 0
  · have h0 : u p * (deriv chi (N⁻¹ * p.2.2) * N⁻¹) = 0 := by rw [hd0]; ring
    rw [h0, abs_zero]
    exact hnn
  obtain ⟨h2, h3⟩ := sq_bounds_of_deriv_ne (t := N⁻¹ * p.2.2) hd0
  have hp1 : p.1 ∈ Icc s0 s1 := hband hu0
  have hη : p.2.2 ^ 2 ≤ 3 * N ^ 2 := by
    have e1 : p.2.2 ^ 2 = N ^ 2 * (N⁻¹ * p.2.2) ^ 2 := by
      field_simp
    rw [e1]
    nlinarith [sq_nonneg N]
  have hsq : Real.sqrt (1 + p.2.2 ^ 2) ≤ 3 * N := by
    rw [Real.sqrt_le_left]
    · nlinarith
    · linarith
  have hsqpos : 0 < Real.sqrt (1 + p.2.2 ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hinv : N⁻¹ ≤ 3 * (Real.sqrt (1 + p.2.2 ^ 2))⁻¹ := by
    have := inv_anti₀ hsqpos hsq
    rw [mul_inv] at this
    linarith
  have habs : |u p * (deriv chi (N⁻¹ * p.2.2) * N⁻¹)| =
      |u p| * |deriv chi (N⁻¹ * p.2.2)| * N⁻¹ := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hN0)]
    ring
  rw [habs]
  have hdB := hB' (N⁻¹ * p.2.2)
  have hterm : errFn s0 s1 (3 * C * B) p = 3 * C * B * (Real.sqrt (1 + p.2.2 ^ 2))⁻¹ := by
    unfold errFn
    rw [Set.indicator_of_mem hp1]
  rw [hterm]
  have hNi : 0 ≤ N⁻¹ := (inv_pos.2 hN0).le
  calc |u p| * |deriv chi (N⁻¹ * p.2.2)| * N⁻¹ ≤ C * B * N⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ hNi
        exact mul_le_mul hup hdB (abs_nonneg _) hC
    _ ≤ C * B * (3 * (Real.sqrt (1 + p.2.2 ^ 2))⁻¹) :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg hC hB)
    _ = 3 * C * B * (Real.sqrt (1 + p.2.2 ^ 2))⁻¹ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.GradPerpCut
