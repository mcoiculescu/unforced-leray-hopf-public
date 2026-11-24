import UnforcedLeray.Units.B0146
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TrainGap.Gauss

/-!
# Train gap, helper: Gaussian bounds for the isolated heat vortex

For the isolated vortex at width `a` (`B0146.u1`, `B0146.u2`, the components of
`B0146.isoVelocity`), with `1 ≤ a ≤ K`:

* `gw_le`: `gw a y ≤ exp(-(y.1² + y.2²)/(4K))`,
* `abs_u1_le`, `abs_u2_le`: `|u_k a y| ≤ (2K+1) exp(-(1/(8K)) y.1²)`.

These are the pointwise decay bounds used for the train gap `CylTrainGap`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.TrainGap

/-- `gw a y ≤ exp(-(y.1² + y.2²)/(4K))` for `1 ≤ a ≤ K`. -/
theorem gw_le {a K : ℝ} (ha : 1 ≤ a) (haK : a ≤ K) (y : ℝ × ℝ) :
    UnforcedLeray.B0113.gw a y ≤ Real.exp (-((y.1 ^ 2 + y.2 ^ 2) / (4 * K))) := by
  have ha0 : 0 < a := by linarith
  have hK : 0 < K := lt_of_lt_of_le ha0 haK
  have hK0 : K ≠ 0 := hK.ne'
  have hinv : K⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 haK
  have hr : 0 ≤ y.1 ^ 2 + y.2 ^ 2 := by positivity
  have hmul : K⁻¹ * (y.1 ^ 2 + y.2 ^ 2) ≤ a⁻¹ * (y.1 ^ 2 + y.2 ^ 2) :=
    mul_le_mul_of_nonneg_right hinv hr
  unfold UnforcedLeray.B0113.gw
  apply Real.exp_le_exp.mpr
  have e : (y.1 ^ 2 + y.2 ^ 2) / (4 * K) = K⁻¹ * (y.1 ^ 2 + y.2 ^ 2) / 4 := by
    field_simp
  have e2 : UnforcedLeray.GaussianVortex.radiusSq y = y.1 ^ 2 + y.2 ^ 2 := rfl
  rw [e2, e]
  linarith

/-- `|u1 a y| ≤ (2K+1) exp(-(1/(8K)) y.1²)` for `1 ≤ a ≤ K`. -/
theorem abs_u1_le {a K : ℝ} (ha : 1 ≤ a) (haK : a ≤ K) (y : ℝ × ℝ) :
    |UnforcedLeray.B0146.u1 a y| ≤ (2 * K + 1) * Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) := by
  have ha0 : 0 < a := by linarith
  have hK : 0 < K := lt_of_lt_of_le ha0 haK
  have hK0 : K ≠ 0 := hK.ne'
  have hinv2 : a⁻¹ ^ 2 ≤ 1 := by
    have h1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
    have h0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
    nlinarith
  have hgpos : 0 < UnforcedLeray.B0113.gw a y := Real.exp_pos _
  have hgle := gw_le ha haK y
  have habs : |UnforcedLeray.B0146.u1 a y| = a⁻¹ ^ 2 * |y.2| * UnforcedLeray.B0113.gw a y := by
    unfold UnforcedLeray.B0146.u1
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a⁻¹ ^ 2),
      abs_of_pos hgpos]
  rw [habs]
  have hy2 : 0 ≤ |y.2| := abs_nonneg _
  have hsplit : Real.exp (-((y.1 ^ 2 + y.2 ^ 2) / (4 * K))) =
      Real.exp (-(y.2 ^ 2 / (4 * K))) * Real.exp (-(y.1 ^ 2 / (4 * K))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbase : |y.2| * Real.exp (-(y.2 ^ 2 / (4 * K))) ≤ K + 1 := by
    have hα : (0 : ℝ) < 1 / (4 * K) := div_pos one_pos (by linarith)
    have h := t_mul_exp_le (α := 1 / (4 * K)) (t := |y.2|) hα (abs_nonneg _)
    rw [sq_abs] at h
    have e1 : -(1 / (4 * K) * y.2 ^ 2) = -(y.2 ^ 2 / (4 * K)) := by ring
    rw [e1] at h
    have e2 : 1 / (4 * (1 / (4 * K))) = K := by
      field_simp
    rw [e2] at h
    exact h
  have hexpnn : 0 ≤ Real.exp (-(y.1 ^ 2 / (4 * K))) := (Real.exp_pos _).le
  have hdecay : Real.exp (-(y.1 ^ 2 / (4 * K))) ≤ Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have : (1 / (8 * K)) * y.1 ^ 2 ≤ y.1 ^ 2 / (4 * K) := by
      rw [div_mul_eq_mul_div, one_mul]
      have hK0' : 0 < 8 * K := by linarith
      rw [div_le_div_iff₀ hK0' (by linarith)]
      nlinarith [mul_nonneg hK.le (sq_nonneg y.1)]
    linarith
  calc a⁻¹ ^ 2 * |y.2| * UnforcedLeray.B0113.gw a y
      ≤ 1 * |y.2| * (Real.exp (-(y.2 ^ 2 / (4 * K))) * Real.exp (-(y.1 ^ 2 / (4 * K)))) := by
        rw [← hsplit]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hinv2 hy2) hgle hgpos.le (by positivity)
    _ = (|y.2| * Real.exp (-(y.2 ^ 2 / (4 * K)))) * Real.exp (-(y.1 ^ 2 / (4 * K))) := by ring
    _ ≤ (K + 1) * Real.exp (-(y.1 ^ 2 / (4 * K))) :=
        mul_le_mul_of_nonneg_right hbase hexpnn
    _ ≤ (K + 1) * Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) :=
        mul_le_mul_of_nonneg_left hdecay (by linarith)
    _ ≤ (2 * K + 1) * Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- `|u2 a y| ≤ (2K+1) exp(-(1/(8K)) y.1²)` for `1 ≤ a ≤ K`. -/
theorem abs_u2_le {a K : ℝ} (ha : 1 ≤ a) (haK : a ≤ K) (y : ℝ × ℝ) :
    |UnforcedLeray.B0146.u2 a y| ≤ (2 * K + 1) * Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) := by
  have ha0 : 0 < a := by linarith
  have hK : 0 < K := lt_of_lt_of_le ha0 haK
  have hK0 : K ≠ 0 := hK.ne'
  have hinv2 : a⁻¹ ^ 2 ≤ 1 := by
    have h1 : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
    have h0 : 0 ≤ a⁻¹ := inv_nonneg.mpr ha0.le
    nlinarith
  have hgpos : 0 < UnforcedLeray.B0113.gw a y := Real.exp_pos _
  have hgle := gw_le ha haK y
  have habs : |UnforcedLeray.B0146.u2 a y| = a⁻¹ ^ 2 * |y.1| * UnforcedLeray.B0113.gw a y := by
    unfold UnforcedLeray.B0146.u2
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ a⁻¹ ^ 2),
      abs_of_pos hgpos]
  rw [habs]
  have hy1 : 0 ≤ |y.1| := abs_nonneg _
  have hsplit : Real.exp (-((y.1 ^ 2 + y.2 ^ 2) / (4 * K))) =
      Real.exp (-(y.2 ^ 2 / (4 * K))) * Real.exp (-(y.1 ^ 2 / (4 * K))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpy2 : Real.exp (-(y.2 ^ 2 / (4 * K))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ y.2 ^ 2 / (4 * K) := div_nonneg (sq_nonneg _) (by linarith)
    linarith
  have hbase : |y.1| * Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) ≤ 2 * K + 1 := by
    have hα : (0 : ℝ) < 1 / (8 * K) := div_pos one_pos (by linarith)
    have h := t_mul_exp_le (α := 1 / (8 * K)) (t := |y.1|) hα (abs_nonneg _)
    rw [sq_abs] at h
    have e2 : 1 / (4 * (1 / (8 * K))) = 2 * K := by
      field_simp
      ring
    rw [e2] at h
    exact h
  have hexpnn : 0 ≤ Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) := (Real.exp_pos _).le
  have hdecay : Real.exp (-(y.1 ^ 2 / (4 * K))) ≤ Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have : (1 / (8 * K)) * y.1 ^ 2 ≤ y.1 ^ 2 / (4 * K) := by
      rw [div_mul_eq_mul_div, one_mul]
      have hK0' : 0 < 8 * K := by linarith
      rw [div_le_div_iff₀ hK0' (by linarith)]
      nlinarith [mul_nonneg hK.le (sq_nonneg y.1)]
    linarith
  have hsplit2 : Real.exp (-(y.1 ^ 2 / (4 * K))) =
      Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) * Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc a⁻¹ ^ 2 * |y.1| * UnforcedLeray.B0113.gw a y
      ≤ 1 * |y.1| * (Real.exp (-(y.2 ^ 2 / (4 * K))) * Real.exp (-(y.1 ^ 2 / (4 * K)))) := by
        rw [← hsplit]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hinv2 hy1) hgle hgpos.le (by positivity)
    _ ≤ 1 * |y.1| * (1 * Real.exp (-(y.1 ^ 2 / (4 * K)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right hexpy2 (Real.exp_pos _).le
    _ = |y.1| * Real.exp (-(y.1 ^ 2 / (4 * K))) := by ring
    _ = (|y.1| * Real.exp (-((1 / (8 * K)) * y.1 ^ 2))) *
          Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) := by
        rw [hsplit2]
        ring
    _ ≤ (2 * K + 1) * Real.exp (-((1 / (8 * K)) * y.1 ^ 2)) :=
        mul_le_mul_of_nonneg_right hbase hexpnn

end UnforcedLeray.Short.IIb.TrainGap
