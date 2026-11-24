import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2

/-!
# The dilated weight: bounds and `σ`-derivative (helper of `FmrDeriv`)

Source of record: `the November 2 reference manuscript`, lines 2937-2946.
For `a = clockA ν σ ≥ 1`: `p_a ≤ jb^m` and `|∂_σ p| ≤ ν m jb^m`, and `∂_σ p_{a(σ)} = movWeightDt`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

open MeasureTheory Set Filter Topology

theorem fd_clockA_ge_one {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 ≤ σ) : 1 ≤ clockA ν σ := by
  unfold clockA; nlinarith

theorem fd_weight_base_le (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 ≤ σ) (x : B0579.Plane) :
    1 + (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ ≤ B0579.jb x := by
  have ha := fd_clockA_ge_one hν hσ
  have h0 : (x.1 ^ 2 + x.2 ^ 2) / clockA ν σ ≤ x.1 ^ 2 + x.2 ^ 2 :=
    div_le_self (by positivity) ha
  unfold B0579.jb; linarith

theorem fd_weight_le (ν σ m : ℝ) (hν : 0 < ν) (hσ : 0 ≤ σ) (hm : 0 ≤ m) (x : B0579.Plane) :
    movWeight m (clockA ν σ) x ≤ B0579.jb x  ^ m := by
  unfold movWeight
  have ha := fd_clockA_ge_one hν hσ
  exact Real.rpow_le_rpow (add_nonneg zero_le_one (div_nonneg (by positivity) (by linarith)))
    (fd_weight_base_le ν σ hν hσ x) hm

theorem fd_weightDt_le (ν σ m : ℝ) (hν : 0 < ν) (hσ : 0 ≤ σ) (hm : 0 ≤ m) (x : B0579.Plane) :
    |movWeightDt ν m (clockA ν σ) x| ≤ ν * m * B0579.jb x ^ m := by
  have ha := fd_clockA_ge_one hν hσ
  set a := clockA ν σ with ha_def
  have ha0 : 0 < a := by linarith
  set r := x.1 ^ 2 + x.2 ^ 2 with hr
  have hr0 : 0 ≤ r := by positivity
  set b := 1 + r / a with hb
  have hb0 : 0 < b := by positivity
  have hbj : b ≤ B0579.jb x := fd_weight_base_le ν σ hν hσ x
  have hbm : b ^ m ≤ B0579.jb x ^ m := Real.rpow_le_rpow hb0.le hbj hm
  have hrb : r / a ^ 2 ≤ b := by
    have h1 : r / a ^ 2 ≤ r / a := by
      rw [div_le_div_iff₀ (by positivity) ha0]
      nlinarith [mul_nonneg hr0 (mul_nonneg (sub_nonneg.2 ha) ha0.le)]
    linarith
  have hbb : b ^ (m - 1) * b = b ^ m := by
    rw [← Real.rpow_add_one hb0.ne']; ring_nf
  unfold movWeightDt
  rw [← hr, ← hb]
  have : |-(ν * m / a ^ 2) * r * b ^ (m - 1)| = ν * m * (r / a ^ 2) * b ^ (m - 1) := by
    have hp : 0 ≤ b ^ (m - 1) := Real.rpow_nonneg hb0.le _
    rw [show -(ν * m / a ^ 2) * r * b ^ (m - 1) = -(ν * m * (r / a ^ 2) * b ^ (m - 1)) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
  rw [this]
  calc ν * m * (r / a ^ 2) * b ^ (m - 1) ≤ ν * m * b * b ^ (m - 1) := by
        have hp : 0 ≤ b ^ (m - 1) := Real.rpow_nonneg hb0.le _
        have : 0 ≤ ν * m := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrb this) hp
    _ = ν * m * b ^ m := by rw [← hbb]; ring
    _ ≤ ν * m * B0579.jb x ^ m := mul_le_mul_of_nonneg_left hbm (by positivity)

theorem fd_weight_hasDeriv (ν σ m : ℝ) (hν : 0 < ν) (ha : 0 < clockA ν σ) (x : B0579.Plane) :
    HasDerivAt (fun r => movWeight m (clockA ν r) x) (movWeightDt ν m (clockA ν σ) x) σ := by
  have hA : HasDerivAt (fun r => clockA ν r) ν σ := by
    unfold clockA
    simpa using ((hasDerivAt_id σ).const_mul ν).const_add 1
  have hI := hA.inv ha.ne'
  have hD := (hI.const_mul (x.1 ^ 2 + x.2 ^ 2)).const_add 1
  have hbase : 0 < 1 + (x.1 ^ 2 + x.2 ^ 2) * (clockA ν σ)⁻¹ :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg (by positivity) (inv_nonneg.2 ha.le))
  have hR := hD.rpow_const (p := m) (Or.inl hbase.ne')
  unfold movWeight movWeightDt
  convert hR using 1
  · funext r; simp [div_eq_mul_inv]
  · simp only [Pi.inv_apply, div_eq_mul_inv]; ring

end UnforcedLeray.Short.IIIa
