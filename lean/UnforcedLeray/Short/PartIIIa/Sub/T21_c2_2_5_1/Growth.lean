import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2_5_1

/-!
# `PartIII-a:T21/c2/2/5/1`, leaf `MwGrowth`: growth of the dilated weight (SP 2950-2954)

`p = w^m`, `w = 1 + |x|²/a ≥ 1`: `|∂_j p| ≤ m (1+1/a) w^m`, `|Δp| ≤ (4m/a)(1+|m-1|) w^m`,
and `w ≤ max 1 (1/a) · jb`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Short.IIb

namespace UnforcedLeray.Short.IIIa

theorem mwg_abs_two_div (a t s : ℝ) (ha : 0 < a) :
    |2 * t / a| ≤ (1 + 1 / a) * (1 + (t ^ 2 + s ^ 2) / a) := by
  have he : 0 < 1 / a := by positivity
  have e1 : 2 * t / a = 2 * t * (1 / a) := by ring
  have e2 : (t ^ 2 + s ^ 2) / a = (t ^ 2 + s ^ 2) * (1 / a) := by ring
  rw [e1, e2]
  generalize 1 / a = e at he ⊢
  rw [abs_le]
  have h1 := mul_nonneg he.le (sq_nonneg (t - 1))
  have h2 := mul_nonneg he.le (sq_nonneg (t + 1))
  have h3 := mul_nonneg (mul_nonneg he.le he.le) (add_nonneg (sq_nonneg t) (sq_nonneg s))
  have h4 := mul_nonneg he.le (sq_nonneg s)
  constructor <;> nlinarith

theorem mwg_rpow_sub_one (w m : ℝ) (hw : 0 < w) : w ^ (m - 1) * w = w ^ m := by
  have := Real.rpow_add_one hw.ne' (m - 1)
  rw [sub_add_cancel] at this
  exact this.symm

theorem mwg_rpow_sub_one_le (w m : ℝ) (hw : 1 ≤ w) : w ^ (m - 1) ≤ w ^ m :=
  Real.rpow_le_rpow_of_exponent_le hw (by linarith)

theorem mwg_pt (m a : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (x : B0579.Plane) :
    |movWeight m a x| + |B0579.pd 0 (movWeight m a) x| + |B0579.pd 1 (movWeight m a) x| +
      |lapP (movWeight m a) x| ≤
    (1 + 2 * (m * (1 + 1 / a)) + (4 * m / a) * (1 + |m - 1|)) *
      (1 + (x.1 ^ 2 + x.2 ^ 2) / a) ^ m := by
  obtain ⟨t, s⟩ := x
  simp only
  set w := 1 + (t ^ 2 + s ^ 2) / a with hwdef
  have hu : 0 ≤ (t ^ 2 + s ^ 2) / a := div_nonneg (by positivity) ha.le
  have hw1 : 1 ≤ w := by rw [hwdef]; linarith
  have hw0 : 0 < w := by linarith
  have hwm : 0 ≤ w ^ m := Real.rpow_nonneg hw0.le m
  have hwm1 : 0 ≤ w ^ (m - 1) := Real.rpow_nonneg hw0.le _
  have hwm2 : 0 ≤ w ^ (m - 2) := Real.rpow_nonneg hw0.le _
  have e := mwg_rpow_sub_one w m hw0
  have e' := mwg_rpow_sub_one w (m - 1) hw0
  rw [show m - 1 - 1 = m - 2 by ring] at e'
  have le1 := mwg_rpow_sub_one_le w m hw1
  have hpt : |movWeight m a (t, s)| = w ^ m := by
    unfold movWeight; simp only; rw [abs_of_nonneg hwm]
  have hp0 : |B0579.pd 0 (movWeight m a) (t, s)| ≤ m * (1 + 1 / a) * w ^ m := by
    rw [fmrIso_pd0 m a ha]
    simp only
    rw [abs_mul, abs_mul, abs_of_nonneg hm, abs_of_nonneg hwm1]
    have h := mwg_abs_two_div a t s ha
    calc m * w ^ (m - 1) * |2 * t / a| ≤ m * w ^ (m - 1) * ((1 + 1 / a) * w) := by gcongr
      _ = m * (1 + 1 / a) * (w ^ (m - 1) * w) := by ring
      _ = _ := by rw [e]
  have hp1 : |B0579.pd 1 (movWeight m a) (t, s)| ≤ m * (1 + 1 / a) * w ^ m := by
    rw [fmrIso_pd1 m a ha]
    simp only
    rw [abs_mul, abs_mul, abs_of_nonneg hm, abs_of_nonneg hwm1]
    have h := mwg_abs_two_div a s t ha
    rw [add_comm (s ^ 2) (t ^ 2)] at h
    calc m * w ^ (m - 1) * |2 * s / a| ≤ m * w ^ (m - 1) * ((1 + 1 / a) * w) := by gcongr
      _ = m * (1 + 1 / a) * (w ^ (m - 1) * w) := by ring
      _ = _ := by rw [e]
  have hl : |lapP (movWeight m a) (t, s)| ≤ (4 * m / a) * (1 + |m - 1|) * w ^ m := by
    rw [fmrBracket_lapP m a ha]
    simp only
    have hq : (t ^ 2 + s ^ 2) / a ^ 2 = ((t ^ 2 + s ^ 2) / a) * (1 / a) := by
      field_simp
    have hea : 0 < 1 / a := by positivity
    have hca : 0 ≤ 4 * m / a := by positivity
    refine (abs_add_le _ _).trans ?_
    have t1 : |4 * m / a * w ^ (m - 1)| ≤ 4 * m / a * w ^ m := by
      rw [abs_of_nonneg (mul_nonneg hca hwm1)]
      exact mul_le_mul_of_nonneg_left le1 hca
    have t2 : |4 * m * (m - 1) * ((t ^ 2 + s ^ 2) / a ^ 2) * w ^ (m - 2)| ≤
        4 * m / a * |m - 1| * w ^ m := by
      rw [hq, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hwm2,
        abs_of_nonneg hu, abs_of_nonneg hea.le, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
        abs_of_nonneg hm]
      have hu' : (t ^ 2 + s ^ 2) / a ≤ w := by rw [hwdef]; linarith
      have hh : (t ^ 2 + s ^ 2) / a * (1 / a) * w ^ (m - 2) ≤ (1 / a) * w ^ m := by
        calc (t ^ 2 + s ^ 2) / a * (1 / a) * w ^ (m - 2) ≤ w * (1 / a) * w ^ (m - 2) := by gcongr
          _ = (1 / a) * (w ^ (m - 2) * w) := by ring
          _ = (1 / a) * w ^ (m - 1) := by rw [e']
          _ ≤ (1 / a) * w ^ m := mul_le_mul_of_nonneg_left le1 hea.le
      calc 4 * m * |m - 1| * ((t ^ 2 + s ^ 2) / a * (1 / a)) * w ^ (m - 2)
          = 4 * m * |m - 1| * ((t ^ 2 + s ^ 2) / a * (1 / a) * w ^ (m - 2)) := by ring
        _ ≤ 4 * m * |m - 1| * ((1 / a) * w ^ m) := by gcongr
        _ = 4 * m / a * |m - 1| * w ^ m := by ring
    calc _ ≤ 4 * m / a * w ^ m + 4 * m / a * |m - 1| * w ^ m := add_le_add t1 t2
      _ = _ := by ring
  rw [hpt]
  nlinarith [hp0, hp1, hl]

theorem mwg_w_le (a : ℝ) (ha : 0 < a) (x : B0579.Plane) :
    1 + (x.1 ^ 2 + x.2 ^ 2) / a ≤ max 1 (1 / a) * B0579.jb x := by
  unfold B0579.jb
  have h1 : (1 : ℝ) ≤ max 1 (1 / a) := le_max_left _ _
  have h2 : 1 / a ≤ max 1 (1 / a) := le_max_right _ _
  have e : (x.1 ^ 2 + x.2 ^ 2) / a = (x.1 ^ 2 + x.2 ^ 2) * (1 / a) := by ring
  rw [e]
  have hq : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hq]

theorem mwGrowth : MwGrowth := by
  intro m a hm ha
  refine ⟨(1 + 2 * (m * (1 + 1 / a)) + (4 * m / a) * (1 + |m - 1|)) * max 1 (1 / a) ^ m,
    fun x => ?_⟩
  refine (mwg_pt m a hm ha x).trans ?_
  have hC : 0 ≤ 1 + 2 * (m * (1 + 1 / a)) + (4 * m / a) * (1 + |m - 1|) := by positivity
  have hw0 : 0 ≤ 1 + (x.1 ^ 2 + x.2 ^ 2) / a := (movWeight_base_pos a ha x).le
  have := Real.rpow_le_rpow hw0 (mwg_w_le a ha x) hm
  rw [Real.mul_rpow (by positivity) (B0579.jb_pos x).le] at this
  calc _ ≤ (1 + 2 * (m * (1 + 1 / a)) + (4 * m / a) * (1 + |m - 1|)) *
        (max 1 (1 / a) ^ m * B0579.jb x ^ m) := mul_le_mul_of_nonneg_left this hC
    _ = _ := by ring

end UnforcedLeray.Short.IIIa
