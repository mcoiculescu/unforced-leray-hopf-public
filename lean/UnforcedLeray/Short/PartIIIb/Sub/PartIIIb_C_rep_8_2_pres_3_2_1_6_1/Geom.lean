import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_Lem

/-!
# Chain-rule bound for `p_lift = s · p_cyl ∘ chart` (geometry)

Source `the November 2 reference manuscript`
lines 1213-1225 (`p_raw = (R/r)² p`, `p_lift = s p_cyl`), 2073-2075 (chart `s = R²/ϱ²`,
`η = R y₃/ϱ`).  For a profile `P` differentiable at the chart point `x = chart R τ y`, with
`|P x| ≤ B` and `‖DP x‖ ≤ B`:
`|s P(x)| ≤ s B` and `‖∇_y (s P∘chart)‖ ≤ 3 (B/ϱ) s (2s + 2R + |η| + 2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem lpc_abs_coord_le {y : Space} (hy : y ∉ axis) (j : Fin 3) :
    |ϱD y (coordinateVector j)| ≤ 1 ∧ |(coordinateVector j) 2| ≤ 1 := by
  have hρ := ϱ_pos hy
  have h0 : |y 0| ≤ ϱ y := by
    unfold ϱ
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 1)])
  have h1 : |y 1| ≤ ϱ y := by
    unfold ϱ
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (y 0)])
  rw [ϱD_apply]
  fin_cases j <;> simp [coordinateVector]
  · rw [abs_div, abs_of_pos hρ, div_le_one hρ]; exact h0
  · rw [abs_div, abs_of_pos hρ, div_le_one hρ]; exact h1

theorem lpc_norm_toLp_le (x : Fin 3 → ℝ) :
    ‖(WithLp.toLp 2 x : Space)‖ ≤ |x 0| + |x 1| + |x 2| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  nlinarith [abs_nonneg (x 0), abs_nonneg (x 1), abs_nonneg (x 2), sq_abs (x 0), sq_abs (x 1),
    sq_abs (x 2), mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 1)),
    mul_nonneg (abs_nonneg (x 0)) (abs_nonneg (x 2)),
    mul_nonneg (abs_nonneg (x 1)) (abs_nonneg (x 2))]

/-- Directional bound for one test direction `v` with `|Dϱ v| ≤ 1`, `|v₃| ≤ 1`. -/
theorem lpc_dir_bound {R τ : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ axis)
    {P : ℝ × (ℝ × ℝ) → ℝ} (hP : DifferentiableAt ℝ P (chart R τ y)) {B : ℝ} (hB0 : 0 ≤ B)
    (h0 : |P (chart R τ y)| ≤ B) (h1 : ‖fderiv ℝ P (chart R τ y)‖ ≤ B)
    (v : Space) (hv1 : |ϱD y v| ≤ 1) (hv2 : |v 2| ≤ 1) :
    |fderiv ℝ (fun y => age R y * P (chart R τ y)) y v| ≤
      (B / ϱ y) * age R y * (2 * age R y + 2 * R + |Axi.trans R y| + 2) := by
  have hρ := ϱ_pos hy
  have hR0 := hR.ne'
  have hc : HasFDerivAt (fun y => P (chart R τ y))
      ((fderiv ℝ P (chart R τ y)).comp (chartD R y)) y :=
    hP.hasFDerivAt.comp y (hasFDerivAt_chart hR0 τ hy)
  have hq : HasFDerivAt (fun y => age R y * P (chart R τ y))
      (age R y • (fderiv ℝ P (chart R τ y)).comp (chartD R y) +
        P (chart R τ y) • ageD R y) y := (hasFDerivAt_age R hy).mul hc
  have hform : fderiv ℝ (fun y => age R y * P (chart R τ y)) y v =
      age R y * (fderiv ℝ P (chart R τ y) (chartD R y v)) +
        P (chart R τ y) * ageD R y v := by
    rw [hq.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
  set L := fderiv ℝ P (chart R τ y) with hL
  set s := age R y with hs
  have hs0 : 0 < s := age_pos hR0 hy
  have hsr : s = R ^ 2 / ϱ y ^ 2 := rfl
  have e1 : |L (1, (0, 0))| ≤ B := by
    refine le_trans ?_ h1
    have := L.le_opNorm (1, (0, 0))
    simpa [Prod.norm_def] using this
  have e2 : |L (0, (1, 0))| ≤ B := by
    refine le_trans ?_ h1
    have := L.le_opNorm (0, (1, 0))
    simpa [Prod.norm_def] using this
  have e3 : |L (0, (0, 1))| ≤ B := by
    refine le_trans ?_ h1
    have := L.le_opNorm (0, (0, 1))
    simpa [Prod.norm_def] using this
  set a := ϱD y v with ha
  have hageD : ageD R y v = -(2 * R ^ 2 / ϱ y ^ 3) * a := by
    simp [ageD, ha]
  have hη : |Axi.trans R y| = R * |y 2| / ϱ y := by
    unfold Axi.trans
    rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos hρ]
  set a1 : ℝ := -(2 * R ^ 2 / ϱ y ^ 3) * a with ha1
  set a2 : ℝ := R / ϱ y * a with ha2
  set a3 : ℝ := R / ϱ y * v 2 - R * y 2 / ϱ y ^ 2 * a with ha3
  have hform2 : fderiv ℝ (fun y => age R y * P (chart R τ y)) y v =
      s * (a1 * L (1, (0, 0)) + a2 * L (0, (1, 0)) + a3 * L (0, (0, 1))) +
        P (chart R τ y) * a1 := by
    rw [hform, chartD_apply, clm_triple, hageD]
    simp only [smul_eq_mul]
    rfl
  rw [hform2]
  have c1 : |a1| ≤ 2 * s / ϱ y := by
    rw [ha1, neg_mul, abs_neg, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * R ^ 2 / ϱ y ^ 3)]
    have : 2 * R ^ 2 / ϱ y ^ 3 = 2 * s / ϱ y := by rw [hsr]; field_simp
    rw [this]
    calc 2 * s / ϱ y * |a| ≤ 2 * s / ϱ y * 1 := by
          apply mul_le_mul_of_nonneg_left hv1; positivity
      _ = _ := mul_one _
  have c2 : |a2| ≤ R / ϱ y := by
    rw [ha2, abs_mul, abs_of_pos (by positivity : (0:ℝ) < R / ϱ y)]
    calc R / ϱ y * |a| ≤ R / ϱ y * 1 := mul_le_mul_of_nonneg_left hv1 (by positivity)
      _ = _ := mul_one _
  have c3 : |a3| ≤ (R + |Axi.trans R y|) / ϱ y := by
    have t1 : |R / ϱ y * v 2| ≤ R / ϱ y := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < R / ϱ y)]
      calc R / ϱ y * |v 2| ≤ R / ϱ y * 1 := mul_le_mul_of_nonneg_left hv2 (by positivity)
        _ = _ := mul_one _
    have t2 : |R * y 2 / ϱ y ^ 2 * a| ≤ |Axi.trans R y| / ϱ y := by
      rw [abs_mul, hη]
      have : |R * y 2 / ϱ y ^ 2| = R * |y 2| / ϱ y / ϱ y := by
        rw [abs_div, abs_mul, abs_of_pos hR, abs_of_pos (by positivity : (0:ℝ) < ϱ y ^ 2)]
        field_simp
      rw [this]
      calc R * |y 2| / ϱ y / ϱ y * |a| ≤ R * |y 2| / ϱ y / ϱ y * 1 :=
            mul_le_mul_of_nonneg_left hv1 (by positivity)
        _ = _ := mul_one _
    calc |a3| ≤ |R / ϱ y * v 2| + |R * y 2 / ϱ y ^ 2 * a| := abs_sub _ _
      _ ≤ R / ϱ y + |Axi.trans R y| / ϱ y := add_le_add t1 t2
      _ = _ := by ring
  have hB : 0 ≤ B := hB0
  have ht : 0 ≤ |Axi.trans R y| := abs_nonneg _
  have T1 : |a1 * L (1, (0, 0)) + a2 * L (0, (1, 0)) + a3 * L (0, (0, 1))| ≤
      (2 * s / ϱ y) * B + (R / ϱ y) * B + ((R + |Axi.trans R y|) / ϱ y) * B := by
    refine le_trans (abs_add_three _ _ _) ?_
    refine add_le_add (add_le_add ?_ ?_) ?_
    · rw [abs_mul]; exact mul_le_mul c1 e1 (abs_nonneg _) (by positivity)
    · rw [abs_mul]; exact mul_le_mul c2 e2 (abs_nonneg _) (by positivity)
    · rw [abs_mul]; exact mul_le_mul c3 e3 (abs_nonneg _) (by positivity)
  have T2 : |P (chart R τ y) * a1| ≤ B * (2 * s / ϱ y) := by
    rw [abs_mul]
    exact mul_le_mul h0 c1 (abs_nonneg _) hB
  have T4 : |s * (a1 * L (1, (0, 0)) + a2 * L (0, (1, 0)) + a3 * L (0, (0, 1)))| ≤
      s * ((2 * s / ϱ y) * B + (R / ϱ y) * B + ((R + |Axi.trans R y|) / ϱ y) * B) := by
    rw [abs_mul, abs_of_pos hs0]
    exact mul_le_mul_of_nonneg_left T1 hs0.le
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ s * ((2 * s / ϱ y) * B + (R / ϱ y) * B + ((R + |Axi.trans R y|) / ϱ y) * B) +
        B * (2 * s / ϱ y) := add_le_add T4 T2
    _ = (B / ϱ y) * s * (2 * s + 2 * R + |Axi.trans R y| + 2) := by
        field_simp
        ring

/-- Gradient bound (sum of the three coordinate directions). -/
theorem lpc_grad_bound {R τ : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ axis)
    {P : ℝ × (ℝ × ℝ) → ℝ} (hP : DifferentiableAt ℝ P (chart R τ y)) {B : ℝ} (hB0 : 0 ≤ B)
    (h0 : |P (chart R τ y)| ≤ B) (h1 : ‖fderiv ℝ P (chart R τ y)‖ ≤ B) :
    ‖physGrad (fun y => age R y * P (chart R τ y)) y‖ ≤
      3 * ((B / ϱ y) * age R y * (2 * age R y + 2 * R + |Axi.trans R y| + 2)) := by
  unfold physGrad
  refine le_trans (lpc_norm_toLp_le _) ?_
  have h := fun j : Fin 3 => lpc_dir_bound hR hy hP hB0 h0 h1 (coordinateVector j)
    (lpc_abs_coord_le hy j).1 (lpc_abs_coord_le hy j).2
  have := h 0
  have := h 1
  have := h 2
  linarith [h 0, h 1, h 2]

end UnforcedLeray.Short.PartIIIb.Concrete

end
