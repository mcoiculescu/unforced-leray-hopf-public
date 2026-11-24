import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.PhysFromMoving

/-!
# Terminal energy of the reverse-time adjoint (SP 3044-3047)

`adjointTerminalBound`: at the terminal age the moving adjoint equals the terminal datum `G`
(`revAge ν s 0 = s`, `movingPhi = G` a.e. on the cell), and on the cell the periodic weight
satisfies `p_d⁻¹ ≤ (4/π²)^{-m} ⟨y⟩^{-2m}` (`|sin u| ≥ (2/π)|u|` on `|u| ≤ π/2`), so that
`E_0(0) ≤ C ‖G‖²_{X_{-m,d_s}}` with `C = (4/π²)^{-m}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Sine bound on the cell: `(4/π²)⟨y⟩² ≤ 1 + y₂² + (d/π)² sin²(π y₁/d)` for `y ∈ C_d`. -/
theorem tb_sin_bound {d : ℝ} (hd : 0 < d) (y : ℝ × ℝ) (hy : y ∈ B0579.cell d) :
    4 / Real.pi ^ 2 * B0579.jb y ≤
      1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by
  simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hy
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hdne : d ≠ 0 := hd.ne'
  have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hx1 : Real.pi * y.1 / d ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hd]
    nlinarith [mul_pos hpi (show 0 < d / 2 - y.1 by linarith [hy.2])]
  have hx2 : -(Real.pi / 2) ≤ Real.pi * y.1 / d := by
    rw [le_div_iff₀ hd]
    nlinarith [mul_nonneg hpi.le (show 0 ≤ y.1 + d / 2 by linarith [hy.1])]
  have habs : |Real.pi * y.1 / d| ≤ Real.pi / 2 := abs_le.2 ⟨hx2, hx1⟩
  have hJ : 2 / Real.pi * |Real.pi * y.1 / d| ≤ Real.sin |Real.pi * y.1 / d| :=
    Real.mul_le_sin (abs_nonneg _) habs
  have hJ2 : (2 / Real.pi * |Real.pi * y.1 / d|) ^ 2 ≤ Real.sin |Real.pi * y.1 / d| ^ 2 :=
    pow_le_pow_left₀ (by positivity) hJ 2
  have hsinabs : Real.sin |Real.pi * y.1 / d| ^ 2 = Real.sin (Real.pi * y.1 / d) ^ 2 := by
    rcases abs_choice (Real.pi * y.1 / d) with h | h
    · rw [h]
    · rw [h, Real.sin_neg, neg_sq]
  have hsq : (2 / Real.pi * |Real.pi * y.1 / d|) ^ 2 =
      (2 / Real.pi) ^ 2 * (Real.pi * y.1 / d) ^ 2 := by
    rw [mul_pow, sq_abs]
  have hkey : (d / Real.pi) ^ 2 * ((2 / Real.pi) ^ 2 * (Real.pi * y.1 / d) ^ 2) =
      4 / Real.pi ^ 2 * y.1 ^ 2 := by
    field_simp
    ring
  have hJ3 : (2 / Real.pi) ^ 2 * (Real.pi * y.1 / d) ^ 2 ≤ Real.sin (Real.pi * y.1 / d) ^ 2 := by
    have h := hJ2
    rw [hsq, hsinabs] at h
    exact h
  have hsin_lb : 4 / Real.pi ^ 2 * y.1 ^ 2 ≤ (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by
    rw [← hkey]
    exact mul_le_mul_of_nonneg_left hJ3 (sq_nonneg _)
  have hk1 : 4 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hk0 : 0 ≤ 4 / Real.pi ^ 2 := by positivity
  unfold B0579.jb
  nlinarith [sq_nonneg y.2, hsin_lb, hk1, hk0, mul_le_mul_of_nonneg_right hk1 (sq_nonneg y.2)]

/-- The periodic weight on the cell: `p_d⁻¹ ≤ (4/π²)^{-m} ⟨y⟩^{-2m}` for `m ≥ 0`. -/
theorem tb_pw_le {m d : ℝ} (hm : 0 ≤ m) (hd : 0 < d) (y : ℝ × ℝ) (hy : y ∈ B0579.cell d) :
    periodicWeight (-m) d y ≤ (4 / Real.pi ^ 2) ^ (-m) * B0579.jb y ^ (-m) := by
  have hpos : 0 < 4 / Real.pi ^ 2 * B0579.jb y := mul_pos (by positivity) (B0579.jb_pos y)
  have h := Real.rpow_le_rpow_of_nonpos hpos (tb_sin_bound hd y hy) (neg_nonpos.2 hm)
  unfold periodicWeight
  rw [Real.mul_rpow (by positivity) (B0579.jb_pos y).le] at h
  exact h

/-- The weighted `L²` norm squared as a real integral. -/
theorem tb_sq_xNorm {c m : ℝ} {G : ℝ × ℝ → ℂ} (hG : MemLp G 2 (B0579.cellMeasure c m)) :
    (xNorm c m G).toReal ^ 2 = ∫ x in B0579.cell c, B0579.jb x ^ m * ‖G x‖ ^ 2 := by
  unfold xNorm
  rw [hG.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hI : 0 ≤ ∫ x, ‖G x‖ ^ (2 : ℝ) ∂(B0579.cellMeasure c m) :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_natCast, ← Real.rpow_mul hI]
  rw [show (2 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  rw [B0579.cellMeasure, integral_withDensity_eq_integral_smul (B0579.measurable_density m)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, B0579.coe_density, Real.rpow_two, smul_eq_mul]

/-- Integrability of the weighted square on the cell. -/
theorem tb_integrable {c m : ℝ} {G : ℝ × ℝ → ℂ} (hG : MemLp G 2 (B0579.cellMeasure c m)) :
    Integrable (fun x => B0579.jb x ^ m * ‖G x‖ ^ 2) (volume.restrict (B0579.cell c)) := by
  have hI : Integrable (fun x => ‖G x‖ ^ (2 : ℝ≥0∞).toReal) (B0579.cellMeasure c m) :=
    hG.integrable_norm_rpow (by norm_num) (by norm_num)
  unfold B0579.cellMeasure at hI
  rw [integrable_withDensity_iff_integrable_smul (B0579.measurable_density m)] at hI
  refine hI.congr (Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, B0579.coe_density, ENNReal.toReal_ofNat, Real.rpow_two, smul_eq_mul]

/-- **Terminal energy** (SP 3044-3047): `E_0(0) ≤ C_m ‖G‖²_{X_{-m,d_s}}`. -/
theorem adjointTerminalBound (m : ℝ) (hm : 0 ≤ m) : AdjointTerminalBound m := by
  refine ⟨(4 / Real.pi ^ 2) ^ (-m), Real.rpow_nonneg (by positivity) _, ?_⟩
  intro ν hν tr t s ht hts G hG φ hφ
  have hc : (0 : ℝ) < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hs0 : 0 < s := lt_of_le_of_lt ht hts
  have ha : 0 < clockA ν s := by
    unfold clockA
    nlinarith [mul_pos hν hs0]
  have hA : clockA ν s ≠ 0 := ha.ne'
  have hr : revAge ν s 0 = s := by
    unfold revAge ageOfZ movingZ
    rw [sub_zero]
    have h1 : 1 - ν * (s / clockA ν s) = 1 / clockA ν s := by
      field_simp
      unfold clockA
      ring
    rw [h1]
    field_simp
  have hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν s) := div_pos hc (Real.sqrt_pos.2 ha)
  have hdc : cellLen (ν ^ (-2 : ℝ)) (clockA ν s) * Real.sqrt (clockA ν s) = ν ^ (-2 : ℝ) := by
    unfold cellLen
    exact div_mul_cancel₀ _ (Real.sqrt_pos.2 ha).ne'
  have hae : ∀ᵐ y ∂(volume.restrict (B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)))),
      movingPhi ν φ s y = G y := by
    have hJ := jscaleInv_ae_volume ha hd hdc hφ.terminal
    have hsq : Real.sqrt (clockA ν s) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
    filter_upwards [hJ, ae_restrict_mem (B0579.measurableSet_cell _)] with y hy _
    have e1 : Real.sqrt (clockA ν s) * y.1 / Real.sqrt (clockA ν s) = y.1 :=
      mul_div_cancel_left₀ _ hsq
    have e2 : Real.sqrt (clockA ν s) * y.2 / Real.sqrt (clockA ν s) = y.2 :=
      mul_div_cancel_left₀ _ hsq
    simp only [JscaleInv, physAdj, e1, e2] at hy
    have hA2 : ((clockA ν s ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 ha.ne'
    have h2 := mul_left_cancel₀ hA2 hy
    unfold movingPhi
    rw [h2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha.ne', Complex.ofReal_one,
      one_mul]
  unfold revE0 adjE0
  rw [hr, tb_sq_xNorm hG, ← integral_const_mul]
  refine integral_mono_of_nonneg
    (ae_of_all _ fun y => mul_nonneg (periodicWeight_nonneg _ _ _) (sq_nonneg _))
    ((tb_integrable hG).const_mul _) ?_
  filter_upwards [hae, ae_restrict_mem (B0579.measurableSet_cell _)] with y h1 h2
  simp only [h1]
  calc periodicWeight (-m) (cellLen (ν ^ (-2 : ℝ)) (clockA ν s)) y * ‖G y‖ ^ 2
      ≤ ((4 / Real.pi ^ 2) ^ (-m) * B0579.jb y ^ (-m)) * ‖G y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (tb_pw_le hm hd y h2) (sq_nonneg _)
    _ = (4 / Real.pi ^ 2) ^ (-m) * (B0579.jb y ^ (-m) * ‖G y‖ ^ 2) := by ring

end UnforcedLeray.Short.IIIa
