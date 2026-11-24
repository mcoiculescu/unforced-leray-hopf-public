import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3

/-!
# Part III-a, `PartIII-a:T21/2/3/4`: the `H¹_{-m,d}` norm by the periodic-weight energies (SP 3044)

For `m ≥ 0` the periodic weight `p_d = periodicWeight (-m) d` satisfies
`⟨y⟩^{-2m} ≤ p_d` everywhere (from `|sin u| ≤ |u|`) and `p_d ≤ (4/π²)^{-m} ⟨y⟩^{-2m}` on the
centered cell (from `sin u ≥ 2u` on `|u| ≤ 1/2`). Hence the weighted `L²` norms of `Φ` and `∇Φ`
are bounded by the energies `E_0`, `E_1`, with constant `C = 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `(d/π)² sin²(π y₁/d) ≥ (4/π²) y₁²` on the centered cell `|y₁| ≤ d/2`. -/
lemma h1s_sin_sq_lower (d : ℝ) (hd : 0 < d) (y : ℝ × ℝ) (hy : y ∈ B0579.cell d) :
    4 / Real.pi ^ 2 * y.1 ^ 2 ≤ (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by
  have hy1 : -(d / 2) ≤ y.1 ∧ y.1 < d / 2 := hy.1
  have hpi : 0 < Real.pi := Real.pi_pos
  have habs : |y.1| ≤ d / 2 := abs_le.mpr ⟨hy1.1, hy1.2.le⟩
  have hz0 : 0 ≤ Real.pi * |y.1| / d := by positivity
  have hz1 : Real.pi * |y.1| / d ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hd]
    nlinarith
  have hsin : 2 / Real.pi * (Real.pi * |y.1| / d) ≤ Real.sin (Real.pi * |y.1| / d) :=
    Real.mul_le_sin hz0 hz1
  have hlhs : 2 / Real.pi * (Real.pi * |y.1| / d) = 2 * |y.1| / d := by
    field_simp
  have hsq : Real.sin (Real.pi * y.1 / d) ^ 2 = Real.sin (Real.pi * |y.1| / d) ^ 2 := by
    rcases abs_cases y.1 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, show Real.pi * -y.1 / d = -(Real.pi * y.1 / d) by ring, Real.sin_neg]
      ring
  have hmul : (2 / Real.pi * (Real.pi * |y.1| / d)) ^ 2 ≤ Real.sin (Real.pi * |y.1| / d) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by positivity) hz0) hsin 2
  rw [hlhs] at hmul
  have h2 : (d / Real.pi) ^ 2 * (2 * |y.1| / d) ^ 2 ≤
      (d / Real.pi) ^ 2 * Real.sin (Real.pi * |y.1| / d) ^ 2 :=
    mul_le_mul_of_nonneg_left hmul (by positivity)
  have e : (d / Real.pi) ^ 2 * (2 * |y.1| / d) ^ 2 = 4 / Real.pi ^ 2 * y.1 ^ 2 := by
    rw [← sq_abs y.1]
    field_simp
    ring
  rw [hsq]
  linarith

/-- `(d/π)² sin²(π y₁/d) ≤ y₁²` everywhere. -/
lemma h1s_sin_sq_upper (d : ℝ) (hd : 0 < d) (y : ℝ × ℝ) :
    (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 ≤ y.1 ^ 2 := by
  have h := Real.abs_sin_le_abs (x := Real.pi * y.1 / d)
  have h2 : Real.sin (Real.pi * y.1 / d) ^ 2 ≤ (Real.pi * y.1 / d) ^ 2 := sq_le_sq.mpr h
  have e : (d / Real.pi) ^ 2 * (Real.pi * y.1 / d) ^ 2 = y.1 ^ 2 := by
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    have : d ≠ 0 := hd.ne'
    field_simp
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (d / Real.pi) ^ 2)
  linarith

/-- The lower weight bound `⟨y⟩^{-2m} ≤ p_d` (SP 3044), valid everywhere for `m ≥ 0`. -/
lemma h1s_pw_lower (m d : ℝ) (hm : 0 ≤ m) (hd : 0 < d) (y : ℝ × ℝ) :
    B0579.jb y ^ (-m) ≤ periodicWeight (-m) d y := by
  unfold periodicWeight
  have hQpos : 0 < 1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by
    positivity
  have hQ : 1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 ≤
      B0579.jb y := by
    have := h1s_sin_sq_upper d hd y
    unfold B0579.jb
    linarith
  exact Real.rpow_le_rpow_of_nonpos hQpos hQ (by linarith)

/-- The upper weight bound `p_d ≤ (4/π²)^{-m} ⟨y⟩^{-2m}` on the centered cell (SP 3044). -/
lemma h1s_pw_upper (m d : ℝ) (hm : 0 ≤ m) (hd : 0 < d) (y : ℝ × ℝ) (hy : y ∈ B0579.cell d) :
    periodicWeight (-m) d y ≤ (4 / Real.pi ^ 2) ^ (-m) * B0579.jb y ^ (-m) := by
  unfold periodicWeight
  have hK : 0 < 4 / Real.pi ^ 2 := by positivity
  have hjb : 0 < B0579.jb y := B0579.jb_pos y
  have hpi4 : 4 / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hlow := h1s_sin_sq_lower d hd y hy
  have h2 : 4 / Real.pi ^ 2 * y.2 ^ 2 ≤ y.2 ^ 2 := mul_le_of_le_one_left (sq_nonneg _) hpi4
  have hQ : 4 / Real.pi ^ 2 * B0579.jb y ≤
      1 + y.2 ^ 2 + (d / Real.pi) ^ 2 * Real.sin (Real.pi * y.1 / d) ^ 2 := by
    unfold B0579.jb
    have e : 4 / Real.pi ^ 2 * (1 + y.1 ^ 2 + y.2 ^ 2) =
        4 / Real.pi ^ 2 + 4 / Real.pi ^ 2 * y.1 ^ 2 + 4 / Real.pi ^ 2 * y.2 ^ 2 := by ring
    rw [e]
    linarith
  have hmono := Real.rpow_le_rpow_of_nonpos (mul_pos hK hjb) hQ (by linarith : -m ≤ 0)
  rw [Real.mul_rpow hK.le hjb.le] at hmono
  exact hmono

/-- `(∫⁻ ‖f‖ₑ²)` is the square of the `L²` norm. -/
lemma h1s_eLpNorm_sq (f : ℝ × ℝ → ℂ) (μ : Measure (ℝ × ℝ)) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.rpow_two]
  norm_num

/-- The bridge: the weighted `L²` norm squared is bounded by the periodic-weight energy. -/
lemma h1s_bridge (m d : ℝ) (hm : 0 ≤ m) (hd : 0 < d) (f : ℝ × ℝ → ℂ)
    (hf : MemLp f 2 (B0579.cellMeasure d (-m))) :
    eLpNorm f 2 (B0579.cellMeasure d (-m)) ^ 2 ≤
      ENNReal.ofReal (∫ y in B0579.cell d, periodicWeight (-m) d y * ‖f y‖ ^ 2) := by
  have hfm : AEStronglyMeasurable f (volume.restrict (B0579.cell d)) :=
    hf.1.mono_ac (B0579.ac_cellMeasure d (-m))
  have hfm2 : AEStronglyMeasurable (fun x => ‖f x‖ ^ 2) (volume.restrict (B0579.cell d)) :=
    (hfm.norm).pow 2
  -- weighted integrability: `⟨x⟩^{-2m} |f|²` is integrable on the cell
  have hint_w : Integrable (fun x => B0579.jb x ^ (-m) * ‖f x‖ ^ 2)
      (volume.restrict (B0579.cell d)) := by
    have h1 := hf.integrable_norm_rpow (by norm_num) ENNReal.ofNat_ne_top
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1
    have h2 := (integrable_withDensity_iff_integrable_smul (B0579.measurable_density (-m))).1 h1
    simpa [NNReal.smul_def, B0579.coe_density] using h2
  have hpcont : Continuous (periodicWeight (-m) d) := by
    unfold periodicWeight
    apply Continuous.rpow_const (by fun_prop)
    intro x
    left
    positivity
  have hint : Integrable (fun x => periodicWeight (-m) d x * ‖f x‖ ^ 2)
      (volume.restrict (B0579.cell d)) := by
    refine Integrable.mono' (hint_w.const_mul ((4 / Real.pi ^ 2) ^ (-m)))
      (hpcont.aestronglyMeasurable.mul hfm2) ?_
    refine (ae_restrict_mem (B0579.measurableSet_cell d)).mono fun x hx => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (periodicWeight_nonneg _ _ _) (sq_nonneg _))]
    calc periodicWeight (-m) d x * ‖f x‖ ^ 2
        ≤ ((4 / Real.pi ^ 2) ^ (-m) * B0579.jb x ^ (-m)) * ‖f x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (h1s_pw_upper m d hm hd x hx) (sq_nonneg _)
      _ = (4 / Real.pi ^ 2) ^ (-m) * (B0579.jb x ^ (-m) * ‖f x‖ ^ 2) := by ring
  have hρ : AEMeasurable (fun x => (B0579.density (-m) x : ℝ≥0∞))
      (volume.restrict (B0579.cell d)) :=
    (B0579.measurable_density (-m)).coe_nnreal_ennreal.aemeasurable
  have hg : AEMeasurable (fun x => ‖f x‖ₑ ^ 2) (volume.restrict (B0579.cell d)) :=
    (hfm.aemeasurable.enorm).pow_const 2
  rw [h1s_eLpNorm_sq f (B0579.cellMeasure d (-m)), B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul₀ hρ hg,
    ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => mul_nonneg (periodicWeight_nonneg _ _ _) (sq_nonneg _))]
  apply lintegral_mono
  intro x
  simp only [Pi.mul_apply]
  have hle : (B0579.density (-m) x : ℝ≥0∞) ≤ ENNReal.ofReal (periodicWeight (-m) d x) :=
    ENNReal.ofReal_le_ofReal (h1s_pw_lower m d hm hd x)
  have hn : ENNReal.ofReal ‖f x‖ = ‖f x‖ₑ := by simp
  rw [ENNReal.ofReal_mul (periodicWeight_nonneg _ _ _), ENNReal.ofReal_pow (norm_nonneg _), hn]
  gcongr

/-- **The `H¹_{-m,d}` norm by the periodic-weight energies** (SP 3044), with `C = 1`. -/
theorem h1BySeminorm (m : ℝ) : H1BySeminorm m := by
  intro hm
  refine ⟨1, zero_le_one, ?_⟩
  intro d hd Φ hΦ hdΦ
  have hE0nn : 0 ≤ adjE0 d m Φ :=
    integral_nonneg fun y => mul_nonneg (periodicWeight_nonneg _ _ _) (sq_nonneg _)
  have hEjnn : ∀ j : Fin 2, 0 ≤ ∫ y in B0579.cell d, periodicWeight (-m) d y * ‖pdCx j Φ y‖ ^ 2 :=
    fun j => integral_nonneg fun y => mul_nonneg (periodicWeight_nonneg _ _ _) (sq_nonneg _)
  have hE1nn : 0 ≤ adjE1 d m Φ := by
    unfold adjE1
    exact Finset.sum_nonneg fun k _ => hEjnn k
  have hX0 : eLpNorm Φ 2 (B0579.cellMeasure d (-m)) ^ 2 ≤ ENNReal.ofReal (adjE0 d m Φ) :=
    h1s_bridge m d hm hd Φ hΦ
  have hsum : ∑ j : Fin 2, eLpNorm (pdCx j Φ) 2 (B0579.cellMeasure d (-m)) ^ 2 ≤
      ENNReal.ofReal (adjE1 d m Φ) := by
    unfold adjE1
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hEjnn k)]
    exact Finset.sum_le_sum fun j _ => h1s_bridge m d hm hd _ (hdΦ j)
  have htot : eLpNorm Φ 2 (B0579.cellMeasure d (-m)) ^ 2 +
      ∑ j : Fin 2, eLpNorm (pdCx j Φ) 2 (B0579.cellMeasure d (-m)) ^ 2 ≤
      ENNReal.ofReal (adjE0 d m Φ + adjE1 d m Φ) := by
    rw [ENNReal.ofReal_add hE0nn hE1nn]
    exact add_le_add hX0 hsum
  unfold h1Norm xNorm
  calc _ ≤ (ENNReal.ofReal (adjE0 d m Φ + adjE1 d m Φ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow htot (by norm_num)
    _ = ENNReal.ofReal ((adjE0 d m Φ + adjE1 d m Φ) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (x := adjE0 d m Φ + adjE1 d m Φ) (p := 1 / 2)
          (by linarith) (by norm_num)
    _ = ENNReal.ofReal (1 * Real.sqrt (adjE0 d m Φ + adjE1 d m Φ)) := by
        rw [one_mul, Real.sqrt_eq_rpow]

end UnforcedLeray.Short.IIIa
