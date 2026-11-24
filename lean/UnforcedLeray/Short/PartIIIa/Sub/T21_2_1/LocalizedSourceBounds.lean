import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1

/-!
# Part III-a, `PartIII-a:T21/2/1/1`: `localizedSourceBounds`

Source of record: `the November 2 reference manuscript` (SP), lines 3050-3054:
the rescaled train bounds give `jb^{(m+2)/2} |∂E_mov| ≤ C` on the cell, hence
`|Φ ∂_jE_mov| ≤ C jb^{-m/2}|Φ| jb^{-1}`. Weighted Cauchy-Schwarz (Hölder with exponents 2, 2)
gives the `L¹` bound with `∫_{ℝ²} jb^{-2} < ∞`, and `jb^{-1} ≤ 1` gives the `L²` bound.
The constants are independent of the cell length.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

lemma enorm_ofReal_cx (r : ℝ) : ‖((r : ℝ) : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Complex.nnnorm_real]

/-- Complex version of `B0579.eLpNorm_cellMeasure`. -/
theorem eLpNorm_cellMeasure_cx (c m : ℝ) (f : ℝ × ℝ → ℂ) :
    eLpNorm f 2 (B0579.cellMeasure c m) =
      eLpNorm (fun x => ((B0579.jb x ^ (m / 2) : ℝ) : ℂ) * f x) 2
        (volume.restrict (B0579.cell c)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), B0579.cellMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (B0579.measurable_density m).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, enorm_mul, ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have h0 : 0 ≤ B0579.jb x ^ (m / 2) := Real.rpow_nonneg (B0579.jb_pos x).le _
  rw [enorm_ofReal_cx, mul_pow, Real.enorm_eq_ofReal h0, ← ENNReal.ofReal_pow h0,
    ← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos x).le]
  have : m / 2 * ((2 : ℕ) : ℝ) = m := by push_cast; ring
  rw [this]
  rfl

/-- For the sup norm on `ℝ × ℝ`, `1 + ‖x‖² ≤ jb x`. -/
lemma one_add_norm_sq_le_jb' (x : ℝ × ℝ) : 1 + ‖x‖ ^ 2 ≤ B0579.jb x := by
  have h1 : ‖x.1‖ ^ 2 = x.1 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖x.2‖ ^ 2 = x.2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have hn : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖x.1‖ ‖x.2‖ with h | h
    · rw [max_eq_right h, h2]
      nlinarith [sq_nonneg x.1]
    · rw [max_eq_left h, h1]
      nlinarith [sq_nonneg x.2]
  unfold B0579.jb
  linarith

/-- `∫_{ℝ²} jb^{-2} < ∞`. -/
theorem integrable_jb_rpow_neg_two' : Integrable (fun y : ℝ × ℝ => B0579.jb y ^ (-(2 : ℝ))) := by
  have hd : ((Module.finrank ℝ (ℝ × ℝ) : ℕ) : ℝ) = 2 := by simp
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ × ℝ) (μ := volume) (r := 2 * 2)
    (by rw [hd]; norm_num)
  have hexp : -((2 : ℝ) * 2) / 2 = -(2 : ℝ) := by norm_num
  rw [hexp] at h
  refine Integrable.mono' h (B0579.continuous_jb_rpow _).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (B0579.jb_pos y).le _)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (one_add_norm_sq_le_jb' y) (by norm_num)

/-- `|∂_j E| ≤ ‖∇E‖` for a real function `E` on the plane. -/
theorem abs_pd_le_norm_iteratedFDeriv_one (E : ℝ × ℝ → ℝ) (j : Fin 2) (y : ℝ × ℝ) :
    |B0579.pd j E y| ≤ ‖iteratedFDeriv ℝ 1 E y‖ := by
  rw [norm_iteratedFDeriv_one]
  have hdir : ‖B0579.dir j‖ ≤ 1 := by
    fin_cases j <;> simp [B0579.dir, Prod.norm_def]
  calc |B0579.pd j E y| = ‖fderiv ℝ E y (B0579.dir j)‖ := by
        rw [B0579.pd, Real.norm_eq_abs]
    _ ≤ ‖fderiv ℝ E y‖ * ‖B0579.dir j‖ := (fderiv ℝ E y).le_opNorm _
    _ ≤ ‖fderiv ℝ E y‖ * 1 := mul_le_mul_of_nonneg_left hdir (norm_nonneg _)
    _ = ‖fderiv ℝ E y‖ := mul_one _

/-- Pointwise bound: `|w ∂_jE| ≤ jb^{-m/2}|w| · (C jb^{-1})` from `jb^{(m+2)/2}|∇E| ≤ C`. -/
theorem norm_mul_pd_le {m C : ℝ} (hC : 0 ≤ C) {E : ℝ × ℝ → ℝ} (j : Fin 2) (y : ℝ × ℝ)
    (w : ℂ) (hE : B0579.jb y ^ ((m + 2) / 2) * ‖iteratedFDeriv ℝ 1 E y‖ ≤ C) :
    ‖w * ((B0579.pd j E y : ℝ) : ℂ)‖ ≤
      ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * w‖ * (C * B0579.jb y ^ (-1 : ℝ)) := by
  have hJ : 0 < B0579.jb y := B0579.jb_pos y
  have hpd := abs_pd_le_norm_iteratedFDeriv_one E j y
  have hA : B0579.jb y ^ ((m + 2) / 2) = B0579.jb y ^ (m / 2) * B0579.jb y := by
    rw [show (m + 2) / 2 = m / 2 + 1 by ring, Real.rpow_add hJ, Real.rpow_one]
  have hneg : B0579.jb y ^ ((-m) / 2) = (B0579.jb y ^ (m / 2))⁻¹ := by
    rw [show (-m) / 2 = -(m / 2) by ring, Real.rpow_neg hJ.le]
  have hm1 : B0579.jb y ^ (-1 : ℝ) = (B0579.jb y)⁻¹ := Real.rpow_neg_one _
  have ht0 : 0 < B0579.jb y ^ (m / 2) := Real.rpow_pos_of_pos hJ _
  have key : |B0579.pd j E y| * (B0579.jb y ^ (m / 2) * B0579.jb y) ≤ C := by
    rw [hA] at hE
    have h2 := mul_le_mul_of_nonneg_left hpd (le_of_lt (mul_pos ht0 hJ))
    nlinarith
  have hL : ‖w * ((B0579.pd j E y : ℝ) : ℂ)‖ = ‖w‖ * |B0579.pd j E y| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hR : ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * w‖ =
      (B0579.jb y ^ (m / 2))⁻¹ * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hneg,
      abs_of_pos (inv_pos.2 ht0)]
  rw [hL, hR, hm1]
  have hfin : (B0579.jb y ^ (m / 2))⁻¹ * ‖w‖ * (C * (B0579.jb y)⁻¹) =
      ‖w‖ * C / (B0579.jb y ^ (m / 2) * B0579.jb y) := by
    field_simp
  rw [hfin, le_div_iff₀ (mul_pos ht0 hJ)]
  calc ‖w‖ * |B0579.pd j E y| * (B0579.jb y ^ (m / 2) * B0579.jb y)
      = ‖w‖ * (|B0579.pd j E y| * (B0579.jb y ^ (m / 2) * B0579.jb y)) := by ring
    _ ≤ ‖w‖ * C := mul_le_mul_of_nonneg_left key (norm_nonneg _)

/-- **Localized source bounds** (SP 3050-3054). -/
theorem localizedSourceBounds (m : ℝ) (hm : 8 < m) (hT : RescaledTrainBounds m) :
    LocalizedSourceBounds m := by
  obtain ⟨b₀, hT⟩ := hT
  refine ⟨b₀, fun b hb => ?_⟩
  obtain ⟨C, ν₀, hν₀, hC⟩ := hT b hb
  have hC0 : 0 ≤ |C| := abs_nonneg C
  -- the weight `H = jb^{-1}` is in `L²(ℝ²)`
  have hHmem : MemLp (fun y : ℝ × ℝ => B0579.jb y ^ (-1 : ℝ)) 2 volume := by
    refine (memLp_two_iff_integrable_sq (B0579.continuous_jb_rpow (-1)).aestronglyMeasurable).2 ?_
    refine integrable_jb_rpow_neg_two'.congr (Filter.Eventually.of_forall fun y => ?_)
    show B0579.jb y ^ (-(2 : ℝ)) = (B0579.jb y ^ (-1 : ℝ)) ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos y).le]
    norm_num
  have hGmem : MemLp (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2 volume :=
    hHmem.const_mul |C|
  have hGfin : eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2 volume < ⊤ :=
    hGmem.2
  have hKnn : 0 ≤ (eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2 volume).toReal :=
    ENNReal.toReal_nonneg
  refine ⟨|C| + (eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2 volume).toReal + 1,
    ν₀, by linarith, hν₀, fun ν hν tr htr r hr hθ Φ hΦ j => ?_⟩
  obtain ⟨-, hB⟩ := hC ν hν tr htr r hr hθ
  set d := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hd
  have hE : ∀ y ∈ B0579.cell d, B0579.jb y ^ ((m + 2) / 2) *
      ‖iteratedFDeriv ℝ 1 (movingTrainE tr r) y‖ ≤ |C| :=
    fun y hy => le_trans (hB 1 (by norm_num) y hy) (le_abs_self C)
  -- the complex weighted field `A = jb^{-m/2} Φ` and its norm identity
  have hAmem : MemLp (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y) 2
      (volume.restrict (B0579.cell d)) := by
    have hcont : Continuous fun y : ℝ × ℝ => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow _)
    refine ⟨hcont.aestronglyMeasurable.mul (hΦ.1.mono_ac (B0579.ac_cellMeasure d (-m))), ?_⟩
    rw [← eLpNorm_cellMeasure_cx]
    exact hΦ.2
  have hAnorm : eLpNorm (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y) 2
      (volume.restrict (B0579.cell d)) = xNorm d (-m) Φ := by
    rw [← eLpNorm_cellMeasure_cx]
    rfl
  have hGr : MemLp (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2
      (volume.restrict (B0579.cell d)) := hGmem.restrict _
  -- pointwise domination of the localized source
  have hL1 : eLpNorm (fun y => Φ y * ((B0579.pd j (movingTrainE tr r) y : ℝ) : ℂ)) 1
      (volume.restrict (B0579.cell d)) ≤
      eLpNorm (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y *
        ((( |C| * B0579.jb y ^ (-1 : ℝ)) : ℝ) : ℂ)) 1 (volume.restrict (B0579.cell d)) := by
    refine eLpNorm_mono_ae (ae_restrict_of_forall_mem (B0579.measurableSet_cell d) fun y hy => ?_)
    have h := norm_mul_pd_le hC0 j y (Φ y) (hE y hy)
    rw [norm_mul (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)]
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC0
      (Real.rpow_nonneg (B0579.jb_pos y).le _))]
    exact h
  have hHold := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (f := fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)
    (g := fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ))
    (p := 2) (q := 2) (r := 1) hAmem.1 hGr.1
    (fun z t => z * ((t : ℝ) : ℂ)) 1
    (Eventually.of_forall fun y => by
simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC0
        (Real.rpow_nonneg (B0579.jb_pos y).le _)), NNReal.coe_one, one_mul, le_refl])
  have hHold' : eLpNorm (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y *
      ((( |C| * B0579.jb y ^ (-1 : ℝ)) : ℝ) : ℂ)) 1 (volume.restrict (B0579.cell d)) ≤
      eLpNorm (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y) 2
        (volume.restrict (B0579.cell d)) *
      eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2
        (volume.restrict (B0579.cell d)) := by
    simpa using hHold
  -- the pointwise bound in `L²`: `jb^{-1} ≤ 1`
  have hpt2 : ∀ y ∈ B0579.cell d,
      ‖Φ y * ((B0579.pd j (movingTrainE tr r) y : ℝ) : ℂ)‖ ≤
        ‖((|C| : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)‖ := by
    intro y hy
    have h := norm_mul_pd_le hC0 j y (Φ y) (hE y hy)
    have hJ1 : 1 ≤ B0579.jb y := by
      unfold B0579.jb; nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    have hH1 : B0579.jb y ^ (-1 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hJ1 (by norm_num)
    calc ‖Φ y * ((B0579.pd j (movingTrainE tr r) y : ℝ) : ℂ)‖
        ≤ ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y‖ * (|C| * B0579.jb y ^ (-1 : ℝ)) := h
      _ ≤ ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y‖ * (|C| * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH1 hC0) (norm_nonneg _)
      _ = ‖((|C| : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)‖ := by
          have hjpos : 0 ≤ B0579.jb y ^ ((-m) / 2) := Real.rpow_nonneg (B0579.jb_pos y).le _
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC0,
            abs_of_nonneg hjpos]
          ring
  -- the scalar bound for the `L¹` part: `eLpNorm` of the weight `G = |C| jb^{-1}` in `L²`
  have hLpt1 : ∀ y ∈ B0579.cell d,
      ‖Φ y * ((B0579.pd j (movingTrainE tr r) y : ℝ) : ℂ)‖ ≤
        ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y *
          ((( |C| * B0579.jb y ^ (-1 : ℝ)) : ℝ) : ℂ)‖ := by
    intro y hy
    have h := norm_mul_pd_le hC0 j y (Φ y) (hE y hy)
    rw [norm_mul (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y), Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (B0579.jb_pos y).le _))]
    exact h
  have hL1 : eLpNorm (fun y => Φ y * ((B0579.pd j (movingTrainE tr r) y : ℝ) : ℂ)) 1
      (volume.restrict (B0579.cell d)) ≤
      eLpNorm (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y *
        ((( |C| * B0579.jb y ^ (-1 : ℝ)) : ℝ) : ℂ)) 1 (volume.restrict (B0579.cell d)) :=
    eLpNorm_mono_ae (ae_restrict_of_forall_mem (B0579.measurableSet_cell d) hLpt1)
  -- measurability of the localized source
  have hpdm : Measurable (fun y : ℝ × ℝ => B0579.pd j (movingTrainE tr r) y) :=
    measurable_fderiv_apply_const ℝ (movingTrainE tr r) (B0579.dir j)
  have hsrcAE : AEStronglyMeasurable (fun y => Φ y * ((B0579.pd j (movingTrainE tr r) y : ℝ) : ℂ))
      (volume.restrict (B0579.cell d)) :=
    (hΦ.1.mono_ac (B0579.ac_cellMeasure d (-m))).mul
      (Complex.measurable_ofReal.comp hpdm).aestronglyMeasurable
  -- the constant
  have hGle : eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2
      (volume.restrict (B0579.cell d)) ≤
      ENNReal.ofReal (|C| + (eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2
        volume).toReal + 1) := by
    calc _ ≤ eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = ENNReal.ofReal (eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2 volume).toReal :=
          (ENNReal.ofReal_toReal hGfin.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  have hxN : xNorm d (-m) Φ < ⊤ := hΦ.2
  have hfin1 : eLpNorm (fun y => Φ y * ((B0579.pd j (movingTrainE tr r) y : ℝ) : ℂ)) 1
      (volume.restrict (B0579.cell d)) ≤
      ENNReal.ofReal (|C| + (eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2
        volume).toReal + 1) * xNorm d (-m) Φ := by
    calc _ ≤ _ := hL1
      _ ≤ _ := hHold'
      _ = eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2
            (volume.restrict (B0579.cell d)) * xNorm d (-m) Φ := by
          rw [hAnorm, mul_comm]
      _ ≤ _ := by gcongr
  have hfin2 : eLpNorm (fun y => Φ y * ((B0579.pd j (movingTrainE tr r) y : ℝ) : ℂ)) 2
      (volume.restrict (B0579.cell d)) ≤
      ENNReal.ofReal (|C| + (eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2
        volume).toReal + 1) * xNorm d (-m) Φ := by
    calc _ ≤ eLpNorm (fun y => ((|C| : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)) 2
          (volume.restrict (B0579.cell d)) :=
          eLpNorm_mono_ae (ae_restrict_of_forall_mem (B0579.measurableSet_cell d) hpt2)
      _ = ENNReal.ofReal |C| * xNorm d (-m) Φ := by
          have hsm := eLpNorm_const_smul (((|C| : ℝ) : ℂ))
            (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y) 2 (volume.restrict (B0579.cell d))
          rw [← hAnorm]
          rw [show (fun y => ((|C| : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)) =
            ((((|C| : ℝ) : ℂ)) • (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)) from rfl,
            eLpNorm_const_smul, enorm_ofReal_cx, Real.enorm_eq_ofReal hC0]
      _ ≤ _ := by gcongr; linarith
  refine ⟨?_, ?_, hfin1, hfin2⟩
  · refine memLp_one_iff_integrable.1 ⟨hsrcAE, ?_⟩
    exact lt_of_le_of_lt hfin1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hxN)
  · refine MemLp.of_le (g := fun y => ((|C| : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) *
      Φ y)) ?_ hsrcAE ?_
    · exact hAmem.const_mul _
    · exact ae_restrict_of_forall_mem (B0579.measurableSet_cell d) hpt2
end UnforcedLeray.Short.IIIa
