import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_8_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.LocalizedSourceBounds

/-!
# Part III-a, task `PartIII-a:T21/2/3/1/8/1/1`: the weighted field bound `AdjWFieldBound`

Source of record: `the November 2 reference manuscript` lines 3052-3058. The sources
`F_j = φ(ρ) ∂_j E(ρ)` of the adjoint localized interaction are bounded in `L¹ ∩ L²` of the cell by
`C' ‖φ(ρ)‖_{X_{-m}}`: the train bound `jb^{(m+2)/2}|∂_j E| ≤ C` (`LadTrainBdd`) gives
`|F_j| ≤ (jb^{-m/2}|φ|) (C jb^{-1})`, then Hölder with `jb^{-1} ∈ L²(ℝ²)` (`L¹`) and `jb^{-1} ≤ 1`
(`L²`). The constant is uniform in `ρ ∈ (t, s)` since `LadTrainBdd tr m s C` is uniform on `[0, s]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Pointwise bound: `|w ∂_jE| ≤ jb^{-m/2}|w| · (C jb^{-1})` from `jb^{(m+2)/2}|∂_jE| ≤ C`. -/
lemma pd_pointwise_bound {m C : ℝ} (hC : 0 ≤ C) (E : ℝ × ℝ → ℝ) (j : Fin 2) (y : ℝ × ℝ)
    (w : ℂ) (hE : B0579.jb y ^ ((m + 2) / 2) * |B0579.pd j E y| ≤ C) :
    ‖w * ((B0579.pd j E y : ℝ) : ℂ)‖ ≤
      ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * w‖ * (C * B0579.jb y ^ (-1 : ℝ)) := by
  have hJ : 0 < B0579.jb y := B0579.jb_pos y
  have ht0 : 0 < B0579.jb y ^ (m / 2) := Real.rpow_pos_of_pos hJ _
  have hA : B0579.jb y ^ ((m + 2) / 2) = B0579.jb y ^ (m / 2) * B0579.jb y := by
    rw [show (m + 2) / 2 = m / 2 + 1 by ring, Real.rpow_add hJ, Real.rpow_one]
  have hneg : B0579.jb y ^ ((-m) / 2) = (B0579.jb y ^ (m / 2))⁻¹ := by
    rw [show (-m) / 2 = -(m / 2) by ring, Real.rpow_neg hJ.le]
  have hm1 : B0579.jb y ^ (-1 : ℝ) = (B0579.jb y)⁻¹ := Real.rpow_neg_one _
  rw [hA] at hE
  have hkey : |B0579.pd j E y| ≤ C * (B0579.jb y ^ (m / 2) * B0579.jb y)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (mul_pos ht0 hJ)]
    linarith [mul_comm (B0579.jb y ^ (m / 2) * B0579.jb y) |B0579.pd j E y|]
  have hL : ‖w * ((B0579.pd j E y : ℝ) : ℂ)‖ = ‖w‖ * |B0579.pd j E y| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hR : ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * w‖ =
      (B0579.jb y ^ (m / 2))⁻¹ * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hneg,
      abs_of_pos (inv_pos.2 ht0)]
  rw [hL, hR, hm1]
  calc ‖w‖ * |B0579.pd j E y| ≤ ‖w‖ * (C * (B0579.jb y ^ (m / 2) * B0579.jb y)⁻¹) :=
        mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
    _ = (B0579.jb y ^ (m / 2))⁻¹ * ‖w‖ * (C * (B0579.jb y)⁻¹) := by
        rw [mul_inv]; ring

/-- Weighted Cauchy-Schwarz for one field: if `Φ` is in `X_{-m,c}` and `jb^{(m+2)/2}|∂_jE| ≤ C` on the
cell, then `Φ ∂_jE` is `L¹ ∩ L²` on the cell with both norms bounded by the uniform constant. -/
theorem weightedFieldBound (m C : ℝ) (hC0 : 0 ≤ C) (c : ℝ) (j : Fin 2) (Φ : ℝ × ℝ → ℂ)
    (E : ℝ × ℝ → ℝ) (hΦm : AEStronglyMeasurable Φ (volume.restrict (B0579.cell c)))
    (hΦx : xNorm c (-m) Φ < ⊤)
    (hE : ∀ y ∈ B0579.cell c, B0579.jb y ^ ((m + 2) / 2) * |B0579.pd j E y| ≤ C) :
    IntegrableOn (fun y => Φ y * ((B0579.pd j E y : ℝ) : ℂ)) (B0579.cell c) ∧
      MemLp (fun y => Φ y * ((B0579.pd j E y : ℝ) : ℂ)) 2 (volume.restrict (B0579.cell c)) ∧
      eLpNorm (fun y => Φ y * ((B0579.pd j E y : ℝ) : ℂ)) 1 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun y => Φ y * ((B0579.pd j E y : ℝ) : ℂ)) 2 (volume.restrict (B0579.cell c)) ≤
        ENNReal.ofReal (2 * (C + (eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2
          volume).toReal + 1)) * xNorm c (-m) Φ := by
  -- the weight `H = C jb^{-1}` is in `L²(ℝ²)`
  have hHmem : MemLp (fun y : ℝ × ℝ => B0579.jb y ^ (-1 : ℝ)) 2 volume := by
    refine (memLp_two_iff_integrable_sq (B0579.continuous_jb_rpow (-1)).aestronglyMeasurable).2 ?_
    refine integrable_jb_rpow_neg_two'.congr (Filter.Eventually.of_forall fun y => ?_)
    show B0579.jb y ^ (-(2 : ℝ)) = (B0579.jb y ^ (-1 : ℝ)) ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul (B0579.jb_pos y).le]
    norm_num
  have hGmem : MemLp (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2 volume :=
    hHmem.const_mul C
  have hGfin : eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2 volume < ⊤ := hGmem.2
  have hKnn : 0 ≤ (eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2 volume).toReal :=
    ENNReal.toReal_nonneg
  set K : ℝ := C + (eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2 volume).toReal + 1
    with hK
  have hK0 : 0 ≤ K := by linarith
  have hGr : MemLp (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2
      (volume.restrict (B0579.cell c)) := hGmem.restrict _
  have hpdm : Measurable (fun y : ℝ × ℝ => B0579.pd j E y) :=
    measurable_fderiv_apply_const ℝ E (B0579.dir j)
  have hsrcAE : AEStronglyMeasurable (fun y => Φ y * ((B0579.pd j E y : ℝ) : ℂ))
      (volume.restrict (B0579.cell c)) :=
    hΦm.mul (Complex.measurable_ofReal.comp hpdm).aestronglyMeasurable
  -- the weighted field `A = jb^{-m/2} Φ`
  have hAmem : MemLp (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y) 2
      (volume.restrict (B0579.cell c)) := by
    have hcont : Continuous fun y : ℝ × ℝ => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (B0579.continuous_jb_rpow _)
    refine ⟨hcont.aestronglyMeasurable.mul hΦm, ?_⟩
    rw [← eLpNorm_cellMeasure_cx]
    exact hΦx
  have hAnorm : eLpNorm (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y) 2
      (volume.restrict (B0579.cell c)) = xNorm c (-m) Φ := by
    rw [← eLpNorm_cellMeasure_cx]
    rfl
  -- pointwise domination, `L¹` part
  have hLpt1 : ∀ y ∈ B0579.cell c,
      ‖Φ y * ((B0579.pd j E y : ℝ) : ℂ)‖ ≤
        ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y *
          (((C * B0579.jb y ^ (-1 : ℝ)) : ℝ) : ℂ)‖ := by
    intro y hy
    have h := pd_pointwise_bound hC0 E j y (Φ y) (hE y hy)
    rw [norm_mul (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y), Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (B0579.jb_pos y).le _))]
    exact h
  have hL1 : eLpNorm (fun y => Φ y * ((B0579.pd j E y : ℝ) : ℂ)) 1
      (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y *
        (((C * B0579.jb y ^ (-1 : ℝ)) : ℝ) : ℂ)) 1 (volume.restrict (B0579.cell c)) :=
    eLpNorm_mono_ae (ae_restrict_of_forall_mem (B0579.measurableSet_cell c) hLpt1)
  have hHold := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
    (f := fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)
    (g := fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ))
    (p := 2) (q := 2) (r := 1) hAmem.1 hGr.1
    (fun z t => z * ((t : ℝ) : ℂ)) 1
    (Eventually.of_forall fun y => by
      simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hC0
        (Real.rpow_nonneg (B0579.jb_pos y).le _)), NNReal.coe_one, one_mul, le_refl])
  have hHold' : eLpNorm (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y *
      (((C * B0579.jb y ^ (-1 : ℝ)) : ℝ) : ℂ)) 1 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y) 2
        (volume.restrict (B0579.cell c)) *
      eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2
        (volume.restrict (B0579.cell c)) := by
    simpa using hHold
  have hGle : eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2
      (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal K := by
    calc _ ≤ eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = ENNReal.ofReal (eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2
            volume).toReal := (ENNReal.ofReal_toReal hGfin.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [hK])
  have hfin1 : eLpNorm (fun y => Φ y * ((B0579.pd j E y : ℝ) : ℂ)) 1
      (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal K * xNorm c (-m) Φ := by
    calc _ ≤ _ := hL1
      _ ≤ _ := hHold'
      _ = eLpNorm (fun y : ℝ × ℝ => C * B0579.jb y ^ (-1 : ℝ)) 2
            (volume.restrict (B0579.cell c)) * xNorm c (-m) Φ := by
          rw [hAnorm, mul_comm]
      _ ≤ _ := by gcongr
  -- pointwise domination, `L²` part: `jb^{-1} ≤ 1`
  have hpt2 : ∀ y ∈ B0579.cell c,
      ‖Φ y * ((B0579.pd j E y : ℝ) : ℂ)‖ ≤
        ‖((C : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)‖ := by
    intro y hy
    have h := pd_pointwise_bound hC0 E j y (Φ y) (hE y hy)
    have hJ1 : 1 ≤ B0579.jb y := by
      unfold B0579.jb; nlinarith [sq_nonneg y.1, sq_nonneg y.2]
    have hH1 : B0579.jb y ^ (-1 : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hJ1 (by norm_num)
    calc ‖Φ y * ((B0579.pd j E y : ℝ) : ℂ)‖
        ≤ ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y‖ * (C * B0579.jb y ^ (-1 : ℝ)) := h
      _ ≤ ‖((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y‖ * (C * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH1 hC0) (norm_nonneg _)
      _ = ‖((C : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)‖ := by
          have hjpos : 0 ≤ B0579.jb y ^ ((-m) / 2) := Real.rpow_nonneg (B0579.jb_pos y).le _
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC0,
            abs_of_nonneg hjpos]
          ring
  have hfin2 : eLpNorm (fun y => Φ y * ((B0579.pd j E y : ℝ) : ℂ)) 2
      (volume.restrict (B0579.cell c)) ≤ ENNReal.ofReal K * xNorm c (-m) Φ := by
    calc _ ≤ eLpNorm (fun y => ((C : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)) 2
          (volume.restrict (B0579.cell c)) :=
          eLpNorm_mono_ae (ae_restrict_of_forall_mem (B0579.measurableSet_cell c) hpt2)
      _ = ENNReal.ofReal C * xNorm c (-m) Φ := by
          rw [← hAnorm]
          rw [show (fun y => ((C : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)) =
            ((((C : ℝ) : ℂ)) • (fun y => ((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) * Φ y)) from rfl,
            eLpNorm_const_smul, enorm_ofReal_cx, Real.enorm_eq_ofReal hC0]
      _ ≤ _ := by gcongr; linarith [hK]
  refine ⟨?_, ?_, ?_⟩
  · exact memLp_one_iff_integrable.1
      ⟨hsrcAE, lt_of_le_of_lt hfin1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΦx)⟩
  · refine MemLp.of_le (g := fun y => ((C : ℝ) : ℂ) * (((B0579.jb y ^ ((-m) / 2) : ℝ) : ℂ) *
      Φ y)) ?_ hsrcAE ?_
    · exact hAmem.const_mul _
    · exact ae_restrict_of_forall_mem (B0579.measurableSet_cell c) hpt2
  · calc _ ≤ ENNReal.ofReal K * xNorm c (-m) Φ + ENNReal.ofReal K * xNorm c (-m) Φ :=
          add_le_add hfin1 hfin2
      _ = ENNReal.ofReal (2 * K) * xNorm c (-m) Φ := by
          rw [← add_mul, ← ENNReal.ofReal_add hK0 hK0, two_mul]

/-- **Leaf `.../1`** (SP 3052-3058, weighted Cauchy-Schwarz): for a jointly smooth weak solution the
sources `F_j = φ(ρ) ∂_jE(ρ)` are in `L¹ ∩ L²` of the cell with
`‖F_j‖_{L¹} + ‖F_j‖_{L²} ≤ C' ‖φ(ρ)‖_{X_{-m}}`, `C'` uniform in `ρ ∈ (t, s)`. -/
theorem adjWFieldBound (m : ℝ) : UnforcedLeray.Short.IIIa.AdjWFieldBound m := by
  intro hm ν c tr t s g φ hc hctx
  have hts0 : 0 ≤ s := by linarith [hctx.2.2.1, hctx.2.2.2.1]
  obtain ⟨C, hC⟩ := hctx.2.2.2.2.1 s hts0
  refine ⟨2 * (|C| + (eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ)) 2 volume).toReal
    + 1), ?_, fun ρ hρ j => ?_⟩
  · have := ENNReal.toReal_nonneg (a := eLpNorm (fun y : ℝ × ℝ => |C| * B0579.jb y ^ (-1 : ℝ))
      2 volume)
    nlinarith [abs_nonneg C]
  have hρI : ρ ∈ Icc (0 : ℝ) s := ⟨le_trans hctx.2.2.1 hρ.1.le, hρ.2.le⟩
  have hΦ := hctx.2.2.2.2.2.1.memX ρ (Ioo_subset_Icc_self hρ)
  have hbd : ∀ y ∈ B0579.cell c,
      B0579.jb y ^ ((m + 2) / 2) * |B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) y| ≤ |C| :=
    fun y hy => le_trans ((hC ρ hρI y hy).2 j) (le_abs_self C)
  exact weightedFieldBound m |C| (abs_nonneg C) c j (φ ρ) (UnforcedLeray.B0238.Ec tr ρ)
    (hΦ.1.mono_ac (B0579.ac_cellMeasure c (-m))) hΦ.2 hbd

end UnforcedLeray.Short.IIIa
