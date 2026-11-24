import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Equiv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3_5.WeakCellMeas
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_8

/-!
# `PartIII-a:T21/2/2/2/7`: the adjoint localized interaction in the weighted energy norm

Source: `the November 2 reference manuscript`, lines 3052-3058 and 3044.
From `AdjointLocalizedBound m` (the H^1 bound on `χ`) we get the weighted estimate
`∫ w |χ|² ≤ (π²/4)^m C² E_0(Φ)`, using
* measurability of `χ` on the cell from its weak cell derivative (`weakCellMeas`),
* `∫ jb^{-m} |f|² = (xNorm f)²` on the cell (`B0579.integral_cellMeasure`),
* the periodic weight comparison `jb^{-m} ≤ w ≤ (π²/4)^m jb^{-m}` (`adjWeightEquiv`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open UnforcedLeray.Short.IIIa
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.E0

theorem xNorm_le_h1 (c m : ℝ) (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) :
    xNorm c (-m) φ ≤ h1Norm c m φ g := by
  unfold h1Norm
  have hS : xNorm c (-m) φ ^ 2 ≤ xNorm c (-m) φ ^ 2 + ∑ j, xNorm c (-m) (g j) ^ 2 :=
    le_self_add
  calc xNorm c (-m) φ = (xNorm c (-m) φ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow hS (by norm_num)

theorem xNorm_toReal_sq (c m : ℝ) (f : ℝ × ℝ → ℂ) (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    (xNorm c m f).toReal ^ 2 = ∫ y in B0579.cell c, B0579.jb y ^ m * ‖f y‖ ^ 2 := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hnn : 0 ≤ (∫ a, ‖f a‖ ^ (2 : ℝ≥0∞).toReal ∂(B0579.cellMeasure c m)) ^
      ((2 : ℝ≥0∞).toReal)⁻¹ :=
    Real.rpow_nonneg (integral_nonneg fun a => by positivity) _
  unfold xNorm
  rw [h, ENNReal.toReal_ofReal hnn]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [B0579.integral_cellMeasure c m (fun x => ‖f x‖ ^ 2)]
  simp only [NNReal.smul_def, smul_eq_mul, B0579.coe_density]
  have hX : 0 ≤ ∫ x in B0579.cell c, B0579.jb x ^ m * ‖f x‖ ^ 2 :=
    integral_nonneg fun y => mul_nonneg (Real.rpow_nonneg (B0579.jb_pos y).le _) (sq_nonneg _)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]
  norm_num

theorem xNorm_integrableOn (c m : ℝ) (f : ℝ × ℝ → ℂ) (hf : MemLp f 2 (B0579.cellMeasure c m)) :
    IntegrableOn (fun y => B0579.jb y ^ m * ‖f y‖ ^ 2) (B0579.cell c) := by
  have hI : Integrable (fun x => ‖f x‖ ^ 2) (B0579.cellMeasure c m) :=
    hf.integrable_norm_pow two_ne_zero
  have h2 := (B0579.integrable_cellMeasure_iff c m).mp hI
  refine h2.congr_fun ?_ (B0579.measurableSet_cell c)
  intro y _
  simp only [NNReal.smul_def, smul_eq_mul, B0579.coe_density]

/-- The weighted integrability on the cell from the equivalent weight bounds. -/
theorem weight_integrableOn (m c : ℝ) (f : ℝ × ℝ → ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict (B0579.cell c)))
    (hup : ∀ y ∈ B0579.cell c,
      periodicWeight (-m) c y ≤ (Real.pi ^ 2 / 4) ^ m * B0579.jb y ^ (-m))
    (hJ : IntegrableOn (fun y => B0579.jb y ^ (-m) * ‖f y‖ ^ 2) (B0579.cell c)) :
    IntegrableOn (fun y => periodicWeight (-m) c y * ‖f y‖ ^ 2) (B0579.cell c) := by
  refine Integrable.mono' (hJ.const_mul ((Real.pi ^ 2 / 4) ^ m))
    ((UnforcedLeray.Short.IIIa.AdjE1.pw_contDiff (-m) c).continuous.aestronglyMeasurable.mul
      (hf.norm.pow 2)) (ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun y hy => ?_)
  show ‖periodicWeight (-m) c y * ‖f y‖ ^ 2‖ ≤
    (Real.pi ^ 2 / 4) ^ m * (B0579.jb y ^ (-m) * ‖f y‖ ^ 2)
  rw [Real.norm_of_nonneg (mul_nonneg (UnforcedLeray.Short.IIIa.AdjE1.pw_pos (-m) c y).le
    (sq_nonneg _))]
  calc periodicWeight (-m) c y * ‖f y‖ ^ 2
      ≤ ((Real.pi ^ 2 / 4) ^ m * B0579.jb y ^ (-m)) * ‖f y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hup y hy) (sq_nonneg _)
    _ = (Real.pi ^ 2 / 4) ^ m * (B0579.jb y ^ (-m) * ‖f y‖ ^ 2) := by ring

/-- **The adjoint localized interaction in the energy norm** (SP 3052-3058, 3044). -/
theorem adjChiWeighted (m : ℝ) (hm : 8 < m) (hL : AdjointLocalizedBound m) :
    UnforcedLeray.Short.IIIa.E0.AdjChiWeighted m := by
  obtain ⟨b₀, hb⟩ := hL
  refine ⟨b₀, fun b hbb => ?_⟩
  obtain ⟨C, ν₀, hν₀, hbound⟩ := hb b hbb
  refine ⟨(Real.pi ^ 2 / 4) ^ m * (max C 0) ^ 2, ν₀, by positivity, hν₀, ?_⟩
  intro ν hν tr hbuc r hr hbθ Φ hΦ
  obtain ⟨χ, gχ, hwk, hh1, hint⟩ := hbound ν hν tr hbuc r hr hbθ Φ hΦ
  set c := cellLen (ν ^ (-2 : ℝ)) (clockA ν r) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    unfold cellLen clockA
    exact div_pos (Real.rpow_pos_of_pos hν.1 _)
      (Real.sqrt_pos.mpr (by have := mul_nonneg hν.1.le hr; linarith))
  obtain ⟨hlow, hup⟩ := (adjWeightEquiv m hm) c hcpos
  have hmeasχ : AEStronglyMeasurable χ (volume.restrict (B0579.cell c)) :=
    UnforcedLeray.Short.IIIa.weakCellMeas c 0 χ (gχ 0) (hwk 0)
  have hμχ : AEStronglyMeasurable χ (B0579.cellMeasure c (-m)) :=
    hmeasχ.mono_ac (B0579.cellMeasure_ac c (-m))
  have hxle : xNorm c (-m) χ ≤ ENNReal.ofReal (max C 0) * xNorm c (-m) Φ :=
    calc xNorm c (-m) χ ≤ h1Norm c m χ gχ := xNorm_le_h1 c m χ gχ
      _ ≤ ENNReal.ofReal C * xNorm c (-m) Φ := hh1
      _ ≤ ENNReal.ofReal (max C 0) * xNorm c (-m) Φ :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left C 0)) zero_le
  have hΦlt : xNorm c (-m) Φ < ⊤ := hΦ.eLpNorm_lt_top
  have hχlt : xNorm c (-m) χ < ⊤ :=
    lt_of_le_of_lt hxle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hΦlt)
  have hχMem : MemLp χ 2 (B0579.cellMeasure c (-m)) := ⟨hμχ, hχlt⟩
  have hmeasΦ : AEStronglyMeasurable Φ (volume.restrict (B0579.cell c)) :=
    hΦ.aestronglyMeasurable.mono_ac (B0579.ac_cellMeasure c (-m))
  have hJχ := xNorm_integrableOn c (-m) χ hχMem
  have hJΦ := xNorm_integrableOn c (-m) Φ hΦ
  have hsqχ := xNorm_toReal_sq c (-m) χ hχMem
  have hsqΦ := xNorm_toReal_sq c (-m) Φ hΦ
  have hIw : IntegrableOn (fun y => periodicWeight (-m) c y * ‖χ y‖ ^ 2) (B0579.cell c) :=
    weight_integrableOn m c χ hmeasχ (fun y hy => hup y hy) hJχ
  have hIΦ : IntegrableOn (fun y => periodicWeight (-m) c y * ‖Φ y‖ ^ 2) (B0579.cell c) :=
    weight_integrableOn m c Φ hmeasΦ (fun y hy => hup y hy) hJΦ
  -- the weighted estimate of `χ`
  have hA : ∫ y in B0579.cell c, periodicWeight (-m) c y * ‖χ y‖ ^ 2 ≤
      ∫ y in B0579.cell c, (Real.pi ^ 2 / 4) ^ m * (B0579.jb y ^ (-m) * ‖χ y‖ ^ 2) :=
    setIntegral_mono_on hIw (hJχ.const_mul _) (B0579.measurableSet_cell c) fun y hy => by
      calc periodicWeight (-m) c y * ‖χ y‖ ^ 2
          ≤ ((Real.pi ^ 2 / 4) ^ m * B0579.jb y ^ (-m)) * ‖χ y‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hup y hy) (sq_nonneg _)
        _ = (Real.pi ^ 2 / 4) ^ m * (B0579.jb y ^ (-m) * ‖χ y‖ ^ 2) := by ring
  rw [integral_const_mul, ← hsqχ] at hA
  -- the norm comparison
  have hnormχ : (xNorm c (-m) χ).toReal ≤ max C 0 * (xNorm c (-m) Φ).toReal := by
    have := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΦlt.ne) hxle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_max_right C 0)] at this
  have hsq_le : (xNorm c (-m) χ).toReal ^ 2 ≤ (max C 0) ^ 2 * (xNorm c (-m) Φ).toReal ^ 2 := by
    calc (xNorm c (-m) χ).toReal ^ 2 ≤ (max C 0 * (xNorm c (-m) Φ).toReal) ^ 2 :=
          pow_le_pow_left₀ ENNReal.toReal_nonneg hnormχ 2
      _ = (max C 0) ^ 2 * (xNorm c (-m) Φ).toReal ^ 2 := by ring
  have hΦlow : (xNorm c (-m) Φ).toReal ^ 2 ≤ adjE0 c m Φ := by
    rw [hsqΦ]
    unfold adjE0
    exact setIntegral_mono_on hJΦ hIΦ (B0579.measurableSet_cell c) fun y _ =>
      mul_le_mul_of_nonneg_right (hlow y) (sq_nonneg _)
  have hfinal : ∫ y in B0579.cell c, periodicWeight (-m) c y * ‖χ y‖ ^ 2 ≤
      (Real.pi ^ 2 / 4) ^ m * (max C 0) ^ 2 * adjE0 c m Φ := by
    calc ∫ y in B0579.cell c, periodicWeight (-m) c y * ‖χ y‖ ^ 2
        ≤ (Real.pi ^ 2 / 4) ^ m * (xNorm c (-m) χ).toReal ^ 2 := by
          exact hA
      _ ≤ (Real.pi ^ 2 / 4) ^ m * ((max C 0) ^ 2 * (xNorm c (-m) Φ).toReal ^ 2) :=
          mul_le_mul_of_nonneg_left hsq_le (by positivity)
      _ ≤ (Real.pi ^ 2 / 4) ^ m * ((max C 0) ^ 2 * adjE0 c m Φ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΦlow (sq_nonneg _))
            (by positivity)
      _ = (Real.pi ^ 2 / 4) ^ m * (max C 0) ^ 2 * adjE0 c m Φ := by ring
  exact ⟨χ, hχMem, hmeasχ, hint, hIw, hfinal⟩

end UnforcedLeray.Short.IIIa.E0
