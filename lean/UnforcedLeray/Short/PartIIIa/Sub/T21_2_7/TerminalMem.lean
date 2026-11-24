import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

/-!
# Part III-a, `PartIII-a:T21/2/7/1/3`: the physical terminal datum lies in `X_{-m,c}`

Source: `the November 2 reference manuscript` lines 3036-3037, 3060
(`g = a G(·/√a)`, `a ≥ 1`; change of variables `x = √a y`, and `⟨x⟩ ≥ ⟨x/√a⟩`, `m ≥ 0`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

namespace TerminalMem

/-- Scaling of the cell measure: `vol|cell c = k² · (k • ·)_* vol|cell d` for `d k = c`. -/
theorem restrict_cell_eq {k d c : ℝ} (hk : 0 < k) (hd : d * k = c) :
    volume.restrict (B0579.cell c) =
      ENNReal.ofReal (k ^ 2) •
        Measure.map (fun y : ℝ × ℝ => k • y) (volume.restrict (B0579.cell d)) := by
  have hmeas : Measurable (fun y : ℝ × ℝ => k • y) := measurable_const_smul k
  ext A hA
  rw [Measure.smul_apply, Measure.map_apply hmeas hA, Measure.restrict_apply hA,
    Measure.restrict_apply (hmeas hA)]
  have hset : (fun y : ℝ × ℝ => k • y) ⁻¹' A ∩ B0579.cell d =
      (fun y : ℝ × ℝ => k • y) ⁻¹' (A ∩ B0579.cell c) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true,
        Prod.smul_fst, smul_eq_mul] at h2 ⊢
      rw [← hd]
      constructor <;> nlinarith [h2.1, h2.2]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      simp only [B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true,
        Prod.smul_fst, smul_eq_mul] at h2 ⊢
      rw [← hd] at h2
      constructor <;> nlinarith [h2.1, h2.2]
  rw [hset, Measure.addHaar_preimage_smul volume hk.ne']
  simp only [Module.finrank_prod, Module.finrank_self, smul_eq_mul]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have : k ^ 2 * |(k ^ (1 + 1))⁻¹| = 1 := by
    rw [abs_of_nonneg (by positivity)]
    field_simp
  rw [this]
  simp

theorem jb_smul_inv_le {k : ℝ} (hk : 1 ≤ k) (x : ℝ × ℝ) :
    B0579.jb ((k⁻¹) • x) ≤ B0579.jb x := by
  have h0 : (0 : ℝ) ≤ k⁻¹ := inv_nonneg.2 (by linarith)
  have h1 : (k⁻¹) ^ 2 ≤ 1 := pow_le_one₀ h0 (inv_le_one_of_one_le₀ hk)
  unfold B0579.jb
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_pow]
  nlinarith [sq_nonneg x.1, sq_nonneg x.2, mul_le_mul_of_nonneg_right h1 (sq_nonneg x.1),
    mul_le_mul_of_nonneg_right h1 (sq_nonneg x.2)]

theorem density_le {k m : ℝ} (hk : 1 ≤ k) (hm : 0 ≤ m) (x : ℝ × ℝ) :
    (B0579.density (-m) x : ℝ≥0∞) ≤ B0579.density (-m) ((k⁻¹) • x) := by
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, B0579.coe_density, B0579.coe_density]
  exact Real.rpow_le_rpow_of_nonpos (B0579.jb_pos _) (jb_smul_inv_le hk x) (by linarith)

theorem terminal_mem (m : ℝ) (hm : 0 ≤ m) : AdjTerminalMem m := by
  intro c a hc ha G hG
  have ha0 : 0 < a := by linarith
  have hk1 : 1 ≤ Real.sqrt a := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ha
  set k := Real.sqrt a with hkdef
  have hk0 : 0 < k := by linarith
  have hka : k ^ 2 = a := Real.sq_sqrt ha0.le
  have hdk : cellLen c a * k = c := by
    unfold cellLen; rw [← hkdef]; field_simp
  set d := cellLen c a with hd
  have hR := restrict_cell_eq hk0 hdk
  have hemb : MeasurableEmbedding (fun y : ℝ × ℝ => k • y) := measurableEmbedding_const_smul₀ hk0.ne'
  have hphys : physAdj a G = fun x : ℝ × ℝ => ((a : ℝ) : ℂ) * G (k⁻¹ • x) := by
    funext x
    unfold physAdj
    rw [← hkdef]
    congr 2
    ext <;> simp [div_eq_inv_mul]
  rw [hphys]
  -- measurability
  have hGm : AEStronglyMeasurable G (volume.restrict (B0579.cell d)) :=
    hG.1.mono_ac (B0579.ac_cellMeasure d (-m))
  have hGk : AEStronglyMeasurable (fun x : ℝ × ℝ => G (k⁻¹ • x))
      (Measure.map (fun y : ℝ × ℝ => k • y) (volume.restrict (B0579.cell d))) := by
    rw [hemb.aestronglyMeasurable_map_iff]
    have : ((fun x : ℝ × ℝ => G (k⁻¹ • x)) ∘ fun y : ℝ × ℝ => k • y) = G := by
      funext y; simp [inv_smul_smul₀ hk0.ne']
    rw [this]; exact hGm
  have hGk2 : AEStronglyMeasurable (fun x : ℝ × ℝ => G (k⁻¹ • x))
      (B0579.cellMeasure c (-m)) := by
    refine AEStronglyMeasurable.mono_ac (B0579.cellMeasure_ac c (-m)) ?_
    rw [hR]
    exact hGk.smul_measure _
  refine ⟨hGk2.const_mul _, ?_⟩
  -- finiteness
  have hG2 := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)).1 hG.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hG2 ⊢
  have hmd := (B0579.measurable_density (-m)).coe_nnreal_ennreal
  have hfin : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (B0579.density (-m) x : ℝ≥0∞) < ⊤ := Eventually.of_forall fun _ => ENNReal.coe_lt_top
  have hfin' : ∀ᵐ x ∂(volume.restrict (B0579.cell d)),
      (B0579.density (-m) x : ℝ≥0∞) < ⊤ := Eventually.of_forall fun _ => ENNReal.coe_lt_top
  unfold B0579.cellMeasure at hG2 ⊢
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmd hfin] at ⊢
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hmd hfin'] at hG2
  have hpt : ∀ x : ℝ × ℝ,
      ((fun x => (B0579.density (-m) x : ℝ≥0∞)) * fun x => ‖((a : ℝ) : ℂ) * G (k⁻¹ • x)‖ₑ ^ 2) x ≤
        ENNReal.ofReal (a ^ 2) *
          ((fun y : ℝ × ℝ => ((fun y => (B0579.density (-m) y : ℝ≥0∞)) *
            fun y => ‖G y‖ₑ ^ 2) y) (k⁻¹ • x)) := by
    intro x
    simp only [Pi.mul_apply, enorm_mul, mul_pow]
    have he : ‖((a : ℝ) : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ha0.le,
        ← ENNReal.ofReal_pow ha0.le]
    rw [he]
    calc (B0579.density (-m) x : ℝ≥0∞) * (ENNReal.ofReal (a ^ 2) * ‖G (k⁻¹ • x)‖ₑ ^ 2)
        = ENNReal.ofReal (a ^ 2) * ((B0579.density (-m) x : ℝ≥0∞) * ‖G (k⁻¹ • x)‖ₑ ^ 2) := by
          ring
      _ ≤ _ := by
          gcongr
          exact ENNReal.coe_le_coe.1 (density_le hk1 hm x)
  calc ∫⁻ x, ((fun x => (B0579.density (-m) x : ℝ≥0∞)) *
        fun x => ‖((a : ℝ) : ℂ) * G (k⁻¹ • x)‖ₑ ^ 2) x ∂(volume.restrict (B0579.cell c))
      ≤ ∫⁻ x, ENNReal.ofReal (a ^ 2) *
          ((fun y : ℝ × ℝ => ((fun y => (B0579.density (-m) y : ℝ≥0∞)) *
            fun y => ‖G y‖ₑ ^ 2) y) (k⁻¹ • x)) ∂(volume.restrict (B0579.cell c)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (k ^ 2) * (ENNReal.ofReal (a ^ 2) *
          ∫⁻ y, ((fun y => (B0579.density (-m) y : ℝ≥0∞)) *
            fun y => ‖G y‖ₑ ^ 2) y ∂(volume.restrict (B0579.cell d))) := by
        rw [hR, lintegral_smul_measure, hemb.lintegral_map]
        congr 1
        have : ∀ y : ℝ × ℝ, k⁻¹ • (k • y) = y := fun y => inv_smul_smul₀ hk0.ne' y
        simp only [this]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hG2)

end TerminalMem

theorem adjTerminalMem (m : ℝ) (hm : 0 ≤ m) : AdjTerminalMem m := TerminalMem.terminal_mem m hm

end UnforcedLeray.Short.IIIa
