import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.Pieces

/-!
# `PartIII-b:C/rep/8/1/1/2` (`geomY`): assembly of `GeomYAt` from the pieces

Source `the November 2 reference manuscript`
5427-5432: `Y₁ - Y^mt = (YA - mnYA) + (YB - mnYB)` by the two exact formulas, so
`|D(Y₁-Y^mt)| ≤ |D(YA-mnYA)| + |D(YB-mnYB)|`, and the normalized phase `L²` norm is subadditive.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- Almost every phase gives almost every cell position (the phase is affine in `q`). -/
theorem ae_chartTau {R : ℝ} (hR : R ≠ 0) (s η : ℝ) {P : ℝ → Prop} (h : ∀ᵐ τ : ℝ, P τ) :
    ∀ᵐ q : ℝ, P (NearInst.chartTau R (s, (q, η))) := by
  have h2 : Measure.QuasiMeasurePreserving (fun q : ℝ => (2 / R) * q) volume volume := by
    refine ⟨measurable_const_mul _, ?_⟩
    rw [Real.map_volume_mul_left (div_ne_zero two_ne_zero hR)]
    exact Measure.smul_absolutelyContinuous
  have h3 := (measurePreserving_add_right volume (Real.log s)).quasiMeasurePreserving
  have h4 := (h3.comp h2).ae h
  filter_upwards [h4] with q hq
  have : NearInst.chartTau R (s, (q, η)) = 2 / R * q + Real.log s := by
    simp only [NearInst.chartTau]; ring
  rw [this]; exact hq

theorem cellL2_mono_ae (R c : ℝ) (F G : ℝ → Space → ℝ) (s η : ℝ)
    (h : ∀ᵐ q ∂(volume.restrict (Ico (-c / 2) (c / 2))),
      F (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η))) ≤
        G (NearInst.chartTau R (s, (q, η))) (NearInst.chartY R (s, (q, η)))) :
    cellL2 R c F s η ≤ cellL2 R c G s η := by
  unfold cellL2
  refine ENNReal.rpow_le_rpow (lintegral_mono_ae ?_) (by norm_num)
  filter_upwards [h] with q hq
  gcongr

theorem varrho_chartY {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : 0 < s) (q η : ℝ) :
    0 < ϱ (NearInst.chartY R (s, (q, η))) := by
  unfold ϱ NearInst.chartY
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  apply Real.sqrt_pos.2
  have : 0 < R / Real.sqrt s := div_pos hR (Real.sqrt_pos.2 hs)
  positivity

theorem isOpen_varrho_pos : IsOpen {y : Space | 0 < ϱ y} := by
  refine isOpen_lt continuous_const ?_
  unfold ϱ
  fun_prop

section Regime

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- Pointwise splitting of `ycmp` at a phase where the formulas and differentiability hold. -/
theorem ycmp_eq_of (T : LStr Pl K L) (τ : ℝ) (y : Space) (hy : 0 < ϱ y)
    (hF : ∀ y : Space, 0 < ϱ y →
      actY Pl K L μ T τ y = actYA Pl K L μ T τ y + actYB Pl K L μ T τ y)
    (hM : ∀ y : Space, 0 < ϱ y →
      mnY Pl K L μ T τ y = mnYA Pl K L μ T τ y + mnYB Pl K L μ T τ y)
    (hD : DifferentiableAt ℝ (actYA Pl K L μ T τ) y ∧ DifferentiableAt ℝ (actYB Pl K L μ T τ) y ∧
      DifferentiableAt ℝ (mnYA Pl K L μ T τ) y ∧ DifferentiableAt ℝ (mnYB Pl K L μ T τ) y) :
    ycmp Pl K L μ T τ y = ‖dYA Pl K L μ T τ y + dYB Pl K L μ T τ y‖ := by
  obtain ⟨h1, h2, h3, h4⟩ := hD
  have hnb : {y : Space | 0 < ϱ y} ∈ 𝓝 y := isOpen_varrho_pos.mem_nhds hy
  have e1 : actY Pl K L μ T τ =ᶠ[𝓝 y] fun y => actYA Pl K L μ T τ y + actYB Pl K L μ T τ y := by
    filter_upwards [hnb] with y' hy' using hF y' hy'
  have e2 : mnY Pl K L μ T τ =ᶠ[𝓝 y] fun y => mnYA Pl K L μ T τ y + mnYB Pl K L μ T τ y := by
    filter_upwards [hnb] with y' hy' using hM y' hy'
  unfold ycmp dYA dYB
  rw [e1.fderiv_eq, e2.fderiv_eq, fderiv_fun_add h1 h2, fderiv_fun_add h3 h4]
  congr 1
  abel

/-- **`GeomYAt` from the pieces** (source 5427-5432). -/
theorem geomYAt_of {C : ℝ} {k : ℕ} (hL : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy)
    (hF : ActYFormulaAt Pl K L μ) (hM : MeanYFormulaAt Pl K L μ) (hD : YTermsDiffAt Pl K L μ)
    (hA : GeomYAAt Pl K L μ C k) (hB : GeomYBAt Pl K L μ C k) :
    GeomYAt Pl K L μ (2 * C) k := by
  intro T hTz s hs η
  obtain ⟨hAm, hAb⟩ := hA hL T hTz s hs η
  obtain ⟨hBm, hBb⟩ := hB hL T hTz s hs η
  have hR : L.ε⁻¹ ≠ 0 := inv_ne_zero L.ε_pos.ne'
  have hae : ∀ᵐ τ : ℝ, ∀ y : Space, 0 < ϱ y →
      ycmp Pl K L μ T τ y = ‖dYA Pl K L μ T τ y + dYB Pl K L μ T τ y‖ := by
    filter_upwards [hF T, hD hL T] with τ h1 h2 y hy
    exact ycmp_eq_of Pl K L μ T τ y hy h1 (fun y' hy' => hM hL T τ y' hy') (h2 y hy)
  have hq : ∀ᵐ q ∂(volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))),
      ycmp Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η))) =
        ‖dYA Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η))) +
          dYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η))) (NearInst.chartY L.ε⁻¹ (s, (q, η)))‖ := by
    refine ae_restrict_of_ae ?_
    filter_upwards [ae_chartTau hR s η hae] with q hq
    exact hq _ (varrho_chartY (inv_pos.2 L.ε_pos) hs.1 q η)
  refine ⟨((hAm.add hBm).norm.aemeasurable).congr (hq.mono fun q h => h.symm), ?_⟩
  have hAm' : AEMeasurable (fun q : ℝ => ‖dYA Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
      (NearInst.chartY L.ε⁻¹ (s, (q, η)))‖) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) :=
    hAm.norm.aemeasurable
  have hBm' : AEMeasurable (fun q : ℝ => ‖dYB Pl K L μ T (NearInst.chartTau L.ε⁻¹ (s, (q, η)))
      (NearInst.chartY L.ε⁻¹ (s, (q, η)))‖) (volume.restrict (Ico (-cOf L.ν / 2) (cOf L.ν / 2))) :=
    hBm.norm.aemeasurable
  have h1 : cellL2 L.ε⁻¹ (cOf L.ν) (ycmp Pl K L μ T) s η ≤
      cellL2 L.ε⁻¹ (cOf L.ν) (fun τ y => ‖dYA Pl K L μ T τ y‖ + ‖dYB Pl K L μ T τ y‖) s η := by
    refine cellL2_mono_ae _ _ _ _ _ _ ?_
    filter_upwards [hq] with q h
    rw [h]
    exact norm_add_le _ _
  have h2 := cellL2_add_le L.ε⁻¹ (cOf L.ν) (fun τ y => ‖dYA Pl K L μ T τ y‖)
    (fun τ y => ‖dYB Pl K L μ T τ y‖) (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _) s η
    hAm' hBm'
  refine h1.trans (h2.trans ?_)
  have e : ENNReal.ofReal (2 * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) =
      2 * ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) := by
    rw [show 2 * C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) =
      2 * (C * L.ν⁻¹ ^ k * (L.ε ^ 4 * s ^ (5 / 2 : ℝ))) by ring,
      ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [e, mul_assoc]
  calc _ ≤ _ := add_le_add hAb hBb
    _ = _ := by rw [← two_mul, mul_assoc]

theorem geomYAAt_mono {C C' : ℝ} {k k' : ℕ} (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') (h : GeomYAAt Pl K L μ C k) : GeomYAAt Pl K L μ C' k' := by
  intro hL T hTz s hs η
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact ⟨(h hL T hTz s hs η).1,
    bound_mono L.ν_pos hν1 (mul_nonneg he hs0) hC hC' hk (h hL T hTz s hs η).2⟩

theorem geomYBAt_mono {C C' : ℝ} {k k' : ℕ} (hν1 : L.ν ≤ 1) (hC : C ≤ C')
    (hC' : 0 ≤ C') (hk : k ≤ k') (h : GeomYBAt Pl K L μ C k) : GeomYBAt Pl K L μ C' k' := by
  intro hL T hTz s hs η
  have hs0 : 0 ≤ s ^ (5 / 2 : ℝ) := Real.rpow_nonneg hs.1.le _
  have he : 0 ≤ L.ε ^ 4 := by have := L.ε_pos; positivity
  exact ⟨(h hL T hTz s hs η).1,
    bound_mono L.ν_pos hν1 (mul_nonneg he hs0) hC hC' hk (h hL T hTz s hs η).2⟩

end Regime

namespace SeqData

variable (D : SeqData)

/-- **`SeqData.GeomY` from the sequence pieces** (source 5427-5432). -/
theorem geomY_of (hLH : D.LHypSeq) (hν : ∀ᶠ n : ℕ in atTop, (D.level n).ν ≤ 1)
    (hF : D.ActYFormula) (hM : D.MeanYFormula) (hD : D.YTermsDiff) (hA : D.GeomYA)
    (hB : D.GeomYB) : D.GeomY := by
  obtain ⟨C₁, k₁, h₁⟩ := hA
  obtain ⟨C₂, k₂, h₂⟩ := hB
  refine ⟨2 * max |C₁| |C₂|, max k₁ k₂, ?_⟩
  filter_upwards [h₁, h₂, hν, hLH, hF, hM, hD] with n hn₁ hn₂ hν1 hL hF' hM' hD' z hz
  have hC0 : 0 ≤ max |C₁| |C₂| := le_trans (abs_nonneg _) (le_max_left _ _)
  have hA' := geomYAAt_mono D.Pl D.K (D.level n) (D.mu n z) hν1 ((le_abs_self C₁).trans
    (le_max_left _ _)) hC0 (le_max_left k₁ k₂) (hn₁ z hz)
  have hB' := geomYBAt_mono D.Pl D.K (D.level n) (D.mu n z) hν1 ((le_abs_self C₂).trans
    (le_max_right _ _)) hC0 (le_max_right k₁ k₂) (hn₂ z hz)
  exact geomYAt_of D.Pl D.K (D.level n) (D.mu n z) (hL z hz) (hF' z hz) (hM' z hz) (hD' z hz) hA' hB'

end SeqData

end UnforcedLeray.Short.PartIIIb.Concrete
