import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarOf
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarId
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.SepDomFacts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.FarDomChart
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelL2.farOutMeasurable
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_1.FiniteCompacts
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# `SepFarAbs` (PartIII-b:C/rep/4/4/1/org/1/1/inv/far/1, source 3604-3621, 3905-3912, 4163-4174)

Finiteness of the order-zero gap majorant of the lift of `strSum F` at a.e. young chart point.
(A) `sepDom` sees only the a.e. class of the source; (B) `IIIa.sepDomPointwise` gives a finite
`L²_τ` norm at every `y`, hence finiteness at a.e. phase, periodically; (C) the chart transfer
`x ↦ (chartTau x, chartY x)`; (D) antitonicity in the gap.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal Topology
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- (A) `sepDom` sees only the a.e. class of the source. -/
theorem fa_sepDom_congr_ae (a : ℝ) (j : ℕ) (D : ℝ) (g₁ g₂ : ℝ → Space → ℝ≥0∞)
    (h : ∀ᵐ x : ℝ × Space ∂(volume : Measure (ℝ × Space)), g₁ x.1 x.2 = g₂ x.1 x.2)
    (τ : ℝ) (y : Space) :
    UnforcedLeray.Short.IIIa.sepDom a j D g₁ τ y = UnforcedLeray.Short.IIIa.sepDom a j D g₂ τ y := by
  have hτ : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ z ∂(volume : Measure Space), g₁ t z = g₂ t z :=
    Measure.ae_ae_of_ae_prod h
  have hNt0 : (volume : Measure ℝ) {t : ℝ | ¬ ∀ᵐ z ∂(volume : Measure Space),
      g₁ t z = g₂ t z} = 0 := ae_iff.1 hτ
  have hl : ∀ᵐ l ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)),
      ∀ᵐ z ∂(volume : Measure Space), g₁ (τ + 2 * Real.log l) z = g₂ (τ + 2 * Real.log l) z := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    have hsub : {l : ℝ | ¬ (l ∈ Ioo (0 : ℝ) 1 → ∀ᵐ z ∂(volume : Measure Space),
        g₁ (τ + 2 * Real.log l) z = g₂ (τ + 2 * Real.log l) z)}
        ⊆ (fun t : ℝ => Real.exp ((t - τ) / 2)) ''
          {t : ℝ | ¬ ∀ᵐ z ∂(volume : Measure Space), g₁ t z = g₂ t z} := by
      intro l hl
      obtain ⟨hI, hbad⟩ := not_imp.1 hl
      refine ⟨τ + 2 * Real.log l, hbad, ?_⟩
      show Real.exp ((τ + 2 * Real.log l - τ) / 2) = l
      rw [show (τ + 2 * Real.log l - τ) / 2 = Real.log l by ring, Real.exp_log hI.1]
    have hfnull : (volume : Measure ℝ) ((fun t : ℝ => Real.exp ((t - τ) / 2)) ''
        {t : ℝ | ¬ ∀ᵐ z ∂(volume : Measure Space), g₁ t z = g₂ t z}) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        (by fun_prop) hNt0
    exact ae_iff.2 (measure_mono_null hsub hfnull)
  unfold UnforcedLeray.Short.IIIa.sepDom
  refine lintegral_congr_ae ?_
  filter_upwards [hl] with l hl'
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hl'] with z hz
  simp only [hz]

/-- A `P`-periodic function that is finite a.e. on one period is finite a.e. -/
theorem fa_periodic_ae (P : ℝ) (hP : 0 < P) (f : ℝ → ℝ≥0∞) (hper : ∀ τ, f (τ + P) = f τ)
    (h : ∀ᵐ τ ∂((volume : Measure ℝ).restrict (Ioc 0 P)), f τ < ⊤) :
    ∀ᵐ τ : ℝ, f τ < ⊤ := by
  have hB' : (volume : Measure ℝ) ({τ | ¬ f τ < ⊤} ∩ Ioc 0 P) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc] at h
    refine measure_mono_null ?_ (ae_iff.1 h)
    intro τ hτ hh
    exact hτ.1 (hh hτ.2)
  have hper' : Function.Periodic f P := hper
  rw [ae_iff]
  have hsub : {τ | ¬ f τ < ⊤} ⊆
      ⋃ k : ℤ, (fun t : ℝ => t + (-(k • P))) ⁻¹' ({τ | ¬ f τ < ⊤} ∩ Ioc 0 P) := by
    intro t ht
    simp only [mem_iUnion]
    refine ⟨toIocDiv hP 0 t, ?_, ?_⟩
    · show ¬ f (t + -(toIocDiv hP 0 t • P)) < ⊤
      rw [← sub_eq_add_neg, hper'.sub_zsmul_eq]
      exact ht
    · have := sub_toIocDiv_zsmul_mem_Ioc hP 0 t
      simpa [sub_eq_add_neg] using this
  refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
  rw [measure_preimage_add_right]
  exact hB'

theorem fa_measurable_srcNorm (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j) :
    Measurable (Function.uncurry (UnforcedLeray.Short.IIIa.srcNorm T)) := by
  unfold UnforcedLeray.Short.IIIa.srcNorm UnforcedLeray.Short.IIIa.tensorNorm Function.uncurry
  refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp ?_)
  refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
  exact (hT i j).pow_const 2

/-- (B) finiteness at every receiver for a.e. phase. -/
theorem fa_finite_phase (μ D P r : ℝ) (hμ : -(1 / 4) < μ) (hD : 0 < D) (hP : 0 < P)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (hsrc : UnforcedLeray.Short.IIIa.IsSepSource P r T)
    (hfin : UnforcedLeray.Short.IIIa.ltauLq P (22 / 19) (UnforcedLeray.Short.IIIa.srcNorm T) < ⊤)
    (y : Space) :
    ∀ᵐ τ : ℝ, UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 D
        (UnforcedLeray.Short.IIIa.srcNorm T) τ y < ⊤ := by
  obtain ⟨C, hC0, hC⟩ := UnforcedLeray.Short.IIIa.sepDomPointwise 0 (22 / 19) (22 / 3) 1
    (by norm_num) (by norm_num) (by norm_num) one_pos
  have hmeas := fa_measurable_srcNorm T hsrc.measurable
  have hper : ∀ τ z, UnforcedLeray.Short.IIIa.srcNorm T (τ + P) z =
      UnforcedLeray.Short.IIIa.srcNorm T τ z := by
    intro τ z
    unfold UnforcedLeray.Short.IIIa.srcNorm
    rw [hsrc.periodic]
  have h1 := hC (2 * μ + 2) (by linarith) (by norm_num; linarith) D P hD hP _ hmeas hper y
  have h2 : UnforcedLeray.Short.IIIa.ltauAt P
      (fun τ => UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 D
        (UnforcedLeray.Short.IIIa.srcNorm T) τ y) < ⊤ :=
    lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  unfold UnforcedLeray.Short.IIIa.ltauAt at h2
  have h3 := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).1 h2
  have h4 : ∫⁻ τ in Ioc 0 P, UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 D
      (UnforcedLeray.Short.IIIa.srcNorm T) τ y ^ (2 : ℝ) < ⊤ := by
    rcases ENNReal.mul_lt_top_iff.1 h3 with ⟨_, h⟩ | h | h
    · exact h
    · exfalso
      have : (ENNReal.ofReal P)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
      exact this h
    · rw [h]; exact ENNReal.zero_lt_top
  have hfm : Measurable fun τ => UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 D
      (UnforcedLeray.Short.IIIa.srcNorm T) τ y :=
    Measurable.of_uncurry_right (sd_measurable_sepDom _ 0 D _ hmeas)
  have h5 : ∀ᵐ τ ∂((volume : Measure ℝ).restrict (Ioc 0 P)),
      UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 D
        (UnforcedLeray.Short.IIIa.srcNorm T) τ y ^ (2 : ℝ) < ⊤ :=
    ae_lt_top (hfm.pow_const _) h4.ne
  have h6 : ∀ᵐ τ ∂((volume : Measure ℝ).restrict (Ioc 0 P)),
      UnforcedLeray.Short.IIIa.sepDom (2 * μ + 2) 0 D
        (UnforcedLeray.Short.IIIa.srcNorm T) τ y < ⊤ := by
    filter_upwards [h5] with τ hτ
    by_contra hh
    rw [not_lt_top_iff] at hh
    rw [hh, ENNReal.top_rpow_of_pos (by norm_num)] at hτ
    exact lt_irrefl _ hτ
  refine fa_periodic_ae P hP _ ?_ h6
  intro τ
  unfold UnforcedLeray.Short.IIIa.sepDom
  refine lintegral_congr (fun l => ?_)
  congr 1
  refine lintegral_congr (fun z => ?_)
  rw [add_right_comm, hper]

/-- (C) chart transfer. -/
theorem fa_chart_null (R c : ℝ) (hR : 0 < R) (a : ℝ) (f : ℝ → Space → ℝ≥0∞)
    (hf : Measurable (Function.uncurry f)) (hy : ∀ y, ∀ᵐ τ : ℝ, f τ y < ⊤) :
    ∀ᵐ x ∂(ageμ c a), f (NearInst.chartTau R x) (NearInst.chartY R x) < ⊤ := by
  have hg : Measurable fun x : Chart => f (NearInst.chartTau R x) (NearInst.chartY R x) :=
    hf.comp ((NearInst.Masked.measurable_chartTau_fn R).prodMk
      (NearInst.Masked.measurable_chartY_fn R))
  have hSm : MeasurableSet {x : Chart | ¬ f (NearInst.chartTau R x) (NearInst.chartY R x) < ⊤} := by
    have : {x : Chart | ¬ f (NearInst.chartTau R x) (NearInst.chartY R x) < ⊤}
        = (fun x : Chart => f (NearInst.chartTau R x) (NearInst.chartY R x)) ⁻¹' {⊤} := by
      ext x; simp [not_lt_top_iff]
    rw [this]
    exact hg (measurableSet_singleton _)
  rw [ae_iff]
  unfold ageμ
  rw [Measure.prod_apply hSm]
  refine (lintegral_congr (fun s => ?_)).trans lintegral_zero
  show Cyl.avgμ c (Prod.mk s ⁻¹' _) = 0
  have hle : ∀ A : Set (ℝ × ℝ), Cyl.avgμ c A ≤ ENNReal.ofReal c⁻¹ * volume A := by
    intro A
    unfold Cyl.avgμ Cyl.cellμ
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
  refine le_antisymm ?_ zero_le
  refine (hle _).trans ?_
  have hz : (volume : Measure (ℝ × ℝ)) (Prod.mk s ⁻¹'
      {x : Chart | ¬ f (NearInst.chartTau R x) (NearInst.chartY R x) < ⊤}) = 0 := by
    have hm : MeasurableSet (Prod.mk s ⁻¹'
        {x : Chart | ¬ f (NearInst.chartTau R x) (NearInst.chartY R x) < ⊤}) :=
      measurable_prodMk_left hSm
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hm]
    refine (lintegral_congr (fun η => ?_)).trans lintegral_zero
    have hset : (fun q : ℝ => (q, η)) ⁻¹' (Prod.mk s ⁻¹'
        {x : Chart | ¬ f (NearInst.chartTau R x) (NearInst.chartY R x) < ⊤})
        = (fun q : ℝ => (2 / R) * q) ⁻¹' ((fun u : ℝ => u + Real.log s) ⁻¹'
            {τ | ¬ f τ (NearInst.chartY R (s, (0, η))) < ⊤}) := by
      ext q
      simp only [mem_preimage, mem_setOf_eq, NearInst.chartTau, NearInst.chartY]
      rw [show 2 * q / R = 2 / R * q by ring]
    rw [hset, Real.volume_preimage_mul_left (by positivity), measure_preimage_add_right]
    have h0 : (volume : Measure ℝ) {τ | ¬ f τ (NearInst.chartY R (s, (0, η))) < ⊤} = 0 :=
      ae_iff.1 (hy _)
    rw [h0, mul_zero]
  rw [hz, mul_zero]

/-- **Absolute convergence of the masked `sep:resolvent` integral at a young receiver.** -/
theorem sepFarAbs (dm dp : ℝ) : SepFarAbs dm dp := by
  intro D hst
  filter_upwards [muWin_gt_quarter D hst] with n hmu
  intro z hz F g₁ g₂ T hg hT
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hε : 0 < (D.level n).ε := (D.level n).ε_pos
  have hc : 0 < cOf (D.level n).ν := cOf_pos hν
  have hR : 0 < (D.level n).ε⁻¹ := inv_pos.2 hε
  obtain ⟨hsrc, hTeq, _, hfin⟩ := hT
  have hG := strSum_lift_ae D.Pl D.K (D.level n) hst.C0_pos F g₁ g₂ hg
  have hGT : ∀ᵐ x : ℝ × Space ∂volume,
      UnforcedLeray.Short.IIIa.srcNorm
          (NearInst.cartLift (D.level n).ε⁻¹ (cOf (D.level n).ν) (strSum F)) x.1 x.2
        = UnforcedLeray.Short.IIIa.srcNorm T x.1 x.2 := by
    filter_upwards [hG, hTeq] with x h1 h2
    unfold UnforcedLeray.Short.IIIa.srcNorm
    rw [h1, h2]
    rfl
  have hpos : 0 < 1 - Real.exp (-(D.K.δ / 2)) := by
    have := Real.exp_lt_exp.2 (show -(D.K.δ / 2) < 0 by linarith [hst.δ_pos])
    rw [Real.exp_zero] at this
    linarith
  have hD0 : 0 < (1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ * Real.sqrt (D.level n).ν :=
    mul_pos (mul_pos hpos hR) (Real.sqrt_pos.2 hν)
  have hP : 0 < 2 * (D.level n).ε * cOf (D.level n).ν := by positivity
  have hfp := fun y => fa_finite_phase (D.mu n z) _ _ _ (hmu z hz) hD0 hP T hsrc hfin y
  have hch := fa_chart_null (D.level n).ε⁻¹ (cOf (D.level n).ν) hR (-3 / 2)
    (UnforcedLeray.Short.IIIa.sepDom (2 * D.mu n z + 2) 0
      ((1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ * Real.sqrt (D.level n).ν)
      (UnforcedLeray.Short.IIIa.srcNorm T))
    (sd_measurable_sepDom _ 0 _ _ (fa_measurable_srcNorm T hsrc.measurable)) hfp
  filter_upwards [hch, fc_ae_pos (cOf (D.level n).ν) (-3 / 2)] with x hx hxpos hle
  have hs : Real.sqrt (D.level n).ν * Real.sqrt x.1 ≤ 1 := by
    rw [← Real.sqrt_mul hν.le]
    calc Real.sqrt ((D.level n).ν * x.1) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  have hsx : 0 < Real.sqrt x.1 := Real.sqrt_pos.2 hxpos
  have hgap : (1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ * Real.sqrt (D.level n).ν ≤
      (1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ / Real.sqrt x.1 := by
    rw [le_div_iff₀ hsx]
    have hpr : 0 < (1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ := mul_pos hpos hR
    calc (1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ * Real.sqrt (D.level n).ν *
          Real.sqrt x.1
        = (1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ *
          (Real.sqrt (D.level n).ν * Real.sqrt x.1) := by ring
      _ ≤ (1 - Real.exp (-(D.K.δ / 2))) * (D.level n).ε⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hs hpr.le
      _ = _ := mul_one _
  rw [fa_sepDom_congr_ae _ _ _ _
    (UnforcedLeray.Short.IIIa.srcNorm T) hGT]
  exact lt_of_le_of_lt (fd_sepDom_anti _ _ _ _ hgap _ _ _) hx

end UnforcedLeray.Short.PartIIIb.Concrete
