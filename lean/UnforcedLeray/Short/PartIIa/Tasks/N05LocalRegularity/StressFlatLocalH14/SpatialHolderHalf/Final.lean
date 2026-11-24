import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.StressFlatLocalH14.SpatialHolderHalf.Ident

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 UnforcedLeray.B0223 N05_4Aux N05_4_1Aux

namespace SHH

instance (c : ℝ) : IsLocallyFiniteMeasure (cellMeasure c) := by
  unfold cellMeasure; infer_instance

theorem ae_mem_U (c : ℝ) :
    ∀ᵐ p ∂(cellMeasure c), p ∈ (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) c ×ˢ (univ : Set ℝ) : Set Profile) := by
  have hnull : cellMeasure c {p : Profile | p.2.1 = c} = 0 := by
    unfold cellMeasure
    refine le_antisymm ((Measure.restrict_le_self _).trans ?_) bot_le
    have : {p : Profile | p.2.1 = c} = (univ : Set ℝ) ×ˢ (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
      ext p; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  filter_upwards [ae_cell_cellMeasure c, measure_eq_zero_iff_ae_notMem.1 hnull] with p hp hn
  obtain ⟨h1, h2, _⟩ := hp
  have : p.2.1 < c := lt_of_le_of_ne h2.2 hn
  exact ⟨h1, ⟨h2.1, this⟩, trivial⟩

theorem ae_eq_W {c : ℝ} (hc : 0 < c) {j : Fin 2} {u dq : Profile → MeridC}
    (hd : WD c j u dq) {h : ℝ} (hh0 : 0 < h) :
    (fun p => u (sj j h p) - u p) =ᵐ[cellMeasure c] Wd j h dq := by
  set μ := cellMeasure c with hμ
  set f : Profile → MeridC := fun p => (u (sj j h p) - u p) - Wd j h dq p with hf
  have hfm : Measurable f :=
    ((hd.mu.comp (measurable_sj j h)).sub hd.mu).sub (stronglyMeasurable_W j h hd.mdq).measurable
  have hfL : MemLp f 2 μ :=
    ((memLp_comp_sj hc j h hd.mu hd.pu hd.lu).sub hd.lu).sub (memLp_W hc j hh0 hd.mdq hd.pdq hd.ldq)
  have hfloc : LocallyIntegrable f μ := hfL.locallyIntegrable (by norm_num)
  have htest : ∀ φ : Profile → MeridC, IsMeridTest c φ → ∫ p, inner ℂ (f p) (φ p) ∂μ = 0 := by
    intro φ hφ
    have hφL : MemLp φ 2 μ := memLp_of_isMeridTest_cellMeasure hc hφ
    have h1 := key_identity hc hd hh0 hφ
    have hi1 : Integrable (fun p => inner ℂ (u (sj j h p) - u p) (φ p)) μ :=
      integrable_inner_cellMeasure ((memLp_comp_sj hc j h hd.mu hd.pu hd.lu).sub hd.lu) hφL
    have hi2 : Integrable (fun p => inner ℂ (Wd j h dq p) (φ p)) μ :=
      integrable_inner_cellMeasure (memLp_W hc j hh0 hd.mdq hd.pdq hd.ldq) hφL
    have e : (fun p => inner ℂ (f p) (φ p)) = fun p =>
        inner ℂ (u (sj j h p) - u p) (φ p) - inner ℂ (Wd j h dq p) (φ p) := by
      funext p; simp only [hf]; rw [inner_sub_left]
    rw [e, integral_sub hi1 hi2, h1, sub_self]
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) c ×ˢ (univ : Set ℝ) : Set Profile) :=
    isOpen_Ioi.prod (isOpen_Ioo.prod isOpen_univ)
  have hFL := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := μ) (f := f)
    (hfloc.locallyIntegrableOn _) (by
      intro g hg hgc hgU
      obtain ⟨Φ, hΦ, hΦper, hΦeq, s0, s1, L, hs0, hband⟩ := exists_periodic_ext hc hg hgc hgU
      have hint : Integrable (fun p => g p • f p) μ :=
        hfloc.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
      set x : MeridC := ∫ p, g p • f p ∂μ with hx
      have hall : ∀ e : MeridC, inner ℂ x e = 0 := by
        intro e
        have hφe : IsMeridTest c (fun p => Φ p • e) :=
          ⟨hΦ.smul contDiff_const, fun p => by simp only [hΦper p], ⟨s0, s1, L, hs0, fun p hp => by
            refine hband p ?_
            intro h0; apply hp; simp [h0]⟩⟩
        have h0 := htest _ hφe
        have h2 : ∫ p, inner ℂ (f p) (Φ p • e) ∂μ = ∫ p, inner ℂ (g p • f p) e ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [ae_cell_cellMeasure c] with p hp
          rw [hΦeq p hp, ← Complex.coe_smul (g p) e, ← Complex.coe_smul (g p) (f p),
            inner_smul_right, inner_smul_left, Complex.conj_ofReal]
        rw [h2, integral_inner_right hint e] at h0
        exact h0
      have := hall x
      rw [inner_self_eq_zero] at this
      exact this)
  filter_upwards [hFL, ae_mem_U c] with p h1 h2
  exact sub_eq_zero.1 (h1 h2)

theorem diffq_pos {c : ℝ} (hc : 0 < c) {j : Fin 2} {u dq : Profile → MeridC}
    (hd : WD c j u dq) {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    ∫ p, ‖u (sj j h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤
      (∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c)) * h := by
  have hae := ae_eq_W hc hd hh0
  have hI : 0 ≤ ∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun p => sq_nonneg _
  calc ∫ p, ‖u (sj j h p) - u p‖ ^ 2 ∂(cellMeasure c)
      = ∫ p, ‖Wd j h dq p‖ ^ 2 ∂(cellMeasure c) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with p hp
        rw [hp]
    _ ≤ h ^ 2 * ∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c) := integral_W_le hc j hh0 hd.mdq hd.pdq hd.ldq
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hI hh0.le) (sub_nonneg.2 hh1)]

theorem diffq_generic {c : ℝ} (hc : 0 < c) {j : Fin 2} {u dq : Profile → MeridC}
    (hd : WD c j u dq) {h : ℝ} (hh : h ∈ Icc (-1 : ℝ) 1) :
    ∫ p, ‖u (sj j h p) - u p‖ ^ 2 ∂(cellMeasure c) ≤
      (∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c)) * |h| := by
  have hI : 0 ≤ ∫ p, ‖dq p‖ ^ 2 ∂(cellMeasure c) := integral_nonneg fun p => sq_nonneg _
  rcases lt_trichotomy h 0 with hneg | hzero | hpos
  · have hpos' := diffq_pos hc hd (h := -h) (by linarith) (by linarith [hh.1])
    have hG := integral_sj_eq_real hc j h
      (G := fun q => ‖u (sj j (-h) q) - u q‖ ^ 2)
      (((hd.mu.comp (measurable_sj j _)).sub hd.mu).norm.pow_const 2)
      (fun p => by
        simp only [periodic_sj_comp j (-h) hd.pu p, hd.pu p])
    simp only [sj_neg_sj] at hG
    have e : ∫ p, ‖u (sj j h p) - u p‖ ^ 2 ∂(cellMeasure c) =
        ∫ p, ‖u p - u (sj j h p)‖ ^ 2 ∂(cellMeasure c) := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [norm_sub_rev]
    rw [e, hG, abs_of_neg hneg]
    exact hpos'
  · subst hzero
    simp [sj_zero_t]
  · rw [abs_of_pos hpos]
    exact diffq_pos hc hd hpos hh.2

theorem cellL2Norm_sq (c : ℝ) (u : Profile → MeridC) :
    cellL2Norm c u ^ 2 = ∫ p, ‖u p‖ ^ 2 ∂(cellMeasure c) := by
  unfold cellL2Norm
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)]

end SHH

theorem cellWeakQDiffQuotient : CellWeakQDiffQuotient := by
  intro c σ H1 L1 hc _ _ _ u dq hu hdq hpu hpdq _ _ hLu hLdq hweak h hh
  have hd : SHH.WD c 0 u dq := ⟨hu, hdq, hpu, hpdq, hLu, hLdq, fun φ hφ => by
    simpa [pdSpatial] using hweak φ hφ⟩
  have := SHH.diffq_generic hc hd hh
  rw [SHH.sj_zero_eq] at this
  rwa [SHH.cellL2Norm_sq]

theorem cellWeakEtaDiffQuotient : CellWeakEtaDiffQuotient := by
  intro c σ H1 L1 hc _ _ _ u dq hu hdq hpu hpdq _ _ hLu hLdq hweak h hh
  have hd : SHH.WD c 1 u dq := ⟨hu, hdq, hpu, hpdq, hLu, hLdq, fun φ hφ => by
    simpa [pdSpatial] using hweak φ hφ⟩
  have := SHH.diffq_generic hc hd hh
  rw [SHH.sj_one_eq] at this
  rwa [SHH.cellL2Norm_sq]

end UnforcedLeray.Short.PartIIa
