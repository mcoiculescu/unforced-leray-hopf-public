import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier.Kernel

/-!
# Part III-a, `PartIII-a:T18/3/1/3/1`: the scalar mollifier as a convolution

Source of record: `the November 2 reference manuscript` lines 3427-3440 and
3541-3552. `lmJs c k g` is the plane convolution of the bump with the periodic extension of `g`; it
is smooth, and its derivative falls on the kernel, hence commutes with weak derivatives on the
cylinder.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff Convolution

namespace UnforcedLeray.Short.IIIa

/-- A bounded measurable function vanishing for `|z₂| ≥ c/3`, composed with `y ↦ x - y`, lies in
every `L^p(cell)`. -/
theorem lm_memLp_band {c : ℝ} {h : ℝ × ℝ → ℝ} (hm : Measurable h) {M : ℝ}
    (hM : ∀ z : ℝ × ℝ, |h z| ≤ M) (hb : ∀ z : ℝ × ℝ, c / 3 ≤ |z.2| → h z = 0) (x : ℝ × ℝ)
    (p : ℝ≥0∞) : MemLp (fun y => h (x - y)) p (volume.restrict (B0579.cell c)) := by
  set S : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ Icc (x.2 - c / 3) (x.2 + c / 3) with hSdef
  have hS : MeasurableSet S := measurableSet_Ico.prod measurableSet_Icc
  have hSsub : S ⊆ B0579.cell c := fun z hz => ⟨hz.1, mem_univ _⟩
  have hfin : volume S < ⊤ :=
    lt_of_le_of_lt (measure_mono (prod_mono Ico_subset_Icc_self subset_rfl))
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have : IsFiniteMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hmeas : Measurable (fun y : ℝ × ℝ => h (x - y)) := hm.comp (measurable_const.sub measurable_id)
  have h1 : MemLp (fun y => h (x - y)) p (volume.restrict S) :=
    MemLp.of_bound hmeas.aestronglyMeasurable M
      (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hM _)
  have h2 : MemLp (S.indicator fun y => h (x - y)) p (volume.restrict (B0579.cell c)) := by
    rw [memLp_indicator_iff_restrict hS, Measure.restrict_restrict_of_subset hSsub]
    exact h1
  refine MemLp.ae_eq ?_ h2
  refine ae_restrict_of_forall_mem (B0579.measurableSet_cell c) fun y hy => ?_
  by_cases hyS : y ∈ S
  · simp [indicator_of_mem hyS]
  · have hband : c / 3 ≤ |(x - y).2| := by
      by_contra hcon
      push Not at hcon
      rw [Prod.snd_sub, abs_lt] at hcon
      exact hyS ⟨hy.1, ⟨by linarith [hcon.2], by linarith [hcon.1]⟩⟩
    simp [indicator_of_notMem hyS, hb _ hband]

theorem lmJs_integrable {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (x : ℝ × ℝ) :
    Integrable (fun y => (lmK c k (x - y) : ℂ) * g y) (volume.restrict (B0579.cell c)) := by
  obtain ⟨M, hM⟩ := lmK_bdd c k
  have h1 := lm_memLp_band (c := c) (measurable_lmK c k) hM
    (fun z hz => lmK_eq_zero_of_snd hc k (by linarith)) x 2
  have h2 : MemLp (fun y => (lmK c k (x - y) : ℂ)) 2 (volume.restrict (B0579.cell c)) :=
    Complex.ofRealCLM.comp_memLp' h1
  exact h2.integrable_mul hg

theorem lmExt_periodic {c : ℝ} (hc : 0 < c) (g : ℝ × ℝ → ℂ) (y : ℝ × ℝ) :
    lmExt c g (y.1 + c, y.2) = lmExt c g y := by
  simp only [lmExt, lmPer_add c hc.ne' y]

theorem lmExt_of_mem {c : ℝ} (hc : 0 < c) (g : ℝ × ℝ → ℂ) {y : ℝ × ℝ} (hy : y ∈ B0579.cell c) :
    lmExt c g y = g y := by
  simp only [lmExt, lmPer_of_mem hc hy]

theorem lmExt_integrableOn {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (n : ℤ) (R : ℝ) :
    IntegrableOn (lmExt c g) (Ico (n * c - c / 2) (n * c + c / 2) ×ˢ Icc (-R) R) := by
  set A : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-R) R with hAdef
  have hA : MeasurableSet A := measurableSet_Ico.prod measurableSet_Icc
  have hAsub : A ⊆ B0579.cell c := fun z hz => ⟨hz.1, mem_univ _⟩
  have hfin : volume A < ⊤ :=
    lt_of_le_of_lt (measure_mono (prod_mono Ico_subset_Icc_self subset_rfl))
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have : IsFiniteMeasure (volume.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hgA : IntegrableOn g A :=
    (hg.mono_measure (Measure.restrict_mono hAsub le_rfl)).integrable (by norm_num)
  set v : ℝ × ℝ := (-(n * c), 0) with hv
  have hmp : MeasurePreserving (· + v) (volume : Measure (ℝ × ℝ)) volume :=
    measurePreserving_add_right volume v
  have hemb : MeasurableEmbedding (· + v : ℝ × ℝ → ℝ × ℝ) :=
    (Homeomorph.addRight v).measurableEmbedding
  have h1 : IntegrableOn (g ∘ (· + v)) ((· + v) ⁻¹' A) :=
    (hmp.integrableOn_comp_preimage hemb).2 hgA
  have hpre : ((· + v) ⁻¹' A) = Ico (n * c - c / 2) (n * c + c / 2) ×ˢ Icc (-R) R := by
    ext y
    simp only [hAdef, hv, mem_preimage, mem_prod, mem_Ico, mem_Icc, Prod.fst_add, Prod.snd_add,
      add_zero]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
  rw [hpre] at h1
  refine h1.congr_fun (fun y hy => ?_) (measurableSet_Ico.prod measurableSet_Icc)
  have hmem : y.1 - n * c ∈ Ico (-(c / 2)) (c / 2) :=
    ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩
  have hper := lmPer1_eq_sub_int hc (t := y.1) n hmem
  show g (y + v) = g (lmPer1 c y.1, y.2)
  rw [hper]
  congr 1
  ext <;> simp [hv, sub_eq_add_neg]

theorem lmExt_locallyIntegrable {c : ℝ} (hc : 0 < c) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) : LocallyIntegrable (lmExt c g) := by
  intro z
  obtain ⟨n, hn⟩ := lmPer1_sub_self hc.ne' z.1
  have hmem := lmPer1_mem hc z.1
  rw [hn] at hmem
  set R : ℝ := |z.2| + 1 with hR
  refine ⟨Ioo (z.1 - c / 2) (z.1 + c / 2) ×ˢ Ioo (z.2 - 1) (z.2 + 1), ?_, ?_⟩
  · exact (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · refine (((lmExt_integrableOn hc hg (n - 1) R).union (lmExt_integrableOn hc hg n R)).union
      (lmExt_integrableOn hc hg (n + 1) R)).mono_set ?_
    rintro ⟨q, η⟩ ⟨hq, hη⟩
    have hq1 : z.1 - c / 2 < q := hq.1
    have hq2 : q < z.1 + c / 2 := hq.2
    have hη' : η ∈ Icc (-R) R := by
      have h1 := hη.1
      have h2 := hη.2
      have h3 := le_abs_self z.2
      have h4 := neg_abs_le z.2
      exact ⟨by rw [hR]; linarith, by rw [hR]; linarith⟩
    push_cast
    by_cases h1 : q < n * c - c / 2
    · refine Or.inl (Or.inl ⟨⟨?_, ?_⟩, hη'⟩) <;> nlinarith [hmem.1, hmem.2]
    · by_cases h2 : q < n * c + c / 2
      · exact Or.inl (Or.inr ⟨⟨not_lt.mp h1, h2⟩, hη'⟩)
      · refine Or.inr ⟨⟨?_, ?_⟩, hη'⟩ <;> nlinarith [hmem.1, hmem.2]

theorem lmJs_eq_convolution {c : ℝ} (hc : 0 < c) (k : ℕ) (g : ℝ × ℝ → ℂ) :
    lmJs c k g =
      MeasureTheory.convolution (lmRho c k) (lmExt c g) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  rw [convolution_eq_swap]
  have hh : ∀ z : ℝ × ℝ, c / 3 ≤ |z.1| → lmRho c k z = 0 := fun z hz =>
    lmRho_eq_zero hc k (Or.inl (by linarith))
  have h := lm_cell_unfold hc hh (lmExt_periodic hc g) x
  simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul]
  rw [← h]
  refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y hy => ?_
  simp only [lmK, lmExt_of_mem hc g hy]

theorem lmJs_contDiff {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) : ContDiff ℝ ∞ (lmJs c k g) := by
  rw [lmJs_eq_convolution hc k g]
  exact (lmRho_hasCompactSupport c k).contDiff_convolution_left _ (lmRho_contDiff c k)
    (lmExt_locallyIntegrable hc hg)

theorem lmPd_eq_fderiv {F : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (hF : DifferentiableAt ℝ F x) (j : Fin 2) :
    LMPd j F x = fderiv ℝ F x (B0579.dir j) := by
  have hre : fderiv ℝ (fun y => (F y).re) x = Complex.reCLM.comp (fderiv ℝ F x) :=
    (Complex.reCLM.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  have him : fderiv ℝ (fun y => (F y).im) x = Complex.imCLM.comp (fderiv ℝ F x) :=
    (Complex.imCLM.hasFDerivAt.comp x hF.hasFDerivAt).fderiv
  unfold LMPd B0579.pd
  rw [hre, him]
  simp only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
  rw [mul_comm]
  exact Complex.re_add_im _

theorem lmJs_pd_plane {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (j : Fin 2) (x : ℝ × ℝ) :
    LMPd j (lmJs c k g) x = ∫ y, (B0579.pd j (lmRho c k) (x - y) : ℂ) * lmExt c g y := by
  have hd := lmJs_contDiff hc k hg
  rw [lmPd_eq_fderiv ((hd.differentiable (by simp)) x), lmJs_eq_convolution hc k g]
  have hloc := lmExt_locallyIntegrable hc hg
  have hcs := lmRho_hasCompactSupport c k
  have hC1 : ContDiff ℝ 1 (lmRho c k) := (lmRho_contDiff c k).of_le (by simp)
  have hder := hcs.hasFDerivAt_convolution_left (𝕜 := ℝ) (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := volume) hC1 hloc x
  rw [hder.fderiv, convolution_eq_swap]
  have hexists := (hcs.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).precompL (ℝ × ℝ))
    (hC1.continuous_fderiv (by simp)) hloc x
  rw [ContinuousLinearMap.integral_apply hexists.integrable_swap]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp [B0579.pd, ContinuousLinearMap.precompL]

theorem lmRho_pd_eq_zero {c : ℝ} (hc : 0 < c) (k : ℕ) (j : Fin 2) (z : ℝ × ℝ)
    (hz : c / 3 ≤ |z.1|) : B0579.pd j (lmRho c k) z = 0 := by
  have hopen : IsOpen {w : ℝ × ℝ | c / 4 < |w.1|} := isOpen_lt continuous_const continuous_fst.abs
  have hev : lmRho c k =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds (show z ∈ {w : ℝ × ℝ | c / 4 < |w.1|} by
      show c / 4 < |z.1|
      linarith)] with w hw
    exact lmRho_eq_zero hc k (Or.inl (le_of_lt hw))
  unfold B0579.pd
  rw [hev.fderiv_eq]
  simp

theorem lmJs_pd_cell {c : ℝ} (hc : 0 < c) (k : ℕ) (g : ℝ × ℝ → ℂ) (j : Fin 2) (x : ℝ × ℝ) :
    ∫ y, (B0579.pd j (lmRho c k) (x - y) : ℂ) * lmExt c g y =
      ∫ y in B0579.cell c, (B0579.pd j (lmK c k) (x - y) : ℂ) * g y := by
  have h := lm_cell_unfold hc (h := B0579.pd j (lmRho c k))
    (fun z hz => lmRho_pd_eq_zero hc k j z hz) (lmExt_periodic hc g) x
  rw [← h]
  refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun y hy => ?_
  simp only [lmK_pd hc k j, lmExt_of_mem hc g hy]

theorem lmJs_pd {c : ℝ} (hc : 0 < c) (k : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (B0579.cell c))) (j : Fin 2) (x : ℝ × ℝ) :
    LMPd j (lmJs c k g) x =
      -∫ y in B0579.cell c, g y * (B0579.pd j (fun y => lmK c k (x - y)) y : ℂ) := by
  rw [lmJs_pd_plane hc k hg j x, lmJs_pd_cell hc k g j x, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [(lmK_test hc k x).2 j y]
  push_cast
  ring

theorem lmJs_commute {c : ℝ} (hc : 0 < c) (k : ℕ) {g h : ℝ × ℝ → ℂ} (j : Fin 2)
    (hgh : LMWeakPd c j g h) (x : ℝ × ℝ) : LMPd j (lmJs c k g) x = lmJs c k h x := by
  obtain ⟨hg, -, hw⟩ := hgh
  have ht := (lmK_test hc k x).1
  rw [lmJs_pd hc k hg j x, hw _ ht.smooth ht.periodic ht.band, neg_neg]
  unfold lmJs
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  exact mul_comm _ _

end UnforcedLeray.Short.IIIa
