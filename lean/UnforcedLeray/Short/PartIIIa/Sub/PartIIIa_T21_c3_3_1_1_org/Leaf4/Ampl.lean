import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.FlowMeas

/-!
# Leaf (d) of `PartIII-a:T21/c3/3/1/1`, part 1: continuity of the amplitudes without the large-`d` hypothesis

Variant of `FlowMeas.continuousOn_ampl` (SP 2991-2997) whose hypotheses are only `1 ≤ d(r)` and
invertibility of the Gram matrix along the path (instead of the near-identity bound for `d ≥ D₁`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

namespace FlowMeas

lemma continuousOn_perGram_inv' (κ : PlanarFrameKernels) {S : Set ℝ} (hS : S ⊆ Ici 1)
    (hdetne : ∀ d ∈ S, (perGram κ d).det ≠ 0) (i j : Fin 2) :
    ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ i j) (S) := by
  have hsub : S ⊆ Ici 1 := hS
  have hG : ∀ a b : Fin 2, ContinuousOn (fun d : ℝ => perGram κ d a b) (S) :=
    fun a b => (continuousOn_perGram κ a b).mono hsub
  have hdet : ContinuousOn (fun d : ℝ => (perGram κ d).det) (S) := by
    have heq : (fun d : ℝ => (perGram κ d).det) =
        fun d => perGram κ d 0 0 * perGram κ d 1 1 - perGram κ d 0 1 * perGram κ d 1 0 := by
      funext d; exact Matrix.det_fin_two (perGram κ d)
    rw [heq]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hdet_ne := hdetne
  have hdet_inv : ContinuousOn (fun d : ℝ => ((perGram κ d).det)⁻¹) (S) :=
    hdet.inv₀ hdet_ne
  fin_cases i <;> fin_cases j
  · change ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ 0 0) (S)
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 0 0) =
        fun d => ((perGram κ d).det)⁻¹ * perGram κ d 1 1 := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG 1 1)
  · change ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ 0 1) (S)
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 0 1) =
        fun d => ((perGram κ d).det)⁻¹ * (-perGram κ d 0 1) := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG 0 1).neg
  · change ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ 1 0) (S)
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 1 0) =
        fun d => ((perGram κ d).det)⁻¹ * (-perGram κ d 1 0) := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG 1 0).neg
  · change ContinuousOn (fun d : ℝ => (perGram κ d)⁻¹ 1 1) (S)
    have hentry : (fun d : ℝ => (perGram κ d)⁻¹ 1 1) =
        fun d => ((perGram κ d).det)⁻¹ * perGram κ d 0 0 := by
      funext d; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    rw [hentry]; exact hdet_inv.mul (hG 0 0)

/-! ## Pointwise continuity of `perSum (d r) f (x / √(a r))` on `Icc t s` -/
lemma continuousOn_physFrameLam' (κ : PlanarFrameKernels) {ν t s : ℝ}
    (hν : 0 < ν) (ht : 0 ≤ t)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t s, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    (i : Fin 2) (x : ℝ × ℝ) :
    ContinuousOn
      (fun r => physAdj (clockA ν r)
        (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) x)
      (Icc t s) := by
  obtain ⟨C, hC0, hC⟩ := Lam0B.lamP_translate_bound κ
  have hmaps : MapsTo (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t s)
      {d : ℝ | 1 ≤ d ∧ (perGram κ d).det ≠ 0} := fun r hr => ⟨hd1 r hr, hdet r hr⟩
  have ha_cont : ContinuousOn (fun r => ((clockA ν r : ℝ) : ℂ)) (Icc t s) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_clockA _)
  have hd_cont : ContinuousOn (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t s) :=
    continuousOn_cellLen_clockA hν ht _ fun _ hr => hr.1
  unfold physAdj perLam
  refine ha_cont.mul (continuousOn_finsetSum Finset.univ fun j _ => ?_)
  have hGinv : ContinuousOn (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i j)
      (Icc t s) :=
    (continuousOn_perGram_inv' κ (S := {d : ℝ | 1 ≤ d ∧ (perGram κ d).det ≠ 0})
      (fun d hd => hd.1) (fun d hd => hd.2) i j).comp hd_cont hmaps
  have hLam0 : ContinuousOn
      (fun r => perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j
        (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r)))
      (Icc t s) :=
    continuousOn_perSum_scaled (κ.lamP_cont j) hC0 (hC j) hν ht hd1 x
  exact hGinv.mul hLam0

/-! ## Bounds and continuity of `ampl` and `amplNorm` on `Icc t s` -/

lemma physFrameLam_bdd' (κ : PlanarFrameKernels) {ν t s : ℝ}
    (hν : 0 < ν) (ht : 0 ≤ t)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t s, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    (i : Fin 2) :
    ∃ B : ℝ, ∀ r ∈ Icc t s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ‖physAdj (clockA ν r) (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) x‖ ≤ B := by
  obtain ⟨B₀, hB₀, hsup⟩ := Lam0B.perLam0_sup κ
  have hd_cont : ContinuousOn (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t s) :=
    continuousOn_cellLen_clockA hν ht _ fun _ hr => hr.1
  have hmaps : MapsTo (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t s)
      {d : ℝ | 1 ≤ d ∧ (perGram κ d).det ≠ 0} := fun r hr => ⟨hd1 r hr, hdet r hr⟩
  have hG : ∀ j : Fin 2, ContinuousOn
      (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i j) (Icc t s) := fun j =>
    (continuousOn_perGram_inv' κ (S := {d : ℝ | 1 ≤ d ∧ (perGram κ d).det ≠ 0})
      (fun d hd => hd.1) (fun d hd => hd.2) i j).comp hd_cont hmaps
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hG 0)
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn (hG 1)
  refine ⟨clockA ν s * ((|M0| + |M1|) * B₀), fun r hr x hx => ?_⟩
  set a := clockA ν r
  set d := cellLen (ν ^ (-2 : ℝ)) a
  have ha : 1 ≤ a := one_le_clockA hν.le (ht.trans hr.1)
  have has : a ≤ clockA ν s := clockA_mono hν.le hr.2
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 (by linarith)
  have hd1' : 1 ≤ d := hd1 r hr
  have hy : (x.1 / Real.sqrt a, x.2 / Real.sqrt a) ∈ B0579.cell d := by
    have hsmul : Real.sqrt a • (x.1 / Real.sqrt a, x.2 / Real.sqrt a) ∈
        B0579.cell (d * Real.sqrt a) := by
      have heq1 : Real.sqrt a • (x.1 / Real.sqrt a, x.2 / Real.sqrt a) = x := by
        ext <;> simp [smul_eq_mul, mul_div_cancel₀ _ hsa.ne']
      have heq2 : d * Real.sqrt a = ν ^ (-2 : ℝ) := by
        simp only [d, cellLen, div_mul_cancel₀ _ hsa.ne']
      rwa [heq1, heq2]
    exact (T07.smul_mem_cell_iff d (Real.sqrt a) hsa _).1 hsmul
  have h0 := hsup d hd1' 0 _ hy
  have h1 := hsup d hd1' 1 _ hy
  have g0 := hM0 r hr
  have g1 := hM1 r hr
  unfold physAdj perLam
  rw [norm_mul, Complex.norm_of_nonneg (by linarith), Fin.sum_univ_two]
  have hsum : ‖(perGram κ d)⁻¹ i 0 * perLam0 κ d 0 (x.1 / Real.sqrt a, x.2 / Real.sqrt a) +
      (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 (x.1 / Real.sqrt a, x.2 / Real.sqrt a)‖ ≤
      (|M0| + |M1|) * B₀ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have e0 : ‖(perGram κ d)⁻¹ i 0‖ ≤ |M0| := g0.trans (le_abs_self _)
    have e1 : ‖(perGram κ d)⁻¹ i 1‖ ≤ |M1| := g1.trans (le_abs_self _)
    nlinarith [norm_nonneg ((perGram κ d)⁻¹ i 0), norm_nonneg ((perGram κ d)⁻¹ i 1),
      norm_nonneg (perLam0 κ d 0 (x.1 / Real.sqrt a, x.2 / Real.sqrt a)),
      norm_nonneg (perLam0 κ d 1 (x.1 / Real.sqrt a, x.2 / Real.sqrt a)),
      mul_le_mul e0 h0 (norm_nonneg _) (abs_nonneg _),
      mul_le_mul e1 h1 (norm_nonneg _) (abs_nonneg _)]
  calc a * ‖_‖ ≤ a * ((|M0| + |M1|) * B₀) := mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ clockA ν s * ((|M0| + |M1|) * B₀) :=
        mul_le_mul_of_nonneg_right has (by positivity)

lemma continuousOn_ampl' (κ : PlanarFrameKernels) {ν m b K t s : ℝ}
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s)
    (hbs : b ≤ clockTheta ν s) (hF : PerFrameFacts κ ν m b K)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (hdet : ∀ r ∈ Icc t s, (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0)
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (i : Fin 2) :
    ContinuousOn (fun r => ampl (periodizedFrame κ ν m b K hν hF) w r i) (Icc t s) := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  set Φ : ℝ → ℝ × ℝ → ℂ := fun r x =>
    physAdj (clockA ν r) (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) x
  obtain ⟨B, hΦ_bdd⟩ := physFrameLam_bdd' κ hν ht hd1 hdet i
  have hΦ_cont_x : ∀ r ∈ Icc t s, Continuous (Φ r) := by
    intro r hr
    have hd_pos : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r) :=
      lt_of_lt_of_le zero_lt_one (hd1 r hr)
    unfold Φ physAdj
    exact continuous_const.mul ((FrameCont.perLam_continuous κ hd_pos i).comp
      ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))
  have hprod_int : ∀ r₁ ∈ Icc t s, ∀ r₂ ∈ Icc t s,
      IntegrableOn (fun x => w r₁ x * Φ r₂ x) (B0579.cell (ν ^ (-2 : ℝ))) := by
    intro r₁ hr₁ r₂ hr₂
    have hw_int := integrableOn_of_memLp_cellMeasure hm (hw.memX r₁ hr₁.1)
    refine (hw_int.norm.const_mul (B)).mono'
      (hw_int.aestronglyMeasurable.mul (hΦ_cont_x r₂ hr₂).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x hx
    rw [norm_mul]
    calc ‖w r₁ x‖ * ‖Φ r₂ x‖ ≤ ‖w r₁ x‖ * (B) :=
          mul_le_mul_of_nonneg_left (hΦ_bdd r₂ hr₂ x hx) (norm_nonneg _)
      _ = B * ‖w r₁ x‖ := mul_comm _ _
  have hampl_eq : ∀ r ∈ Icc t s,
      ampl (periodizedFrame κ ν m b K hν hF) w r i =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * Φ r x := by
    intro r hr
    have ha : 0 < clockA ν r := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hr.1))
    have hco := pairingCoV (ν ^ (-2 : ℝ)) (clockA ν r) hc ha (w r)
      (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i)
    simpa only [ampl, periodizedFrame, movingW, movingCell, Φ, mul_comm] using hco
  intro r hr
  rw [ContinuousWithinAt]
  have h1 : Tendsto (fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w r' x - w r x) * Φ r' x)
      (𝓝[Icc t s] r) (𝓝 0) := by
    set C_s : ℝ := max K 0 * (clockA ν s) ^ ((3 : ℝ) / 2)
    have hAs0 : 0 ≤ clockA ν s := le_trans zero_le_one (one_le_clockA hν.le (ht.trans hts))
    have hC_s0 : 0 ≤ C_s := by positivity
    have hdiff_le : ∀ r' ∈ Icc t s,
        ‖∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w r' x - w r x) * Φ r' x‖ ≤
          C_s * (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal := by
      intro r' hr'
      have hr'0 : 0 ≤ r' := ht.trans hr'.1
      have ha' : 1 ≤ clockA ν r' := one_le_clockA hν.le hr'0
      have hbr' : b ≤ clockTheta ν r' := hbs.trans (theta_anti hν hr'0 hr'.2)
      have hco := pairingCoV (ν ^ (-2 : ℝ)) (clockA ν r') hc (by linarith) (w r' - w r)
        (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i)
      have heq : (∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w r' x - w r x) * Φ r' x) =
          ∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i y *
              JscaleInv (clockA ν r') (w r' - w r) y := by
        simpa only [Φ, Pi.sub_apply, mul_comm] using hco.symm
      rw [heq]
      have hmem_sub : MemLp (w r' - w r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) :=
        (hw.memX r' hr'.1).sub (hw.memX r hr.1)
      have hfin : xNorm (ν ^ (-2 : ℝ)) m (w r' - w r) ≠ ⊤ := hmem_sub.2.ne
      have hbd1 : ENNReal.ofReal ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i y *
              JscaleInv (clockA ν r') (w r' - w r) y‖ ≤
          ENNReal.ofReal K * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) m
            (JscaleInv (clockA ν r') (w r' - w r)) :=
        hF.2.2 r' hr'0 hbr' i (JscaleInv (clockA ν r') (w r' - w r))
      have hbd2 := xNorm_JscaleInv_le (ν ^ (-2 : ℝ)) m (clockA ν r') (by linarith) ha'
        (w r' - w r) hmem_sub
      have hA_le : (clockA ν r') ^ ((3 : ℝ) / 2) ≤ (clockA ν s) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by linarith) (clockA_mono hν.le hr'.2) (by norm_num)
      have hcomb : ENNReal.ofReal ‖∫ y in B0579.cell (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')),
            perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) i y *
              JscaleInv (clockA ν r') (w r' - w r) y‖ ≤
          ENNReal.ofReal (C_s * (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal) := by
        calc _ ≤ ENNReal.ofReal K * xNorm (cellLen (ν ^ (-2 : ℝ)) (clockA ν r')) m
                (JscaleInv (clockA ν r') (w r' - w r)) := hbd1
          _ ≤ ENNReal.ofReal (max K 0) * (ENNReal.ofReal ((clockA ν s) ^ ((3 : ℝ) / 2)) *
                xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)) := by
              gcongr
              · exact le_max_left K 0
              · exact hbd2.trans (by gcongr)
          _ = ENNReal.ofReal C_s *
                ENNReal.ofReal (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (le_max_right K 0),
                ENNReal.ofReal_toReal hfin]
          _ = ENNReal.ofReal (C_s * (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal) :=
              (ENNReal.ofReal_mul hC_s0).symm
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC_s0 ENNReal.toReal_nonneg)).1 hcomb
    have hsc := (hw.strongCont r hr.1).mono_left
      (nhdsWithin_mono r fun r' (hr' : r' ∈ Icc t s) => (hr'.1 : r' ∈ Ici t))
    have htoR : Tendsto (fun r' => (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal)
        (𝓝[Icc t s] r) (𝓝 0) := by
      have := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hsc
      simpa only [Function.comp_def, ENNReal.toReal_zero] using this
    have hmul : Tendsto (fun r' => C_s * (xNorm (ν ^ (-2 : ℝ)) m (w r' - w r)).toReal)
        (𝓝[Icc t s] r) (𝓝 0) := by
      simpa using htoR.const_mul C_s
    exact squeeze_zero_norm' (eventually_nhdsWithin_of_forall hdiff_le) hmul
  have h2 : Tendsto (fun r' => ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * Φ r' x)
      (𝓝[Icc t s] r) (𝓝 (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * Φ r x)) := by
    have hw_int := integrableOn_of_memLp_cellMeasure hm (hw.memX r hr.1)
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => (B) * ‖w r x‖) ?_ ?_ (hw_int.norm.const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with r' hr'
      exact (hprod_int r hr r' hr').aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r' hr'
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x hx
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hΦ_bdd r' hr' x hx) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x _hx
      exact tendsto_const_nhds.mul (continuousOn_physFrameLam' κ hν ht hd1 hdet i x r hr)
  have hsum := h1.add h2
  rw [zero_add, ← hampl_eq r hr] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r' hr'
  have hsub : (∫ x in B0579.cell (ν ^ (-2 : ℝ)), (w r' x - w r x) * Φ r' x) =
      (∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r' x * Φ r' x) -
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * Φ r' x := by
    simp_rw [sub_mul]
    exact integral_sub (hprod_int r' hr' r' hr') (hprod_int r hr r' hr')
  rw [hsub, sub_add_cancel, hampl_eq r' hr']


end FlowMeas

end UnforcedLeray.Short.IIIa
