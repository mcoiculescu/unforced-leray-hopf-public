import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.FlowMeas

/-!
# Helper for `PartIII-a:T21/c3/2/1/2/3/1`: continuity of the frame amplitudes and vectors

Source: `the November 2 reference manuscript` lines 2891-2897 and 2914-2925.

On a block `[t, s]` with `1 ≤ b ≤ θ(s)` (so every cell length `d(r) = c/√a(r)` is `≥ 1`):

* `det_perGram_ne_zero`: the Gram matrix is invertible at every frame age (the dual relation
  `Λ E = I₂` of `PerFrameFacts` fails for the zero inverse);
* `continuousOn_ampl_age`: the amplitudes `α_i(r) = Λ_i W(z(r))` are continuous on `[t, s]` (the
  argument of `FlowMeas.continuousOn_ampl`, with the Gram inverse controlled by continuity and
  compactness instead of the near-identity condition);
* `eFun`, `tendsto_xNorm_eFun`: the rescaled vectors `x ↦ a⁻² E_i(x/√a)` on the fixed cell are
  continuous in `X_{m,c}` (dominated convergence, Gaussian tails of `E_i`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa.ComplMildYAux

open FlowMeas

/-- On the frame ages the cell length is at least one. -/
theorem cellLen_one_le_of_theta {ν r b : ℝ} (hν : 0 < ν) (hr : 0 ≤ r) (hb : 1 ≤ b)
    (hbr : b ≤ clockTheta ν r) : 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r) := by
  have ha : 1 ≤ clockA ν r := one_le_clockA hν.le hr
  have hpos : 0 < ν * clockA ν r := mul_pos hν (by linarith)
  have h1 : 1 ≤ (ν * clockA ν r)⁻¹ := hb.trans hbr
  have hνa : ν * clockA ν r ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h1 hpos.le
    rwa [mul_one, mul_inv_cancel₀ hpos.ne'] at this
  have hν1 : ν ≤ 1 := by nlinarith
  have hsa : 0 < Real.sqrt (clockA ν r) := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (clockA ν r) ≤ clockA ν r := by
    calc Real.sqrt (clockA ν r) ≤ Real.sqrt (clockA ν r ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = clockA ν r := Real.sqrt_sq (by linarith)
  have hAν : clockA ν r ≤ (ν ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]
    have : clockA ν r * ν ^ 2 = (ν * clockA ν r) * ν := by ring
    rw [this]
    calc ν * clockA ν r * ν ≤ 1 * 1 := mul_le_mul hνa hν1 hν.le zero_le_one
      _ = 1 := by ring
  unfold cellLen
  rw [le_div_iff₀ hsa, one_mul, Real.rpow_neg hν.le, Real.rpow_two]
  exact hsq.trans hAν

/-- The Gram matrix is invertible at the frame ages: otherwise `Λ = 0` contradicts `Λ E = I₂`. -/
theorem det_perGram_ne_zero (κ : PlanarFrameKernels) {ν m b K r : ℝ}
    (hF : PerFrameFacts κ ν m b K) (hr : 0 ≤ r) (hbr : b ≤ clockTheta ν r) :
    (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0 := by
  intro h0
  have hinv : (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ = 0 :=
    Matrix.nonsing_inv_apply_not_isUnit _ (by rw [h0]; exact not_isUnit_zero)
  have h := hF.1 r hr hbr 0 0
  simp only [perLam, hinv, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    integral_zero] at h
  simp at h

/-- Continuity of the Gram inverse along the frame ages. -/
theorem continuousOn_perGram_inv_age (κ : PlanarFrameKernels) {ν m b K t s : ℝ}
    (hν : 0 < ν) (ht : 0 ≤ t) (hbs : b ≤ clockTheta ν s) (hF : PerFrameFacts κ ν m b K)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (i j : Fin 2) :
    ContinuousOn (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i j)
      (Icc t s) := by
  have hd_cont : ContinuousOn (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t s) :=
    continuousOn_cellLen_clockA hν ht _ fun _ hr => hr.1
  have hmaps : MapsTo (fun r => cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (Icc t s) (Ici 1) :=
    fun r hr => hd1 r hr
  have hG : ∀ a c : Fin 2, ContinuousOn
      (fun r => perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) a c) (Icc t s) :=
    fun a c => (continuousOn_perGram κ a c).comp hd_cont hmaps
  have hdet : ContinuousOn (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det)
      (Icc t s) := by
    have heq : (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det) = fun r =>
        perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 0 0 *
            perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 1 1 -
          perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 0 1 *
            perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 1 0 := by
      funext r; exact Matrix.det_fin_two _
    rw [heq]
    exact ((hG 0 0).mul (hG 1 1)).sub ((hG 0 1).mul (hG 1 0))
  have hdet_ne : ∀ r ∈ Icc t s,
      (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det ≠ 0 := by
    intro r hr
    have hr0 : 0 ≤ r := ht.trans hr.1
    exact det_perGram_ne_zero κ hF hr0 (hbs.trans (theta_anti hν hr0 hr.2))
  have hdet_inv := hdet.inv₀ hdet_ne
  fin_cases i <;> fin_cases j
  · have hentry : (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ 0 0) =
        fun r => ((perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det)⁻¹ *
          perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 1 1 := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    change ContinuousOn (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ 0 0) _
    rw [hentry]; exact hdet_inv.mul (hG 1 1)
  · have hentry : (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ 0 1) =
        fun r => ((perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det)⁻¹ *
          (-perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 0 1) := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    change ContinuousOn (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ 0 1) _
    rw [hentry]; exact hdet_inv.mul (hG 0 1).neg
  · have hentry : (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ 1 0) =
        fun r => ((perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det)⁻¹ *
          (-perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 1 0) := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    change ContinuousOn (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ 1 0) _
    rw [hentry]; exact hdet_inv.mul (hG 1 0).neg
  · have hentry : (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ 1 1) =
        fun r => ((perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r))).det)⁻¹ *
          perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) 0 0 := by
      funext r; rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]; rfl
    change ContinuousOn (fun r => (perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ 1 1) _
    rw [hentry]; exact hdet_inv.mul (hG 0 0)

/-- The pulled-back dual rows are bounded on the fixed cell, uniformly on the block. -/
theorem physLam_bound (κ : PlanarFrameKernels) {ν m b K t s : ℝ}
    (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s) (hbs : b ≤ clockTheta ν s)
    (hF : PerFrameFacts κ ν m b K)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (i : Fin 2) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ r ∈ Icc t s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ‖physAdj (clockA ν r) (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) x‖ ≤ Bd := by
  obtain ⟨B₀, hB₀, hsup⟩ := Lam0B.perLam0_sup κ
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_perGram_inv_age κ hν ht hbs hF hd1 i 0)
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_perGram_inv_age κ hν ht hbs hF hd1 i 1)
  set Cg : ℝ := max (max C0 C1) 0 with hCg
  have hCg0 : 0 ≤ Cg := le_max_right _ _
  have hAs1 : 1 ≤ clockA ν s := one_le_clockA hν.le (ht.trans hts)
  have hBd0 : 0 ≤ 2 * Cg * B₀ := mul_nonneg (mul_nonneg (by norm_num) hCg0) hB₀
  refine ⟨clockA ν s * (2 * Cg * B₀), mul_nonneg (by linarith) hBd0, fun r hr x hx => ?_⟩
  have hg0 : ‖(perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i 0‖ ≤ Cg :=
    (hC0 r hr).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hg1 : ‖(perGram κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)))⁻¹ i 1‖ ≤ Cg :=
    (hC1 r hr).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hAr : clockA ν r ≤ clockA ν s := clockA_mono hν.le hr.2
  set a := clockA ν r with ha_def
  set d := cellLen (ν ^ (-2 : ℝ)) a with hd_def
  have ha : 1 ≤ a := one_le_clockA hν.le (ht.trans hr.1)
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
  have hsum : ‖(perGram κ d)⁻¹ i 0 * perLam0 κ d 0 (x.1 / Real.sqrt a, x.2 / Real.sqrt a) +
      (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 (x.1 / Real.sqrt a, x.2 / Real.sqrt a)‖ ≤
        2 * Cg * B₀ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    nlinarith [mul_le_mul hg0 h0 (norm_nonneg _) hCg0, mul_le_mul hg1 h1 (norm_nonneg _) hCg0]
  unfold physAdj perLam
  rw [norm_mul, Complex.norm_of_nonneg (by linarith), Fin.sum_univ_two]
  calc a * ‖(perGram κ d)⁻¹ i 0 * perLam0 κ d 0 (x.1 / Real.sqrt a, x.2 / Real.sqrt a) +
        (perGram κ d)⁻¹ i 1 * perLam0 κ d 1 (x.1 / Real.sqrt a, x.2 / Real.sqrt a)‖
      ≤ a * (2 * Cg * B₀) := mul_le_mul_of_nonneg_left hsum (by linarith)
    _ ≤ clockA ν s * (2 * Cg * B₀) := mul_le_mul_of_nonneg_right hAr hBd0

/-- Pointwise continuity of the pulled-back dual rows along the block. -/
theorem continuousOn_physLam (κ : PlanarFrameKernels) {ν m b K t s : ℝ}
    (hν : 0 < ν) (ht : 0 ≤ t) (hbs : b ≤ clockTheta ν s) (hF : PerFrameFacts κ ν m b K)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (i : Fin 2) (x : ℝ × ℝ) :
    ContinuousOn
      (fun r => physAdj (clockA ν r) (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) x)
      (Icc t s) := by
  obtain ⟨C, hC0, hC⟩ := Lam0B.lamP_translate_bound κ
  have ha_cont : ContinuousOn (fun r => ((clockA ν r : ℝ) : ℂ)) (Icc t s) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_clockA _)
  unfold physAdj perLam
  refine ha_cont.mul (continuousOn_finsetSum Finset.univ fun j _ => ?_)
  have hLam0 : ContinuousOn
      (fun r => perLam0 κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) j
        (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r)))
      (Icc t s) :=
    continuousOn_perSum_scaled (κ.lamP_cont j) hC0 (hC j) hν ht hd1 x
  exact (continuousOn_perGram_inv_age κ hν ht hbs hF hd1 i j).mul hLam0

/-- **Continuity of the amplitudes** `α_i(r) = Λ_i W(z(r))` on the block (SP 2891-2897,
2914-2925), for every frame obeying `PerFrameFacts` (no smallness of `ν` beyond `1 ≤ b ≤ θ`). -/
theorem continuousOn_ampl_age (κ : PlanarFrameKernels) {ν m b K t s : ℝ}
    (hm : 8 < m) (hν : 0 < ν) (ht : 0 ≤ t) (hts : t ≤ s)
    (hbs : b ≤ clockTheta ν s) (hF : PerFrameFacts κ ν m b K)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    {tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))}
    {f : ℝ × ℝ → ℂ} {w : ℝ → ℝ × ℝ → ℂ} {u : ℝ → ℝ × ℝ → Fin 2 → ℂ}
    (hw : IsLinearisedFlow ν (ν ^ (-2 : ℝ)) m tr t f w u) (i : Fin 2) :
    ContinuousOn (fun r => ampl (periodizedFrame κ ν m b K hν hF) w r i) (Icc t s) := by
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  set Φ : ℝ → ℝ × ℝ → ℂ := fun r x =>
    physAdj (clockA ν r) (perLam κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i) x
  obtain ⟨Bd, hBd0, hBd⟩ := physLam_bound κ hν ht hts hbs hF hd1 i
  have hΦ_bdd : ∀ r ∈ Icc t s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)), ‖Φ r x‖ ≤ Bd := hBd
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
    refine (hw_int.norm.const_mul Bd).mono'
      (hw_int.aestronglyMeasurable.mul (hΦ_cont_x r₂ hr₂).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x hx
    rw [norm_mul]
    calc ‖w r₁ x‖ * ‖Φ r₂ x‖ ≤ ‖w r₁ x‖ * Bd :=
          mul_le_mul_of_nonneg_left (hΦ_bdd r₂ hr₂ x hx) (norm_nonneg _)
      _ = Bd * ‖w r₁ x‖ := mul_comm _ _
  have hampl_eq : ∀ r ∈ Icc t s,
      ampl (periodizedFrame κ ν m b K hν hF) w r i =
        ∫ x in B0579.cell (ν ^ (-2 : ℝ)), w r x * Φ r x := by
    intro r hr
    have ha : 0 < clockA ν r :=
      lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hr.1))
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
      (fun x => Bd * ‖w r x‖) ?_ ?_ (hw_int.norm.const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin] with r' hr'
      exact (hprod_int r hr r' hr').aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with r' hr'
      filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x hx
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hΦ_bdd r' hr' x hx) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x _hx
      exact tendsto_const_nhds.mul (continuousOn_physLam κ hν ht hbs hF hd1 i x r hr)
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

end UnforcedLeray.Short.IIIa.ComplMildYAux
