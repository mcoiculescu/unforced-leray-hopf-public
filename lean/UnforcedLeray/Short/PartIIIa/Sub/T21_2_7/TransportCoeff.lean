import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.AdjWeakDefs

/-!
# Part III-a, `PartIII-a:T21/2/7/1/6`: the transport coefficient of the adjoint problem

Proves `AdjTransportCoeff m` (`Sub/T21_2_7/AdjWeakDefs.lean`): multiplication by `-v_j(r)` on
`X_{-m,c} = L²(C_c, ⟨x⟩^{-2m} dx)`, `c = ν^{-2}`, for a train with the bounds `LadTrainBdd`.
Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
(`B(t)` bounded: the train velocity is bounded).

Route. On `[0, T]` the velocity is bounded on the cell (`LadTrainBdd`), so multiplication by
`-v_j(r)` is a bounded operator on `L²(μ)`, `μ = cellMeasure c (-m)`, of norm `≤ C`. The age
`r` is clamped to `[0, T]` (`clampT`) so that every `r` has a definition. Strong continuity is
dominated convergence in `L²(μ)`, using the pointwise continuity of `r ↦ v_j(r, x)` on `[0, ∞)`
from `tr.isTrain.smooth_v`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Multiplication by a bounded function on `L²(μ)` -/

section Mult

variable {μ : Measure (ℝ × ℝ)}

theorem mulBdd_memLp (G : ℝ × ℝ → ℂ) (hG : AEStronglyMeasurable G μ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ᵐ x ∂μ, ‖G x‖ ≤ K) (w : Lp ℂ 2 μ) :
    MemLp (fun x => G x * w x) 2 μ :=
  MemLp.of_le_mul (c := K) (Lp.memLp w) (hG.mul (Lp.aestronglyMeasurable w)) (by
    filter_upwards [hK] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- Multiplication by a bounded function, as a linear map on `L²(μ)`. -/
def mulBddLin (G : ℝ × ℝ → ℂ) (hG : AEStronglyMeasurable G μ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ᵐ x ∂μ, ‖G x‖ ≤ K) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun w := (mulBdd_memLp G hG hK0 hK w).toLp _
  map_add' w₁ w₂ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (mulBdd_memLp G hG hK0 hK (w₁ + w₂)),
      Lp.coeFn_add ((mulBdd_memLp G hG hK0 hK w₁).toLp _) ((mulBdd_memLp G hG hK0 hK w₂).toLp _),
      MemLp.coeFn_toLp (mulBdd_memLp G hG hK0 hK w₁),
      MemLp.coeFn_toLp (mulBdd_memLp G hG hK0 hK w₂),
      Lp.coeFn_add w₁ w₂] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h2 h5 ⊢
    rw [h2, h1, h3, h4, h5]
    ring
  map_smul' c w := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (mulBdd_memLp G hG hK0 hK (c • w)),
      Lp.coeFn_smul c ((mulBdd_memLp G hG hK0 hK w).toLp _),
      MemLp.coeFn_toLp (mulBdd_memLp G hG hK0 hK w),
      Lp.coeFn_smul c w] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul] at h2 h4 ⊢
    rw [h2, h3, h1, h4]
    ring

/-- Multiplication by a bounded function, as a continuous linear map on `L²(μ)`, of norm `≤ K`. -/
def mulBddCLM (G : ℝ × ℝ → ℂ) (hG : AEStronglyMeasurable G μ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ᵐ x ∂μ, ‖G x‖ ≤ K) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous (mulBddLin G hG hK0 hK) K (fun w => by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [MemLp.coeFn_toLp (mulBdd_memLp G hG hK0 hK w), hK] with x hx hGx
    show ‖(mulBdd_memLp G hG hK0 hK w).toLp _ x‖ ≤ K * ‖w x‖
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right hGx (norm_nonneg _))

theorem mulBddCLM_apply_ae (G : ℝ × ℝ → ℂ) (hG : AEStronglyMeasurable G μ) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ᵐ x ∂μ, ‖G x‖ ≤ K) (w : Lp ℂ 2 μ) :
    ⇑(mulBddCLM G hG hK0 hK w) =ᵐ[μ] fun x => G x * w x :=
  MemLp.coeFn_toLp (mulBdd_memLp G hG hK0 hK w)

theorem norm_mulBddCLM_le (G : ℝ × ℝ → ℂ) (hG : AEStronglyMeasurable G μ) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ᵐ x ∂μ, ‖G x‖ ≤ K) :
    ‖mulBddCLM G hG hK0 hK‖ ≤ K :=
  LinearMap.mkContinuous_norm_le _ hK0 _

end Mult

/-! ## Dominated convergence in `L²(μ)` (eLpNorm form) -/

theorem adjTT_enorm_le {a b : ℂ} {K : ℝ} (hK0 : 0 ≤ K) (h : ‖a‖ ≤ K * ‖b‖) :
    ‖a‖ₑ ≤ ENNReal.ofReal K * ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm a, ← ofReal_norm_eq_enorm b, ← ENNReal.ofReal_mul hK0]
  exact ENNReal.ofReal_le_ofReal h

theorem adjTT_dct {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ : Measure (ℝ × ℝ)} {F : ι → ℝ × ℝ → ℂ} {W : ℝ × ℝ → ℂ} {K : ℝ} (hK0 : 0 ≤ K)
    (hF : ∀ i, AEMeasurable (F i) μ) (hW : MemLp W 2 μ)
    (hb : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ K * ‖W x‖)
    (hlim : ∀ x, Tendsto (fun i => F i x) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (F i) 2 μ) l (𝓝 0) := by
  have hWfin : ∫⁻ x, ‖W x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ :=
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).1 hW.2
  have hfin : ∫⁻ x, (ENNReal.ofReal K * ‖W x‖ₑ) ^ (2 : ℝ) ∂μ ≠ ⊤ := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top)]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      ENNReal.ofReal_ne_top) hWfin.ne
  have hI : Tendsto (fun i => ∫⁻ x, ‖F i x‖ₑ ^ (2 : ℝ) ∂μ) l (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := l)
      (F := fun i x => ‖F i x‖ₑ ^ (2 : ℝ)) (f := fun _ => (0 : ℝ≥0∞))
      (fun x => (ENNReal.ofReal K * ‖W x‖ₑ) ^ (2 : ℝ))
      (Eventually.of_forall fun i => ((hF i).enorm).pow_const (2 : ℝ))
      (Eventually.of_forall fun i => (hb i).mono fun x hx =>
        ENNReal.rpow_le_rpow (adjTT_enorm_le hK0 hx) (by norm_num))
      hfin
      (ae_of_all _ fun x => by
        have h1 : Tendsto (fun i => ‖F i x‖ₑ) l (𝓝 0) := by
          have h0 := (continuous_enorm.tendsto (0 : ℂ)).comp (hlim x)
          simpa [Function.comp_def] using h0
        have h2 := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h1
        have h3 : (0 : ℝ≥0∞) ^ (2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
        simpa [Function.comp_def, h3] using h2)
    simpa using this
  have hEq : ∀ i, eLpNorm (F i) 2 μ = (∫⁻ x, ‖F i x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := fun i => by
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    norm_num
  simp only [hEq]
  have h4 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hI
  have h5 : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  simpa [Function.comp_def, h5] using h4

/-! ## The clamped train velocity -/

/-- Clamp of the age to `[0, T]`. -/
def clampT (T r : ℝ) : ℝ := max 0 (min r T)

theorem clampT_mem {T : ℝ} (hT : 0 ≤ T) (r : ℝ) : clampT T r ∈ Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem clampT_of_mem {T r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) : clampT T r = r := by
  unfold clampT
  rw [min_eq_left hr.2, max_eq_right hr.1]

theorem continuous_clampT (T : ℝ) : Continuous (clampT T) := by
  unfold clampT
  fun_prop

/-- The `j`-th coordinate of the train velocity, as a function of `x`, for fixed `s ≥ 0`. -/
theorem adjTT_coord_cont_x {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 ≤ s) (j : Fin 2) : Continuous fun x : ℝ × ℝ => tr.v s x j := by
  have h1 : ContinuousOn (fun x : ℝ × ℝ => tr.v s x) univ :=
    tr.isTrain.smooth_v.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => ⟨hs, mem_univ _⟩)
  have h2 : Continuous fun y : UnforcedLeray.Train.Vec => y j := by
    fun_prop
  exact h2.comp (continuousOn_univ.1 h1)

/-- The `j`-th coordinate of the train velocity, as a function of the age `s`, for fixed `x`. -/
theorem adjTT_coord_contOn_s {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (x : ℝ × ℝ)
    (j : Fin 2) : ContinuousOn (fun s : ℝ => tr.v s x j) (Ici 0) := by
  have h1 : ContinuousOn (fun s : ℝ => tr.v s x) (Ici 0) :=
    tr.isTrain.smooth_v.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ _⟩)
  have h2 : Continuous fun y : UnforcedLeray.Train.Vec => y j := by
    fun_prop
  exact h2.comp_continuousOn h1

/-- The clamped coefficient `-v_j(clamp r, x)` as a complex function of `x`. -/
def velCoordG {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (T : ℝ) (j : Fin 2) (r : ℝ) :
    ℝ × ℝ → ℂ :=
  fun x => -((tr.v (clampT T r) x j : ℝ) : ℂ)

theorem velCoordG_continuous {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {T : ℝ}
    (hT : 0 ≤ T) (j : Fin 2) (r : ℝ) : Continuous (velCoordG tr T j r) :=
  (Complex.continuous_ofReal.comp
    (adjTT_coord_cont_x tr (clampT_mem hT r).1 j)).neg

theorem velCoordG_contWithin {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {T : ℝ}
    (hT : 0 ≤ T) (j : Fin 2) (x : ℝ × ℝ) {r₀ : ℝ} (hr₀ : r₀ ∈ Icc (0 : ℝ) T) :
    ContinuousWithinAt (fun r => velCoordG tr T j r x) (Icc 0 T) r₀ := by
  have hv : ContinuousWithinAt (fun s => tr.v s x j) (Ici 0) (clampT T r₀) :=
    adjTT_coord_contOn_s tr x j _ (by rw [clampT_of_mem hr₀]; exact hr₀.1)
  have hcl : ContinuousWithinAt (clampT T) (Icc 0 T) r₀ :=
    (continuous_clampT T).continuousWithinAt
  have hmaps : MapsTo (clampT T) (Icc 0 T) (Ici 0) := fun r _ => (clampT_mem hT r).1
  have hcomp := hv.comp hcl hmaps
  exact ((Complex.continuous_ofReal.continuousWithinAt (s := univ)).comp hcomp
    (mapsTo_univ _ _)).neg

/-! ## The transport coefficient -/

theorem adjTransport_of_c {c : ℝ} (hc : 0 < c) {ν : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) (m T C : ℝ) (hT0 : 0 ≤ T)
    (hB : LadTrainBdd tr m T C) :
    ∃ Mv : ℝ → Fin 2 → AdjX c m →L[ℂ] AdjX c m,
      (∀ r ∈ Icc 0 T, ∀ j, ‖Mv r j‖ ≤ C) ∧
      (∀ j w, ContinuousOn (fun r => Mv r j w) (Icc 0 T)) ∧
      ∀ r ∈ Icc 0 T, ∀ j w, ⇑(Mv r j w) =ᵐ[B0579.cellMeasure c (-m)]
        fun x => -((tr.v r x j : ℝ) : ℂ) * w x := by
  have hC0 : 0 ≤ C := by
    have h0 : (0 : ℝ × ℝ) ∈ B0579.cell c :=
      ⟨⟨by show -(c / 2) ≤ (0 : ℝ); linarith, by show (0 : ℝ) < c / 2; linarith⟩,
        mem_univ _⟩
    exact (abs_nonneg _).trans ((hB 0 ⟨le_refl 0, hT0⟩ 0 h0).1 0)
  have hcell_ae : ∀ P : ℝ × ℝ → Prop, (∀ x ∈ B0579.cell c, P x) →
      ∀ᵐ x ∂B0579.cellMeasure c (-m), P x := fun P hP =>
    (B0579.cellMeasure_ac c (-m)).ae_le
      ((ae_restrict_iff' (B0579.measurableSet_cell c)).2
        (Eventually.of_forall fun x hx => hP x hx))
  have hG_meas : ∀ r j, AEStronglyMeasurable (velCoordG tr T j r) (B0579.cellMeasure c (-m)) :=
    fun r j => (velCoordG_continuous tr hT0 j r).aestronglyMeasurable
  have hG_bd : ∀ r j, ∀ᵐ x ∂B0579.cellMeasure c (-m), ‖velCoordG tr T j r x‖ ≤ C :=
    fun r j => hcell_ae _ fun x hx => by
      have h := (hB (clampT T r) (clampT_mem hT0 r) x hx).1 j
      unfold velCoordG
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
      exact h
  refine ⟨fun r j => mulBddCLM (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j), ?_, ?_, ?_⟩
  · intro r _ j
    exact norm_mulBddCLM_le _ _ hC0 _
  · intro j w r₀ hr₀
    unfold ContinuousWithinAt
    rw [tendsto_iff_norm_sub_tendsto_zero]
    let H : ℝ → ℝ × ℝ → ℂ := fun r x => velCoordG tr T j r x * w x
    have key : Tendsto (fun r => eLpNorm (fun x => H r x - H r₀ x) 2 (B0579.cellMeasure c (-m)))
        (𝓝[Icc 0 T] r₀) (𝓝 0) := by
      refine adjTT_dct (l := 𝓝[Icc 0 T] r₀) (K := 2 * C) (by linarith) ?_ (Lp.memLp w) ?_ ?_
      · intro r
        exact (((hG_meas r j).mul (Lp.aestronglyMeasurable w)).sub
          ((hG_meas r₀ j).mul (Lp.aestronglyMeasurable w))).aemeasurable
      · intro r
        filter_upwards [hG_bd r j, hG_bd r₀ j] with x h1 h2
        show ‖velCoordG tr T j r x * w x - velCoordG tr T j r₀ x * w x‖ ≤ 2 * C * ‖w x‖
        calc ‖velCoordG tr T j r x * w x - velCoordG tr T j r₀ x * w x‖
            ≤ ‖velCoordG tr T j r x * w x‖ + ‖velCoordG tr T j r₀ x * w x‖ := norm_sub_le _ _
          _ ≤ C * ‖w x‖ + C * ‖w x‖ := by
              rw [norm_mul, norm_mul]
              exact add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
                (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
          _ = 2 * C * ‖w x‖ := by ring
      · intro x
        have hc : ContinuousWithinAt (fun r => velCoordG tr T j r x) (Icc 0 T) r₀ :=
          velCoordG_contWithin tr hT0 j x hr₀
        have h1 : Tendsto (fun r => velCoordG tr T j r x * w x) (𝓝[Icc 0 T] r₀)
            (𝓝 (velCoordG tr T j r₀ x * w x)) :=
          (hc.mul_const (w x)).tendsto
        have h2 := h1.sub (tendsto_const_nhds (x := velCoordG tr T j r₀ x * w x))
        simpa using h2
    have hEqn : ∀ r ∈ Icc 0 T, ‖(mulBddCLM (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j) w
        - mulBddCLM (velCoordG tr T j r₀) (hG_meas r₀ j) hC0 (hG_bd r₀ j) w)‖ =
        ENNReal.toReal (eLpNorm (fun x => H r x - H r₀ x) 2 (B0579.cellMeasure c (-m))) := by
      intro r _
      rw [Lp.norm_def]
      congr 1
      apply eLpNorm_congr_ae
      filter_upwards [Lp.coeFn_sub
          (mulBddCLM (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j) w)
          (mulBddCLM (velCoordG tr T j r₀) (hG_meas r₀ j) hC0 (hG_bd r₀ j) w),
        mulBddCLM_apply_ae _ (hG_meas r j) hC0 (hG_bd r j) w,
        mulBddCLM_apply_ae _ (hG_meas r₀ j) hC0 (hG_bd r₀ j) w] with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    have key2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp key
    simp only [ENNReal.toReal_zero] at key2
    refine key2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hEqn r hr).symm
  · intro r hr j w
    filter_upwards [mulBddCLM_apply_ae (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j) w]
      with x hx
    show (mulBddCLM (velCoordG tr T j r) (hG_meas r j) hC0 (hG_bd r j) w) x = _
    rw [hx]
    unfold velCoordG
    rw [clampT_of_mem hr]

/-- **`PartIII-a:T21/2/7/1/6`**: the transport coefficient of the weak adjoint (SP 2819-2836). -/
theorem adjTransportCoeff (m : ℝ) : AdjTransportCoeff m := by
  intro ν hν tr T C hT0 hB
  exact adjTransport_of_c (Real.rpow_pos_of_pos hν _) tr m T C hT0 hB

end UnforcedLeray.Short.IIIa
