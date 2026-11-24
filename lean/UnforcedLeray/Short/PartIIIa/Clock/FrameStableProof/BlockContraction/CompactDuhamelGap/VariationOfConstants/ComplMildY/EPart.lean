import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildY.Ampl

/-!
# Helper for `PartIII-a:T21/c3/2/1/2/3/1`: the rescaled frame vectors on the fixed cell

Source: `the November 2 reference manuscript` lines 2891-2897 and 2914-2925.

`eFun κ ν i r x = a(r)⁻² E_i(x/√a(r))` is the frame vector `E_i` of the moving cell
`d(r) = c/√a(r)` pulled back to the fixed cell `c = ν⁻²` with the factor `a⁻²` of `J_a`. On a
block with cell lengths `≥ 1` it lies in `X_{m,c}` (Gaussian tails, `perE_pointwise`) and is
continuous in `r` in `X_{m,c}` (dominated convergence).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa.ComplMildYAux

open FlowMeas

/-- The rescaled periodized growing vector on the fixed cell: `x ↦ a⁻² E_i(x/√a)`. -/
def eFun (κ : PlanarFrameKernels) (ν : ℝ) (i : Fin 2) (r : ℝ) (x : ℝ × ℝ) : ℂ :=
  ((((clockA ν r) ^ 2)⁻¹ : ℝ) : ℂ) *
    perE κ (cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) i
      (x.1 / Real.sqrt (clockA ν r), x.2 / Real.sqrt (clockA ν r))

theorem continuous_eFun (κ : PlanarFrameKernels) {ν r : ℝ}
    (hd : 0 < cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) (i : Fin 2) : Continuous (eFun κ ν i r) := by
  unfold eFun
  exact continuous_const.mul ((FrameCont.perE_continuous κ hd i).comp
    ((continuous_fst.div_const _).prodMk (continuous_snd.div_const _)))

/-- Gaussian bound of the rescaled vectors on the fixed cell, uniform on the block. -/
theorem eFun_bound (κ : PlanarFrameKernels) {ν t s : ℝ} (hν : 0 < ν) (ht : 0 ≤ t)
    (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (i : Fin 2), ∀ r ∈ Icc t s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ‖eFun κ ν i r x‖ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by
  obtain ⟨M, hM0, hM⟩ := perE_pointwise κ
  refine ⟨M, hM0, fun i r' hr' x hx => ?_⟩
  have hd1' := hd1 r' hr'
  have ha'1 : 1 ≤ clockA ν r' := one_le_clockA hν.le (ht.trans hr'.1)
  have ha's : clockA ν r' ≤ clockA ν s := clockA_mono hν.le hr'.2
  unfold eFun
  set a' := clockA ν r'
  set d' := cellLen (ν ^ (-2 : ℝ)) a'
  have hsa' : 0 < Real.sqrt a' := Real.sqrt_pos.2 (by linarith)
  have hy : (x.1 / Real.sqrt a', x.2 / Real.sqrt a') ∈ B0579.cell d' := by
    have hsmul : Real.sqrt a' • (x.1 / Real.sqrt a', x.2 / Real.sqrt a') ∈
        B0579.cell (d' * Real.sqrt a') := by
      have heq1 : Real.sqrt a' • (x.1 / Real.sqrt a', x.2 / Real.sqrt a') = x := by
        ext <;> simp [smul_eq_mul, mul_div_cancel₀ _ hsa'.ne']
      have heq2 : d' * Real.sqrt a' = ν ^ (-2 : ℝ) := by
        simp only [d', cellLen, div_mul_cancel₀ _ hsa'.ne']
      rwa [heq1, heq2]
    exact (T07.smul_mem_cell_iff d' (Real.sqrt a') hsa' _).1 hsmul
  have hE := hM d' hd1' i _ hy
  have hexp_le : Real.exp (-((x.1 / Real.sqrt a') ^ 2 + (x.2 / Real.sqrt a') ^ 2) / 16) ≤
      Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by
    rw [div_pow, div_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ a')]
    have heq : -((x.1 ^ 2 / a' + x.2 ^ 2 / a') / 16) = -(x.1 ^ 2 + x.2 ^ 2) / (16 * a') := by
      ring
    rw [neg_div, heq, neg_div, neg_div]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    exact div_le_div_of_nonneg_left (add_nonneg (sq_nonneg x.1) (sq_nonneg x.2))
      (by linarith) (by linarith)
  have hfac0 : 0 ≤ (a' ^ 2)⁻¹ := by positivity
  have hfac1 : (a' ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hfac0]
  calc (a' ^ 2)⁻¹ * ‖perE κ d' i (x.1 / Real.sqrt a', x.2 / Real.sqrt a')‖
      ≤ 1 * (M * Real.exp (-((x.1 / Real.sqrt a') ^ 2 + (x.2 / Real.sqrt a') ^ 2) / 16)) :=
        mul_le_mul hfac1 hE (norm_nonneg _) zero_le_one
    _ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by
        rw [one_mul]; exact mul_le_mul_of_nonneg_left hexp_le hM0

/-- The weighted Gaussian has finite integral on the cell. -/
theorem lintegral_gauss_ne_top {c m A C : ℝ} (hm : 0 ≤ m) (hA : 0 < A) (hC : 0 ≤ C) :
    (∫⁻ x, ENNReal.ofReal (C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
      ∂(B0579.cellMeasure c m)) ≠ ⊤ := by
  have hdom_meas : Measurable
      (fun x : ℝ × ℝ => ENNReal.ofReal (C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))) := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp ?_))
    exact (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).neg).div_const _
  have hJi := (integrable_jb_gauss_scaled hm hA).const_mul C
  have hle : (∫⁻ x, ENNReal.ofReal (C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
        ∂(B0579.cellMeasure c m)) ≤
      ∫⁻ x, ENNReal.ofReal (C *
        (B0579.jb x ^ m * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))) := by
    calc ∫⁻ x, ENNReal.ofReal (C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
          ∂(B0579.cellMeasure c m)
        = ∫⁻ x, (B0579.density m x : ℝ≥0∞) *
            ENNReal.ofReal (C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A)))
            ∂(volume.restrict (B0579.cell c)) := by
          unfold B0579.cellMeasure
          exact lintegral_withDensity_eq_lintegral_mul _
            (B0579.measurable_density m).coe_nnreal_ennreal hdom_meas
      _ ≤ ∫⁻ x, (B0579.density m x : ℝ≥0∞) *
            ENNReal.ofReal (C * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * A))) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = _ := by
          refine lintegral_congr fun x => ?_
          rw [T07.density_coe, ← ENNReal.ofReal_mul (Real.rpow_nonneg (B0579.jb_pos x).le m)]
          congr 1; ring
  refine ne_top_of_le_ne_top ?_ hle
  rw [← ofReal_integral_eq_lintegral_ofReal hJi
    (Eventually.of_forall fun x => mul_nonneg hC
      (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le m) (Real.exp_pos _).le))]
  exact ENNReal.ofReal_ne_top

/-- The rescaled vectors lie in `X_{m,c}`. -/
theorem memLp_eFun (κ : PlanarFrameKernels) {ν m t s : ℝ} (hm : 0 ≤ m) (hν : 0 < ν)
    (ht : 0 ≤ t) (hts : t ≤ s) (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (i : Fin 2) (r : ℝ) (hr : r ∈ Icc t s) :
    MemLp (eFun κ ν i r) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := by
  obtain ⟨M, hM0, hM⟩ := eFun_bound κ hν ht hd1
  have hAs : 0 < clockA ν s := lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hts))
  have hcont := continuous_eFun κ (lt_of_lt_of_le zero_lt_one (hd1 r hr)) i
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  rw [T07.eLpNorm_two_eq_lintegral]
  have hfin := lintegral_gauss_ne_top (c := ν ^ (-2 : ℝ)) (m := m) (C := M ^ 2) hm hAs
    (sq_nonneg M)
  have hle : (∫⁻ x, ‖eFun κ ν i r x‖ₑ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) ≤
      ∫⁻ x, ENNReal.ofReal (M ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * clockA ν s)))
        ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m) := by
    refine lintegral_mono_ae ?_
    refine (B0579.cellMeasure_ac (ν ^ (-2 : ℝ)) m).ae_le ?_
    filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x hx
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖eFun κ ν i r x‖ ^ 2
        ≤ (M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hM i r hr x hx) 2
      _ = M ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * clockA ν s)) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 2; push_cast; ring
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_top_of_le_ne_top hfin hle)

/-- **Continuity of the rescaled vectors** in `X_{m,c}` along the block. -/
theorem tendsto_xNorm_eFun (κ : PlanarFrameKernels) {ν m t s : ℝ} (hm : 0 ≤ m) (hν : 0 < ν)
    (ht : 0 ≤ t) (hts : t ≤ s) (hd1 : ∀ r ∈ Icc t s, 1 ≤ cellLen (ν ^ (-2 : ℝ)) (clockA ν r))
    (i : Fin 2) (r : ℝ) (hr : r ∈ Icc t s) :
    Tendsto (fun r' => xNorm (ν ^ (-2 : ℝ)) m (eFun κ ν i r' - eFun κ ν i r))
      (𝓝[Icc t s] r) (𝓝 0) := by
  set Ep : ℝ → ℝ × ℝ → ℂ := fun r' => eFun κ ν i r'
  obtain ⟨M, hM0, hM⟩ := eFun_bound κ hν ht hd1
  have hEp_cont : ∀ r' ∈ Icc t s, Continuous (Ep r') := fun r' hr' =>
    continuous_eFun κ (lt_of_lt_of_le zero_lt_one (hd1 r' hr')) i
  have hEp_bdd : ∀ r' ∈ Icc t s, ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      ‖Ep r' x‖ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) :=
    fun r' hr' x hx => hM i r' hr' x hx
  have hlint : Tendsto
      (fun r' => ∫⁻ x, ‖Ep r' x - Ep r x‖ₑ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
      (𝓝[Icc t s] r) (𝓝 0) := by
    have hAs_pos : 0 < clockA ν s :=
      lt_of_lt_of_le zero_lt_one (one_le_clockA hν.le (ht.trans hts))
    set dom : ℝ × ℝ → ℝ≥0∞ := fun x =>
      ENNReal.ofReal ((2 * M) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * clockA ν s)))
    have hdom_fin : (∫⁻ x, dom x ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) ≠ ⊤ :=
      lintegral_gauss_ne_top hm hAs_pos (sq_nonneg _)
    have hlim : Tendsto
        (fun r' => ∫⁻ x, ‖Ep r' x - Ep r x‖ₑ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m))
        (𝓝[Icc t s] r) (𝓝 (∫⁻ _ : ℝ × ℝ, 0 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m))) := by
      refine MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
        dom ?_ ?_ hdom_fin ?_
      · filter_upwards [self_mem_nhdsWithin] with r' hr'
        exact ((hEp_cont r' hr').sub (hEp_cont r hr)).measurable.enorm.pow_const 2
      · filter_upwards [self_mem_nhdsWithin] with r' hr'
        refine (B0579.cellMeasure_ac (ν ^ (-2 : ℝ)) m).ae_le ?_
        filter_upwards [ae_restrict_mem (B0579.measurableSet_cell _)] with x hx
        have htri : ‖Ep r' x - Ep r x‖ ≤
            2 * M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by
          calc ‖Ep r' x - Ep r x‖ ≤ ‖Ep r' x‖ + ‖Ep r x‖ := norm_sub_le _ _
            _ ≤ M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) +
                  M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) :=
                add_le_add (hEp_bdd r' hr' x hx) (hEp_bdd r hr x hx)
            _ = 2 * M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s)) := by ring
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖Ep r' x - Ep r x‖ ^ 2
            ≤ (2 * M * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (16 * clockA ν s))) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) htri 2
          _ = (2 * M) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * clockA ν s)) := by
              rw [mul_pow, ← Real.exp_nat_mul]
              congr 2; push_cast; ring
      · refine Eventually.of_forall fun x => ?_
        obtain ⟨C_e, hC_e⟩ := FrameCont.e_translate_bound κ
        have hC_e0 : 0 ≤ max C_e 0 := le_max_right _ _
        have hC_e' : ∀ z, ‖κ.e i z‖ ≤ max C_e 0 * (1 + |z.1|) ^ (-(2 : ℝ)) := fun z =>
          (hC_e i z).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        have hfac : ContinuousOn (fun r' => ((((clockA ν r') ^ 2)⁻¹ : ℝ) : ℂ)) (Icc t s) := by
          refine Complex.continuous_ofReal.comp_continuousOn ?_
          refine ((continuousOn_clockA _).pow 2).inv₀ fun r' hr' => ?_
          have := one_le_clockA hν.le (ht.trans hr'.1)
          exact (pow_pos (by linarith) 2).ne'
        have hc_Ep : ContinuousOn (fun r' => Ep r' x) (Icc t s) :=
          hfac.mul (continuousOn_perSum_scaled (κ.e_cont i) hC_e0 hC_e' hν ht hd1 x)
        have hsub0 : Tendsto (fun r' => Ep r' x - Ep r x) (𝓝[Icc t s] r) (𝓝 0) := by
          simpa using (hc_Ep r hr).tendsto.sub (tendsto_const_nhds (x := Ep r x))
        have he0 : Tendsto (fun r' => ‖Ep r' x - Ep r x‖ₑ ^ 2) (𝓝[Icc t s] r)
            (𝓝 (‖(0 : ℂ)‖ₑ ^ 2)) :=
          (((ENNReal.continuous_pow 2).comp continuous_enorm).tendsto 0).comp hsub0
        simpa using he0
    simpa using hlim
  have hrpow : Tendsto
      (fun r' => (∫⁻ x, ‖Ep r' x - Ep r x‖ₑ ^ 2 ∂(B0579.cellMeasure (ν ^ (-2 : ℝ)) m)) ^
        (1 / 2 : ℝ))
      (𝓝[Icc t s] r) (𝓝 ((0 : ℝ≥0∞) ^ (1 / 2 : ℝ))) :=
    (ENNReal.continuous_rpow_const.tendsto 0).comp hlint
  unfold xNorm
  simp_rw [T07.eLpNorm_two_eq_lintegral]
  simpa only [Function.comp_def, Pi.sub_apply, Ep,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hrpow

end UnforcedLeray.Short.IIIa.ComplMildYAux
