import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_4
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLipZeroCirc.CellInt

/-!
# `PartIII-a:T21/2/3/1/4`, leaf 1: the weak linearised flow keeps zero circulation

Source: `the November 2 reference manuscript` 270-288 and 2819-2830.

For `ω = w(ρ)` with `IsBiotSavart c ω u`, the curl clause tested with the cutoff `χ_R = ladCut R`
(which has `∂_q χ_R = 0`) gives `∫_cell ω χ_R = ∫_cell u₀ ∂_η χ_R`. As `R → ∞` the left side tends
to `∫_cell ω` (dominated convergence), and the right side tends to `0`: `∂_η χ_R` is bounded by
`K/R` and supported in `R ≤ |η| ≤ √2 R`, so the pointwise bound `|u₀ ∂_ηχ_R| ≤ (K/2)|u₀|² 1_{|η|≥R}
+ (K/2)R⁻² 1_{|η|≤√2R}` (AM-GM) integrates to `(K/2)·tail_R + O(1/R)`, with `tail_R → 0` by
dominated convergence since `u₀ ∈ L²(cell)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace FlowZeroAux

open LadCutPropsAux

lemma deriv_cutH_of_lt {y : ℝ} (h : y ^ 2 < 1) : deriv cutH y = 0 := by
  have ho : IsOpen {y' : ℝ | y' ^ 2 < 1} := isOpen_lt (by fun_prop) continuous_const
  have hev : cutH =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [ho.mem_nhds h] with y' hy'
    have hy'' : y' ^ 2 < 1 := hy'
    show cutH y' = 1
    unfold cutH
    exact Real.smoothTransition.one_of_one_le (by linarith)
  rw [hev.deriv_eq, deriv_const]

lemma deriv_cutH_of_gt {y : ℝ} (h : 2 < y ^ 2) : deriv cutH y = 0 := by
  have ho : IsOpen {y' : ℝ | 2 < y' ^ 2} := isOpen_lt continuous_const (by fun_prop)
  have hev : cutH =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [ho.mem_nhds h] with y' hy'
    have hy'' : 2 < y' ^ 2 := hy'
    show cutH y' = 0
    unfold cutH
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [hev.deriv_eq, deriv_const]

lemma pd1_ladCut {R : ℝ} (hR0 : R ≠ 0) (x : ℝ × ℝ) :
    B0579.pd 1 (ladCut R) x = deriv cutH (x.2 / R) * R⁻¹ := by
  rw [ladCut_eq, pd1_comp 1 R cutH x cutH_differentiable hR0, one_mul]

lemma pd1_ladCut_zero {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ}
    (h : x.2 ^ 2 < R ^ 2 ∨ 2 * R ^ 2 < x.2 ^ 2) : B0579.pd 1 (ladCut R) x = 0 := by
  rw [pd1_ladCut hR.ne' x]
  rcases h with h | h
  · have hy : (x.2 / R) ^ 2 < 1 := by
      rw [div_pow, div_lt_one (by positivity)]
      exact h
    rw [deriv_cutH_of_lt hy, zero_mul]
  · have hy : 2 < (x.2 / R) ^ 2 := by
      rw [div_pow, lt_div_iff₀ (by positivity)]
      linarith
    rw [deriv_cutH_of_gt hy, zero_mul]

lemma pd1_ladCut_zero' {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ}
    (h : ¬ (R ^ 2 ≤ x.2 ^ 2 ∧ x.2 ^ 2 ≤ 2 * R ^ 2)) : B0579.pd 1 (ladCut R) x = 0 := by
  rcases lt_or_ge (x.2 ^ 2) (R ^ 2) with h1 | h1
  · exact pd1_ladCut_zero hR (Or.inl h1)
  · have h2 : 2 * R ^ 2 < x.2 ^ 2 := by
      by_contra h2
      push_neg at h2
      exact h ⟨h1, h2⟩
    exact pd1_ladCut_zero hR (Or.inr h2)

lemma pd0_ladCut (R : ℝ) (x : ℝ × ℝ) : B0579.pd 0 (ladCut R) x = 0 := by
  rw [ladCut_eq, pd0_comp 1 R cutH x cutH_differentiable]

/-- Pointwise domination of `u₀ ∂_η χ_R` (AM-GM, `|∂_ηχ_R| ≤ K/R`, support in `R ≤ |η| ≤ √2 R`). -/
lemma pointwise_dom {K R : ℝ} (hK0 : 0 ≤ K) (hR : 0 < R) (z : ℂ) (g η : ℝ) (hg : |g| ≤ K / R)
    (hsupp : ¬ (R ^ 2 ≤ η ^ 2 ∧ η ^ 2 ≤ 2 * R ^ 2) → g = 0) :
    ‖z * (g : ℂ)‖ ≤ K / 2 * (if R ^ 2 ≤ η ^ 2 then ‖z‖ ^ 2 else 0) +
      K / 2 * (R⁻¹) ^ 2 * (if η ^ 2 ≤ 2 * R ^ 2 then (1 : ℝ) else 0) := by
  by_cases h : R ^ 2 ≤ η ^ 2 ∧ η ^ 2 ≤ 2 * R ^ 2
  · obtain ⟨h1, h2⟩ := h
    rw [if_pos h1, if_pos h2, norm_mul, Complex.norm_real, mul_one]
    have hgn : ‖g‖ ≤ K * R⁻¹ := by
      rw [Real.norm_eq_abs]
      calc |g| ≤ K / R := hg
        _ = K * R⁻¹ := div_eq_mul_inv _ _
    have h3 : ‖z‖ * ‖g‖ ≤ ‖z‖ * (K * R⁻¹) := mul_le_mul_of_nonneg_left hgn (norm_nonneg _)
    nlinarith [mul_nonneg hK0 (sq_nonneg (‖z‖ - R⁻¹))]
  · have hg0 := hsupp h
    rw [hg0, Complex.ofReal_zero, mul_zero, norm_zero]
    have hK2 : 0 ≤ K / 2 := by linarith
    have t1 : 0 ≤ K / 2 * (if R ^ 2 ≤ η ^ 2 then ‖z‖ ^ 2 else 0) :=
      mul_nonneg hK2 (by split_ifs <;> positivity)
    have t2 : 0 ≤ K / 2 * (R⁻¹) ^ 2 * (if η ^ 2 ≤ 2 * R ^ 2 then (1 : ℝ) else 0) :=
      mul_nonneg (mul_nonneg hK2 (sq_nonneg _)) (by split_ifs <;> norm_num)
    linarith

lemma box_volume (c R : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R) :
    volume (B0579.box c (2 * R)) = ENNReal.ofReal (c * (4 * R)) := by
  unfold B0579.box
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ c / 2 - -(c / 2) by linarith)]
  congr 1
  ring

/-- The tail of `‖u₀‖²` on `{|η| ≥ R}` tends to `0`. -/
lemma tail_tendsto {c : ℝ} (u0 : ℝ × ℝ → ℂ)
    (hu : Integrable (fun x => ‖u0 x‖ ^ 2) (volume.restrict (B0579.cell c))) :
    Tendsto (fun R : ℝ => ∫ x in B0579.cell c,
      {x : ℝ × ℝ | R ^ 2 ≤ x.2 ^ 2}.indicator (fun y => ‖u0 y‖ ^ 2) x) atTop (𝓝 0) := by
  have hS : ∀ R : ℝ, MeasurableSet {x : ℝ × ℝ | R ^ 2 ≤ x.2 ^ 2} := fun R =>
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (B0579.cell c)) (l := atTop)
    (F := fun (R : ℝ) (x : ℝ × ℝ) => {x : ℝ × ℝ | R ^ 2 ≤ x.2 ^ 2}.indicator
      (fun y => ‖u0 y‖ ^ 2) x)
    (f := fun _ => (0 : ℝ)) (fun x => ‖u0 x‖ ^ 2) ?_ ?_ hu ?_
  · simpa using h
  · exact Eventually.of_forall fun R => hu.aestronglyMeasurable.indicator (hS R)
  · refine Eventually.of_forall fun R => ae_of_all _ fun x => ?_
    simp only [Set.indicator_apply]
    split_ifs <;> simp [norm_nonneg]
  · refine ae_of_all _ fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (|x.2| + 1)] with R hR
    have hlt : x.2 ^ 2 < R ^ 2 := by nlinarith [sq_abs x.2, abs_nonneg x.2]
    simp [Set.indicator_apply, not_le.2 hlt]

/-- The cutoff-rate estimate `‖∫_cell u₀ ∂_ηχ_R‖ ≤ (K/2)·tail_R + 2Kc/R`. -/
lemma L_bound {c R K : ℝ} (hc : 1 ≤ c) (hR : 0 < R) (hK0 : 0 ≤ K) (u0 : ℝ × ℝ → ℂ)
    (hu : Integrable (fun x => ‖u0 x‖ ^ 2) (volume.restrict (B0579.cell c)))
    (hg : ∀ x, |B0579.pd 1 (ladCut R) x| ≤ K / R) :
    ‖∫ x in B0579.cell c, u0 x * (B0579.pd 1 (ladCut R) x : ℂ)‖ ≤
      K / 2 * (∫ x in B0579.cell c,
        {x : ℝ × ℝ | R ^ 2 ≤ x.2 ^ 2}.indicator (fun y => ‖u0 y‖ ^ 2) x) + 2 * K * c / R := by
  have hS : MeasurableSet {x : ℝ × ℝ | R ^ 2 ≤ x.2 ^ 2} :=
    (isClosed_le continuous_const (by fun_prop)).measurableSet
  have hS2 : MeasurableSet {x : ℝ × ℝ | x.2 ^ 2 ≤ 2 * R ^ 2} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hA : Integrable ({x : ℝ × ℝ | R ^ 2 ≤ x.2 ^ 2}.indicator (fun y => ‖u0 y‖ ^ 2))
      (volume.restrict (B0579.cell c)) := hu.indicator hS
  have hsub : {x : ℝ × ℝ | x.2 ^ 2 ≤ 2 * R ^ 2} ∩ B0579.cell c ⊆ B0579.box c (2 * R) := by
    intro x hx
    apply B0579.mem_box_of_mem_cell hx.2
    have h2 : x.2 ^ 2 ≤ 2 * R ^ 2 := hx.1
    nlinarith [sq_abs x.2, abs_nonneg x.2]
  have hfin : volume.restrict (B0579.cell c) {x : ℝ × ℝ | x.2 ^ 2 ≤ 2 * R ^ 2} ≠ ⊤ := by
    rw [Measure.restrict_apply hS2]
    exact ((measure_mono hsub).trans_lt (B0579.isCompact_box c (2 * R)).measure_lt_top).ne
  have hB : Integrable ({x : ℝ × ℝ | x.2 ^ 2 ≤ 2 * R ^ 2}.indicator (fun _ => (1 : ℝ)))
      (volume.restrict (B0579.cell c)) :=
    (integrable_indicator_iff hS2).2 (integrableOn_const hfin)
  have hBint : ∫ x in B0579.cell c, {x : ℝ × ℝ | x.2 ^ 2 ≤ 2 * R ^ 2}.indicator (fun _ => (1 : ℝ)) x
      ≤ c * (4 * R) := by
    rw [integral_indicator_const (1 : ℝ) hS2, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply hS2]
    apply ENNReal.toReal_le_of_le_ofReal (by nlinarith)
    calc volume ({x : ℝ × ℝ | x.2 ^ 2 ≤ 2 * R ^ 2} ∩ B0579.cell c)
        ≤ volume (B0579.box c (2 * R)) := measure_mono hsub
      _ = ENNReal.ofReal (c * (4 * R)) := box_volume c R (by linarith) hR.le
  have hmain : ‖∫ x in B0579.cell c, u0 x * (B0579.pd 1 (ladCut R) x : ℂ)‖ ≤
      ∫ x in B0579.cell c, (K / 2 * {x : ℝ × ℝ | R ^ 2 ≤ x.2 ^ 2}.indicator
          (fun y => ‖u0 y‖ ^ 2) x + K / 2 * (R⁻¹) ^ 2 *
          {x : ℝ × ℝ | x.2 ^ 2 ≤ 2 * R ^ 2}.indicator (fun _ => (1 : ℝ)) x) := by
    refine norm_integral_le_of_norm_le ((hA.const_mul (K / 2)).add (hB.const_mul _))
      (ae_of_all _ fun x => ?_)
    have hp := pointwise_dom hK0 hR (u0 x) (B0579.pd 1 (ladCut R) x) x.2 (hg x)
      (fun h => pd1_ladCut_zero' hR (x := x) h)
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    exact hp
  rw [integral_add (hA.const_mul _) (hB.const_mul _), integral_const_mul, integral_const_mul]
    at hmain
  have hcoef : 0 ≤ K / 2 * (R⁻¹) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hRne : R ≠ 0 := hR.ne'
  have e : K / 2 * (R⁻¹) ^ 2 * (c * (4 * R)) = 2 * K * c / R := by
    field_simp
    ring
  have hX := mul_le_mul_of_nonneg_left hBint hcoef
  linarith [hmain, hX, e]

end FlowZeroAux

open FlowZeroAux in
/-- **Leaf 1** (SP 270-288, 2819-2830): the weak linearised flow keeps zero circulation. -/
theorem ladFlowZeroCirc (m : ℝ) (hm : 1 < m) : LadFlowZeroCirc m := by
  intro ν c tr t f w u hc hf hflow ρ hρ
  obtain ⟨K, hK0, hK⟩ := ladCutProps
  have hc1 : (1 : ℝ) ≤ c := hc
  have hbs := hflow.biotSavart ρ hρ
  have hmemX := hflow.memX ρ hρ
  have hu0 : MemLp (fun x => u ρ x 0) 2 (volume.restrict (B0579.cell c)) := hbs.1 0
  have hint : IntegrableOn (w ρ) (B0579.cell c) := integrableOn_cell_of_X hm hmemX
  refine ⟨hint, ?_⟩
  have hsq : Integrable (fun x => ‖u ρ x 0‖ ^ 2) (volume.restrict (B0579.cell c)) := by
    have h := hu0.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa [Real.rpow_two] using h
  -- the cut-off rate tends to zero
  have hT := tail_tendsto (u ρ · 0) hsq
  have hbound_lim : Tendsto (fun R : ℝ => K / 2 * (∫ x in B0579.cell c,
      {x : ℝ × ℝ | R ^ 2 ≤ x.2 ^ 2}.indicator (fun y => ‖u ρ y 0‖ ^ 2) x) + 2 * K * c / R)
      atTop (𝓝 0) := by
    have h1 := hT.const_mul (K / 2)
    have h2 : Tendsto (fun R : ℝ => 2 * K * c / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h3 := h1.add h2
    simpa using h3
  have hLlim : Tendsto (fun R : ℝ => ∫ x in B0579.cell c, u ρ x 0 * (B0579.pd 1 (ladCut R) x : ℂ))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound_lim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
    exact L_bound hc1 (by linarith) hK0 (u ρ · 0) hsq
      (fun x => (hK R (by linarith)).2.2.2.2.1 x 1)
  -- the cut-off integrals of `w ρ` converge to its circulation
  have hωlim : Tendsto (fun R : ℝ => ∫ x in B0579.cell c, w ρ x * (ladCut R x : ℂ)) atTop
      (𝓝 (∫ x in B0579.cell c, w ρ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖w ρ x‖) ?_ ?_ hint.norm ?_
    · refine Eventually.of_forall fun R => ?_
      exact hint.aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp (CutLimitAux.continuous_cut R)).aestronglyMeasurable
    · refine Eventually.of_forall fun R => ae_of_all _ fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (CutLimitAux.nonneg R x)]
      exact mul_le_of_le_one_right (norm_nonneg _) (CutLimitAux.le_one R x)
    · refine ae_of_all _ fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (|x.2| + 1)] with R hR
      rw [CutLimitAux.eq_one hR]
      simp
  -- identify the cut-off integrals through the curl clause
  have heq : (fun R : ℝ => ∫ x in B0579.cell c, w ρ x * (ladCut R x : ℂ)) =ᶠ[atTop]
      (fun R : ℝ => ∫ x in B0579.cell c, u ρ x 0 * (B0579.pd 1 (ladCut R) x : ℂ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [hbs.2.2 (ladCut R) ((hK R hR).1 c)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [pd0_ladCut]
  have hlim2 : Tendsto (fun R : ℝ => ∫ x in B0579.cell c, w ρ x * (ladCut R x : ℂ)) atTop
      (𝓝 0) := hLlim.congr' heq.symm
  exact tendsto_nhds_unique hωlim hlim2

end UnforcedLeray.Short.IIIa
