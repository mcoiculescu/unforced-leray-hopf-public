import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

/-!
# `PartIII-a:T21/2/7/2/2/1/2/5`: the `lintegral` form of the cutoff gradient energy

Source: `the November 2 reference manuscript`
(SP) lines 3060-3067 (cutoff energy identity and its integral), 3044-3049 (weights), 3052-3058.

Proves `AdjCutConvert m` (leaf (e) of `AdjCutRate`):
* `cutGradEnergy c m R φ k ρ = ofReal (cutGReal c m R φ k ρ)` for `ρ ∈ [t, s)`, via
  `integral_cellMeasure_eq` (the weight `jb^{-m}` of the cell measure) and the
  integrability of the continuous integrand, which vanishes outside the band `2R² ≤ x.2²`;
* `cutGReal ≥ 0` and continuous on `[t, s)` (hypothesis `AdjCutE0Cont`);
* `∫⁻_{Ioc r s'} ofReal G = ofReal ∫_r^{s'} G` for `G ≥ 0` continuous on `[r, s']`;
* the finite sum over `k` and the constant `ν = ofReal ν` pass through `ofReal`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace AdjCutConvertAux

lemma ladCut_continuous' (R : ℝ) : Continuous (ladCut R) := by
  unfold ladCut
  exact Real.smoothTransition.continuous.comp (by fun_prop)

/-- The transverse cutoff vanishes on the band `2R² ≤ η²`. -/
lemma ladCut_zero_of_band {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R ^ 2 ≤ x.2 ^ 2) :
    ladCut R x = 0 := by
  unfold ladCut
  apply Real.smoothTransition.zero_of_nonpos
  have h : 2 ≤ x.2 ^ 2 / R ^ 2 := (le_div_iff₀ (by positivity)).2 hx
  linarith

lemma pdCx_continuous' {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 2) :
    Continuous (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The slice `x ↦ φ ρ x` is smooth for `ρ ∈ [t, s)`. -/
lemma slice_contDiff {t s ρ : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hρ : ρ ∈ Ico t s) : ContDiff ℝ ∞ (φ ρ) := by
  have h1 : ContDiffOn ℝ ∞ ((fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) ∘
      (fun x : ℝ × ℝ => ((ρ, x) : ℝ × (ℝ × ℝ)))) univ :=
    hφ.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨hρ, mem_univ x⟩)
  rw [contDiffOn_univ] at h1
  exact h1

/-- The cell integral of the cutoff gradient energy equals the `ofReal` of the real integral. -/
lemma cutLint_eq (c m R : ℝ) (hR : 0 < R) (F : ℝ × ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (k : Fin 2) :
    ∫⁻ x, ENNReal.ofReal (ladCut R x ^ 2) * ‖pdCx k F x‖ₑ ^ (2 : ℝ)
        ∂(B0579.cellMeasure c (-m)) =
      ENNReal.ofReal (∫ x in B0579.cell c,
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k F x‖ ^ 2)) := by
  -- the real integrand `v x = ladCut² ‖∂_k F‖²` and its weighted form
  have hu_cont : Continuous (fun x => B0579.jb x ^ (-m) * (ladCut R x ^ 2 * ‖pdCx k F x‖ ^ 2)) := by
    apply Continuous.mul (B0579.continuous_jb_rpow (-m))
    exact ((ladCut_continuous' R).pow 2).mul (((pdCx_continuous' hF k).norm).pow 2)
  have hint_cell : IntegrableOn
      (fun x => B0579.jb x ^ (-m) * (ladCut R x ^ 2 * ‖pdCx k F x‖ ^ 2)) (B0579.cell c) := by
    refine B0579.integrableOn_cell_of_continuous hu_cont (B0579.isCompact_box c (2 * R)) ?_
    intro x hx hK
    have hband : 2 * R ^ 2 ≤ x.2 ^ 2 := by
      by_contra h
      push Not at h
      apply hK
      apply B0579.mem_box_of_mem_cell hx
      nlinarith [sq_abs x.2, abs_nonneg x.2]
    rw [ladCut_zero_of_band hR hband]
    simp
  -- integrability of `v` against the cell measure
  have hv : Integrable (fun x => ladCut R x ^ 2 * ‖pdCx k F x‖ ^ 2)
      (B0579.cellMeasure c (-m)) := by
    unfold B0579.cellMeasure
    rw [integrable_withDensity_iff_integrable_smul'
      (B0579.measurable_density (-m)).coe_nnreal_ennreal
      (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
    have hfun : (fun x => (((B0579.density (-m) x : NNReal) : ℝ≥0∞)).toReal •
        (ladCut R x ^ 2 * ‖pdCx k F x‖ ^ 2)) =
        fun x => B0579.jb x ^ (-m) * (ladCut R x ^ 2 * ‖pdCx k F x‖ ^ 2) := by
      funext x
      rw [smul_eq_mul, ENNReal.coe_toReal, B0579.coe_density]
    rw [hfun]
    exact hint_cell
  have hμint : ∫ x, ladCut R x ^ 2 * ‖pdCx k F x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) =
      ∫ x in B0579.cell c, B0579.jb x ^ (-m) * (ladCut R x ^ 2 * ‖pdCx k F x‖ ^ 2) :=
    integral_cellMeasure_eq c m (fun x => ladCut R x ^ 2 * ‖pdCx k F x‖ ^ 2)
  have hz : ∀ x, ‖pdCx k F x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖pdCx k F x‖ ^ 2) := by
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two]
  have hlin : ∫⁻ x, ENNReal.ofReal (ladCut R x ^ 2) * ‖pdCx k F x‖ₑ ^ (2 : ℝ)
        ∂(B0579.cellMeasure c (-m)) =
      ∫⁻ x, ENNReal.ofReal (ladCut R x ^ 2 * ‖pdCx k F x‖ ^ 2)
        ∂(B0579.cellMeasure c (-m)) := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (sq_nonneg _), hz x]
  rw [hlin, ← ofReal_integral_eq_lintegral_ofReal hv
    (Eventually.of_forall fun x => by positivity), hμint]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

/-- Nonnegativity of the real cutoff energy density integral. -/
lemma cutGReal_nonneg (c m R : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (k : Fin 2) (ρ : ℝ) :
    0 ≤ ∫ x in B0579.cell c,
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k (φ ρ) x‖ ^ 2) := by
  refine setIntegral_nonneg (B0579.measurableSet_cell c) (fun x _ => ?_)
  exact mul_nonneg (sq_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))

end AdjCutConvertAux

open AdjCutConvertAux in
/-- **(e) Conversion to `lintegral` form** (`AdjCutConvert m`, SP 3060-3067). -/
theorem adjCutConvert (m : ℝ) : AdjCutConvert m := by
  intro hcont ν tr t s G φ hctx K hK R hR r hr s' hs'
  have hν : 0 < ν := hctx.1
  have hφ := hctx.2.2.2.2.2.2.2
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hrs : r ≤ s' := hs'.1
  have hIoc : Ioc r s' ⊆ Ico t s := fun ρ hρ =>
    ⟨le_trans hr.1 (le_of_lt hρ.1), lt_of_le_of_lt hρ.2 hs'.2⟩
  have hIcc : Icc r s' ⊆ Ico t s := fun ρ hρ =>
    ⟨le_trans hr.1 hρ.1, lt_of_le_of_lt hρ.2 hs'.2⟩
  have hpt : ∀ k : Fin 2, ∀ ρ ∈ Ico t s,
      cutGradEnergy (ν ^ (-2 : ℝ)) m R φ k ρ =
        ENNReal.ofReal (cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ) := by
    intro k ρ hρ
    exact cutLint_eq _ m R hRpos (φ ρ) (slice_contDiff hφ hρ) k
  have hI0 : ∀ k : Fin 2, 0 ≤ ∫ ρ in r..s', cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ := fun k =>
    intervalIntegral.integral_nonneg hrs (fun ρ _ => cutGReal_nonneg _ m R φ k ρ)
  have hstep : ∀ k : Fin 2,
      ∫⁻ ρ in Ioc r s', cutGradEnergy (ν ^ (-2 : ℝ)) m R φ k ρ =
        ENNReal.ofReal (∫ ρ in r..s', cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ) := by
    intro k
    have hcontG : ContinuousOn (cutGReal (ν ^ (-2 : ℝ)) m R φ k) (Ico t s) :=
      (hcont ν tr t s G φ hctx R hRpos).2.2 k
    have hintIoc : IntegrableOn (cutGReal (ν ^ (-2 : ℝ)) m R φ k) (Ioc r s') :=
      ((hcontG.mono hIcc).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have e1 : ∫⁻ ρ in Ioc r s', cutGradEnergy (ν ^ (-2 : ℝ)) m R φ k ρ =
        ∫⁻ ρ in Ioc r s', ENNReal.ofReal (cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ) :=
      setLIntegral_congr_fun measurableSet_Ioc (fun ρ hρ => hpt k ρ (hIoc hρ))
    have e2 : ENNReal.ofReal (∫ ρ in Ioc r s', cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ) =
        ∫⁻ ρ in Ioc r s', ENNReal.ofReal (cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ) :=
      ofReal_integral_eq_lintegral_ofReal hintIoc
        (Eventually.of_forall fun ρ => cutGReal_nonneg _ m R φ k ρ)
    have e3 : ∫ ρ in r..s', cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ =
        ∫ ρ in Ioc r s', cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ :=
      intervalIntegral.integral_of_le hrs
    rw [e1, e3, ← e2]
  rw [Finset.sum_congr rfl (fun k _ => hstep k),
    ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun k : Fin 2 => ∫ ρ in r..s', cutGReal (ν ^ (-2 : ℝ)) m R φ k ρ)
      (fun k _ => hI0 k),
    ← ENNReal.ofReal_mul hν.le]
  exact ENNReal.ofReal_le_ofReal (hK R hR r hr s' hs')

end UnforcedLeray.Short.IIIa
