import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs

/-!
# `pdSigmaToLambda`: back from the phase-lag form to the `λ`-form

Source `the November 2 reference manuscript` 3611-3617 (`σ = τ + 2 log λ`).
Tonelli on the product, then the one-dimensional change of variables `l = e^{-(τ-σ)/2}` from
`Ioo 0 1` onto `Iio τ`, with Jacobian `2/l` and `λ · (2/λ) = 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pdSigmaToLambda : PDSigmaToLambda := by
  intro τ Φ hΦ
  have hA : Measurable (fun e : ℝ × Space =>
      if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1)) else 0) := by
    refine Measurable.ite (measurableSet_lt measurable_fst measurable_const) ?_ measurable_const
    exact Measurable.ennreal_ofReal (by unfold pdLam; fun_prop)
  have hF : Measurable (fun e : ℝ × Space =>
      (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1)) else 0) * Φ e) := hA.mul hΦ
  -- fibrewise: the integral over `z` of the `σ`-slice
  have hfib : ∀ σ : ℝ, (∫⁻ z : Space,
      (if σ < τ then ENNReal.ofReal (pdLam (τ - σ)) else 0) * Φ (σ, z)) =
      Set.indicator (Set.Iio τ)
        (fun σ => ENNReal.ofReal (pdLam (τ - σ)) * ∫⁻ z : Space, Φ (σ, z)) σ := by
    intro σ
    by_cases hσ : σ < τ
    · rw [if_pos hσ, Set.indicator_apply, if_pos (Set.mem_Iio.mpr hσ)]
      exact lintegral_const_mul' (ENNReal.ofReal (pdLam (τ - σ)))
        (fun z : Space => Φ (σ, z)) ENNReal.ofReal_ne_top
    · rw [if_neg hσ, Set.indicator_apply, if_neg (fun h => hσ (Set.mem_Iio.mp h))]
      simp
  have hstep1 : ∫⁻ e : ℝ × Space,
      (if e.1 < τ then ENNReal.ofReal (pdLam (τ - e.1)) else 0) * Φ e =
      ∫⁻ σ in Set.Iio τ, ENNReal.ofReal (pdLam (τ - σ)) * ∫⁻ z : Space, Φ (σ, z) := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hF.aemeasurable]
    refine (lintegral_congr hfib).trans ?_
    rw [lintegral_indicator measurableSet_Iio]
  -- the image of `Ioo 0 1` under `l ↦ τ + 2 log l` is `Iio τ`
  have himg : (fun l : ℝ => τ + 2 * Real.log l) '' Set.Ioo 0 1 = Set.Iio τ := by
    ext σ
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hlog : Real.log l < 0 := Real.log_neg hl.1 hl.2
      show τ + 2 * Real.log l < τ
      linarith
    · intro hσ
      have hσ' : σ < τ := hσ
      refine ⟨Real.exp ((σ - τ) / 2), ⟨Real.exp_pos _, ?_⟩, ?_⟩
      · rw [Real.exp_lt_one_iff]
        linarith
      · show τ + 2 * Real.log (Real.exp ((σ - τ) / 2)) = σ
        rw [Real.log_exp]
        ring
  have hderiv : ∀ l ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun l : ℝ => τ + 2 * Real.log l) (2 * l⁻¹) (Set.Ioo 0 1) l := by
    intro l hl
    exact (((Real.hasDerivAt_log hl.1.ne').const_mul 2).const_add τ).hasDerivWithinAt
  have hinj : Set.InjOn (fun l : ℝ => τ + 2 * Real.log l) (Set.Ioo 0 1) := by
    intro a ha b hb hab
    have hab' : τ + 2 * Real.log a = τ + 2 * Real.log b := hab
    have h1 : Real.log a = Real.log b := by linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha.1) (Set.mem_Ioi.mpr hb.1) h1
  have key : ∀ l ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (|2 * l⁻¹|) * (ENNReal.ofReal (pdLam (τ - (τ + 2 * Real.log l))) *
        ∫⁻ z : Space, Φ (τ + 2 * Real.log l, z)) =
      2 * ∫⁻ z : Space, Φ (τ + 2 * Real.log l, z) := by
    intro l hl
    have hl0 : 0 < l := hl.1
    have hp : 0 < 2 * l⁻¹ := by positivity
    have hlog : pdLam (τ - (τ + 2 * Real.log l)) = l := by
      unfold pdLam
      rw [show -((τ - (τ + 2 * Real.log l)) / 2) = Real.log l by ring]
      exact Real.exp_log hl0
    rw [hlog, abs_of_pos hp, ← mul_assoc, ← ENNReal.ofReal_mul hp.le]
    have h2 : 2 * l⁻¹ * l = 2 := by field_simp
    rw [h2, ENNReal.ofReal_ofNat]
  have hstep2 : ∫⁻ σ in Set.Iio τ, ENNReal.ofReal (pdLam (τ - σ)) * ∫⁻ z : Space, Φ (σ, z) =
      2 * ∫⁻ l in Set.Ioo (0 : ℝ) 1, ∫⁻ z : Space, Φ (τ + 2 * Real.log l, z) := by
    rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj]
    rw [setLIntegral_congr_fun measurableSet_Ioo key,
      lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  exact hstep1.trans hstep2

end UnforcedLeray.Short.PartIIIb.Concrete

end
