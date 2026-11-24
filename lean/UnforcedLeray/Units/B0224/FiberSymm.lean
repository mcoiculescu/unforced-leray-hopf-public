import UnforcedLeray.Units.B0224.FiberHeat

/-!
# B0224 helper: the age-dependent cylinder heat is self-adjoint on `H`

Blueprint unit B0224 (label `eq:st18-t00117`), `paper/main.tex` lines 3370–3379; proof outline
"the adjoint follows by the same substitution and self-adjointness of heat". The heat `H_θ`
(`heatH`) acts at fixed age `s`, so `⟨H_θ f, g⟩_H = ∫ s^{-3/2} ∫_strip ⟨e^{θ(s)Δ}f(s), g(s)⟩ ds`
and the symmetry of the heat on each fibre (`integral_strip_inner_planeHeat`) gives
`isSelfAdjoint_heatH`. The fibres `f(s, ·)` are in `L²(strip)` for a.e. `s > 0`
(`ae_slice_lt_top`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.B0224

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.B0220

variable {c : ℝ} {θ : ℝ → ℝ}

/-- An `H`-integral as an iterated integral `∫_{s>0} ∫_strip s^{-3/2} φ`. -/
theorem integral_measureH_eq_iter {φ : Profile → ℝ} (hφ : Integrable φ (measureH c)) :
    ∫ p, φ p ∂measureH c =
      ∫ s in Ioi (0 : ℝ), ∫ x in strip c, (weightH (s, x)).toReal * φ (s, x) := by
  have hlt : ∀ᵐ p ∂cellMeasure c, weightH p < ∞ :=
    Eventually.of_forall fun p => ENNReal.ofReal_lt_top
  have hint : Integrable (fun p => (weightH p).toReal • φ p) (cellMeasure c) :=
    (integrable_withDensity_iff_integrable_smul' measurable_weightH hlt).1 hφ
  rw [measureH, integral_withDensity_eq_integral_toReal_smul measurable_weightH hlt]
  rw [cellMeasure_eq_prod'] at hint ⊢
  rw [integral_prod _ hint]
  simp only [smul_eq_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- For `f ∈ H`, a.e. fibre `f(s, ·)` is in `L²` of the strip. -/
theorem ae_slice_lt_top (f : HSpace c E) :
    ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), ∫⁻ x in strip c, ‖f (s, x)‖ₑ ^ 2 < ∞ := by
  have h := lintegral_sq_lt_top f
  have hm : Measurable fun p : Profile => ‖f p‖ₑ ^ 2 :=
    (Lp.stronglyMeasurable f).enorm.pow_const 2
  have hmw : Measurable fun p : Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ‖f p‖ₑ ^ 2 :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).mul hm
  rw [lintegral_measureH_eq _ hm, cellMeasure_eq_prod',
    lintegral_prod (fun p : Profile => ENNReal.ofReal (p.1 ^ (-(3 / 2 : ℝ))) * ‖f p‖ₑ ^ 2)
      hmw.aemeasurable] at h
  have hmeas : Measurable fun s : ℝ => ∫⁻ x in strip c,
      ENNReal.ofReal ((s, x).1 ^ (-(3 / 2 : ℝ))) * ‖f (s, x)‖ₑ ^ 2 :=
    hmw.lintegral_prod_right'
  filter_upwards [ae_lt_top hmeas h.ne, ae_restrict_mem measurableSet_Ioi] with s hs hpos
  have hms : Measurable fun x : ℝ × ℝ => ‖f (s, x)‖ₑ ^ 2 := hm.comp measurable_prodMk_left
  rw [lintegral_const_mul _ hms] at hs
  have hw : ENNReal.ofReal (s ^ (-(3 / 2 : ℝ))) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos _)).ne'
  exact ENNReal.lt_top_of_mul_ne_top_right hs.ne hw

/-- The fibre of `f ∈ H` at age `s`, extended `c`-periodically in `q`. -/
theorem slice_facts (hc : 0 < c) (f : HSpace c E) (s : ℝ)
    (hs : ∫⁻ x in strip c, ‖f (s, x)‖ₑ ^ 2 < ∞) :
    StronglyMeasurable (fun z : ℝ × ℝ => periodize c (f : Profile → E) (s, z)) ∧
      Cyl.IsPeriodic c (fun z : ℝ × ℝ => periodize c (f : Profile → E) (s, z)) ∧
      ∫⁻ x in strip c, ‖periodize c (f : Profile → E) (s, x)‖ₑ ^ 2 < ∞ := by
  refine ⟨(stronglyMeasurable_periodize (Lp.stronglyMeasurable f)).comp_measurable
    measurable_prodMk_left, isPeriodic_periodize_slice hc _ s, ?_⟩
  rwa [setLIntegral_congr_fun (measurableSet_strip c)
    (fun x hx => by rw [periodize_slice_of_mem hc _ s hx])]

/-- **The age-dependent cylinder heat is symmetric on `H`.** -/
theorem inner_heatH (hc : 0 < c) (hθ : Measurable θ) (f g : HSpace c E) :
    ⟪heatH hc hθ f, g⟫_ℝ = ⟪f, heatH hc hθ g⟫_ℝ := by
  have e1 : (fun p => ⟪heatH hc hθ f p, g p⟫_ℝ) =ᵐ[measureH c]
      fun p => ⟪fiberHeat c θ f p, g p⟫_ℝ := by
    filter_upwards [coeFn_heatH hc hθ f] with p hp
    rw [hp]
  have e2 : (fun p => ⟪f p, heatH hc hθ g p⟫_ℝ) =ᵐ[measureH c]
      fun p => ⟪f p, fiberHeat c θ g p⟫_ℝ := by
    filter_upwards [coeFn_heatH hc hθ g] with p hp
    rw [hp]
  have hI1 := (L2.integrable_inner (𝕜 := ℝ) (heatH hc hθ f) g).congr e1
  have hI2 := (L2.integrable_inner (𝕜 := ℝ) f (heatH hc hθ g)).congr e2
  rw [L2.inner_def, L2.inner_def, integral_congr_ae e1, integral_congr_ae e2,
    integral_measureH_eq_iter hI1, integral_measureH_eq_iter hI2]
  refine integral_congr_ae ?_
  filter_upwards [ae_slice_lt_top f, ae_slice_lt_top g] with s hfs hgs
  obtain ⟨hu, hup, hu2⟩ := slice_facts hc f s hfs
  obtain ⟨hv, hvp, hv2⟩ := slice_facts hc g s hgs
  simp only [weightH]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have ea : ∫ x in strip c, ⟪fiberHeat c θ f (s, x), g (s, x)⟫_ℝ =
      ∫ x in strip c, ⟪planeHeat (θ s) (fun z => periodize c (f : Profile → E) (s, z)) x,
        periodize c (g : Profile → E) (s, x)⟫_ℝ :=
    setIntegral_congr_fun (measurableSet_strip c) fun x hx => by
      simp only [fiberHeat, periodize_slice_of_mem hc _ s hx]
  have eb : ∫ x in strip c, ⟪f (s, x), fiberHeat c θ g (s, x)⟫_ℝ =
      ∫ x in strip c, ⟪periodize c (f : Profile → E) (s, x),
        planeHeat (θ s) (fun z => periodize c (g : Profile → E) (s, z)) x⟫_ℝ :=
    setIntegral_congr_fun (measurableSet_strip c) fun x hx => by
      simp only [fiberHeat, periodize_slice_of_mem hc _ s hx]
  rw [ea, eb]
  exact integral_strip_inner_planeHeat hc hu hv hup hvp hu2 hv2

theorem isSelfAdjoint_heatH (hc : 0 < c) (hθ : Measurable θ) :
    IsSelfAdjoint (heatH hc hθ : HSpace c E →L[ℝ] HSpace c E) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun f g => inner_heatH hc hθ f g

theorem adjoint_heatH (hc : 0 < c) (hθ : Measurable θ) :
    ContinuousLinearMap.adjoint (heatH hc hθ : HSpace c E →L[ℝ] HSpace c E) = heatH hc hθ :=
  isSelfAdjoint_heatH hc hθ

end UnforcedLeray.B0224
