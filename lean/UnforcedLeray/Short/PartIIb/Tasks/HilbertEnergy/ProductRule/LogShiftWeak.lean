import UnforcedLeray.Short.PartIIb.Sub.T15_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogShiftTest
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTestBounds
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogAvgLocInt

/-!
# Part II-b, task `PartII-b:T15/2/8`: the shifted weak identity at a test function

Source of record: `the November 2 reference manuscript`, lines 1975-1979. The target is
the Prop `LogShiftWeak` (`Sub/T15_2.lean`, leaf `PartII-b:T15/2/8`), proved unchanged.

Proof outline. Let `G = g - u/4`, and let `G'` be a strongly measurable representative.
1. Per shift `σ`: `LogShiftTest` (`T15/2/16`) gives `∫ G(·+σ) Φ = -∫ u (∂_tΦ)(· - σ)`.
2. Fubini in `(x, σ)` on `logMeas c ⊗ volume|_{uIoc 0 h}` (two swaps, `logSh_jointA`, `logSh_jointB`).
3. FTC in `σ`: `∫_0^h ∂_tΦ(x.1 - σ, x.2) dσ = Φ x - Φ(x.1 - h, x.2)`.
4. Translation `x ↦ (x.1 + h, x.2)` for the left side.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## Measure-theoretic helpers -/

/-- The translation `x ↦ (x.1 + σ, x.2)` as a measurable embedding. -/
theorem logSh_emb (σ : ℝ) : MeasurableEmbedding (fun x : Coord => (x.1 + σ, x.2)) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.addRight σ)
    (MeasurableEquiv.refl (ℝ × ℝ))).measurableEmbedding

/-- Pointwise norm bound for a product with a real factor bounded by `C`. -/
theorem logSh_enorm_mul_real (z : ℂ) (r C : ℝ) (hr : |r| ≤ C) :
    ‖z * (r : ℂ)‖ₑ ≤ ENNReal.ofReal C * ‖z‖ₑ := by
  have hr' : ‖(r : ℂ)‖ₑ = ENNReal.ofReal |r| := by
    rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← Real.enorm_eq_ofReal_abs, enorm_eq_nnnorm]
  rw [enorm_mul, hr', mul_comm (ENNReal.ofReal C)]
  gcongr

/-- Integrability on a product from an a.e. bound on the inner `x`-integrals (Tonelli). -/
theorem logSh_integrable_of_ae_bound {μ : Measure Coord} {ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {F : Coord × ℝ → ℂ} (hF : AEStronglyMeasurable F (μ.prod ν)) {A : ℝ≥0∞} (hA : A < ⊤)
    (hν : ν univ < ⊤) (hbd : ∀ᵐ σ ∂ν, ∫⁻ x, ‖F (x, σ)‖ₑ ∂μ ≤ A) : Integrable F (μ.prod ν) := by
  refine ⟨hF, ?_⟩
  show ∫⁻ z, ‖F z‖ₑ ∂(μ.prod ν) < ⊤
  rw [lintegral_prod_symm _ hF.aemeasurable.enorm]
  calc ∫⁻ σ, ∫⁻ x, ‖F (x, σ)‖ₑ ∂μ ∂ν ≤ ∫⁻ _σ, A ∂ν := lintegral_mono_ae hbd
    _ = A * ν univ := lintegral_const A
    _ < ⊤ := ENNReal.mul_lt_top hA hν

/-- Swapping an interval integral in `σ` with an integral in `x`. -/
theorem logSh_swap {μ : Measure Coord} [SFinite μ] (h : ℝ) (F : Coord → ℝ → ℂ)
    (hF : Integrable (fun p : Coord × ℝ => F p.1 p.2) (μ.prod (volume.restrict (Set.uIoc 0 h)))) :
    ∫ x, (∫ σ in (0:ℝ)..h, F x σ) ∂μ = ∫ σ in (0:ℝ)..h, ∫ x, F x σ ∂μ := by
  have hswap := integral_integral_swap (μ := μ) (ν := volume.restrict (Set.uIoc 0 h))
    (f := fun x σ => F x σ) hF
  simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_smul]
  rw [hswap]

/-! ## Fundamental theorem of calculus in the `σ`-variable -/

theorem logSh_ftc {Φ : Coord → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (x : Coord) (h : ℝ) :
    ∫ σ in (0:ℝ)..h, cpd 0 Φ (x.1 - σ, x.2) = Φ x - Φ (x.1 - h, x.2) := by
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hderiv : ∀ σ ∈ uIcc (0:ℝ) h,
      HasDerivAt (fun σ : ℝ => Φ (x.1 - σ, x.2)) (-cpd 0 Φ (x.1 - σ, x.2)) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => x.1 - σ) (-1) σ := by
      simpa using (hasDerivAt_id σ).const_sub x.1
    have hγ : HasDerivAt (fun σ : ℝ => ((x.1 - σ, x.2) : Coord))
        (((-1 : ℝ), (0 : ℝ × ℝ)) : Coord) σ :=
      h1.prodMk (hasDerivAt_const σ x.2)
    have hc := (hdiff (x.1 - σ, x.2)).hasFDerivAt.comp_hasDerivAt σ hγ
    have hv : (((-1 : ℝ), (0 : ℝ × ℝ)) : Coord) = -cdir 0 := by
      ext <;> simp [cdir]
    rw [hv, map_neg] at hc
    exact hc
  have hcont : Continuous (fun σ : ℝ => cpd 0 Φ (x.1 - σ, x.2)) :=
    (logTestBounds_cpd_continuous hΦ).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const)
  have hint : IntervalIntegrable (fun σ : ℝ => -cpd 0 Φ (x.1 - σ, x.2)) volume 0 h :=
    hcont.neg.intervalIntegrable _ _
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg] at key
  simp only [sub_zero, Prod.mk.eta] at key
  linarith

/-! ## Joint integrability -/

/-- Joint integrability of `(x, σ) ↦ G'(x.1 + σ, x.2) Φ(x)` for `G' ∈ L²` and `Φ` bounded,
vanishing outside `{|t| ≤ T, |η| ≤ L}`. -/
theorem logSh_jointA (c h : ℝ) {G' : Coord → ℂ} (hG'sm : StronglyMeasurable G')
    (hG'L2 : MemLp G' 2 (logMeas c)) {Φ : Coord → ℝ} (hΦc : Continuous Φ) {C T L : ℝ}
    (hC : ∀ x, |Φ x| ≤ C) (hz : ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → Φ x = 0) :
    Integrable (fun p : Coord × ℝ => G' (p.1.1 + p.2, p.1.2) * ((Φ p.1 : ℝ) : ℂ))
      ((logMeas c).prod (volume.restrict (Set.uIoc 0 h))) := by
  have hmeasΨ : Measurable (fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) := by fun_prop
  have hG'meas : Measurable G' := hG'sm.measurable
  have hK'm : MeasurableSet {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} :=
    logAL_box_meas _ _
  have hK'fin : logMeas c {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} < ⊤ :=
    logAL_box_lt_top c _ _
  have hfm : Measurable (Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
      (fun y : Coord => ‖G' y‖ₑ)) :=
    hG'meas.enorm.indicator hK'm
  haveI : IsFiniteMeasure ((logMeas c).restrict {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK'fin⟩
  have hM : ∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖G' y‖ₑ ∂(logMeas c) < ⊤ :=
    (MemLp.integrable (one_le_two : (1 : ℝ≥0∞) ≤ 2)
      (MemLp.restrict {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} hG'L2)).2
  have hνfin : (volume.restrict (Set.uIoc 0 h)) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top
  have hpt : ∀ σ : ℝ, |σ| ≤ |h| → ∀ x : Coord,
      ‖G' (x.1 + σ, x.2) * ((Φ x : ℝ) : ℂ)‖ₑ ≤
        ENNReal.ofReal C * Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
          (fun y : Coord => ‖G' y‖ₑ) (x.1 + σ, x.2) := by
    intro σ hσ x
    by_cases hx : T < |x.1| ∨ L < |x.2.2|
    · rw [hz x hx]
      simp
    · push_neg at hx
      have hmem : (x.1 + σ, x.2) ∈ {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} := by
        refine ⟨?_, hx.2⟩
        linarith [abs_add_le x.1 σ, hx.1]
      rw [Set.indicator_of_mem hmem]
      exact logSh_enorm_mul_real _ _ _ (hC x)
  have hA : ∀ σ ∈ Set.uIoc 0 h,
      ∫⁻ x, ‖G' (x.1 + σ, x.2) * ((Φ x : ℝ) : ℂ)‖ₑ ∂(logMeas c)
        ≤ ENNReal.ofReal C * ∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖G' y‖ₑ ∂(logMeas c) := by
    intro σ hσ
    have hσ' := logAL_abs_le_of_mem_uIoc h σ hσ
    calc ∫⁻ x, ‖G' (x.1 + σ, x.2) * ((Φ x : ℝ) : ℂ)‖ₑ ∂(logMeas c)
        ≤ ∫⁻ x, ENNReal.ofReal C * Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
            (fun y : Coord => ‖G' y‖ₑ) (x.1 + σ, x.2) ∂(logMeas c) :=
          lintegral_mono (fun x => hpt σ hσ' x)
      _ = ENNReal.ofReal C * ∫⁻ y, Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
            (fun y : Coord => ‖G' y‖ₑ) y ∂(logMeas c) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact (logAL_measurePreserving c σ).lintegral_comp hfm
      _ = ENNReal.ofReal C * ∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖G' y‖ₑ
            ∂(logMeas c) := by
          rw [lintegral_indicator hK'm]
  have hF : AEStronglyMeasurable (fun p : Coord × ℝ => G' (p.1.1 + p.2, p.1.2) * ((Φ p.1 : ℝ) : ℂ))
      ((logMeas c).prod (volume.restrict (Set.uIoc 0 h))) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hG'meas.comp hmeasΨ).aestronglyMeasurable
    · exact (Complex.continuous_ofReal.comp (hΦc.comp continuous_fst)).aestronglyMeasurable
  refine logSh_integrable_of_ae_bound (A := ENNReal.ofReal C * ∫⁻ y in
      {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖G' y‖ₑ ∂(logMeas c)) hF
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM) hνfin ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with σ hσ
  exact (hA σ hσ).trans_eq' rfl

/-- Joint integrability of `(x, σ) ↦ u(x) D(x.1 - σ, x.2)` for `u ∈ L²` and `D` bounded, vanishing
outside `{|t| ≤ T, |η| ≤ L}`. -/
theorem logSh_jointB (c h : ℝ) {u : Coord → ℂ} (hu : MemLp u 2 (logMeas c))
    {D : Coord → ℝ} (hDc : Continuous D) {C T L : ℝ} (hC : ∀ x, |D x| ≤ C)
    (hz : ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → D x = 0) :
    Integrable (fun p : Coord × ℝ => u p.1 * ((D (p.1.1 - p.2, p.1.2) : ℝ) : ℂ))
      ((logMeas c).prod (volume.restrict (Set.uIoc 0 h))) := by
  have hK'm : MeasurableSet {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} := logAL_box_meas _ _
  have hK'fin : logMeas c {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} < ⊤ :=
    logAL_box_lt_top c _ _
  haveI : IsFiniteMeasure ((logMeas c).restrict {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK'fin⟩
  have hM : ∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖u y‖ₑ ∂(logMeas c) < ⊤ :=
    (MemLp.integrable (one_le_two : (1 : ℝ≥0∞) ≤ 2)
      (MemLp.restrict {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L} hu)).2
  have hνfin : (volume.restrict (Set.uIoc 0 h)) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono Set.uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top
  have hpt : ∀ σ : ℝ, |σ| ≤ |h| → ∀ x : Coord,
      ‖u x * ((D (x.1 - σ, x.2) : ℝ) : ℂ)‖ₑ ≤
        ENNReal.ofReal C * Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
          (fun y : Coord => ‖u y‖ₑ) x := by
    intro σ hσ x
    by_cases hx : x ∈ {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
    · rw [Set.indicator_of_mem hx]
      exact logSh_enorm_mul_real _ _ _ (hC _)
    · rw [Set.indicator_of_notMem hx]
      have hx' : ¬ (|x.1| ≤ T + |h| ∧ |x.2.2| ≤ L) := hx
      have hD0 : D (x.1 - σ, x.2) = 0 := by
        apply hz
        by_cases h2 : L < |x.2.2|
        · exact Or.inr h2
        · have h3 : T + |h| < |x.1| := by
            by_contra h3
            exact hx' ⟨not_lt.mp h3, not_lt.mp h2⟩
          left
          have h4 := abs_sub_abs_le_abs_sub x.1 σ
          show T < |x.1 - σ|
          linarith
      rw [hD0]
      simp
  have hA : ∀ σ ∈ Set.uIoc 0 h,
      ∫⁻ x, ‖u x * ((D (x.1 - σ, x.2) : ℝ) : ℂ)‖ₑ ∂(logMeas c)
        ≤ ENNReal.ofReal C * ∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L},
            ‖u y‖ₑ ∂(logMeas c) := by
    intro σ hσ
    have hσ' := logAL_abs_le_of_mem_uIoc h σ hσ
    calc ∫⁻ x, ‖u x * ((D (x.1 - σ, x.2) : ℝ) : ℂ)‖ₑ ∂(logMeas c)
        ≤ ∫⁻ x, ENNReal.ofReal C * Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
            (fun y : Coord => ‖u y‖ₑ) x ∂(logMeas c) :=
          lintegral_mono (fun x => hpt σ hσ' x)
      _ = ENNReal.ofReal C * ∫⁻ y, Set.indicator {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}
            (fun y : Coord => ‖u y‖ₑ) y ∂(logMeas c) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C * ∫⁻ y in {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L},
            ‖u y‖ₑ ∂(logMeas c) := by
          rw [lintegral_indicator hK'm]
  have hcont : Continuous (fun p : Coord × ℝ => (p.1.1 - p.2, p.1.2)) :=
    ((continuous_fst.comp continuous_fst).sub continuous_snd).prodMk
      (continuous_snd.comp continuous_fst)
  have hF : AEStronglyMeasurable
      (fun p : Coord × ℝ => u p.1 * ((D (p.1.1 - p.2, p.1.2) : ℝ) : ℂ))
      ((logMeas c).prod (volume.restrict (Set.uIoc 0 h))) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact hu.aestronglyMeasurable.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_fst (μ := logMeas c) (ν := volume.restrict (Set.uIoc 0 h)))
    · exact (Complex.continuous_ofReal.comp (hDc.comp hcont)).aestronglyMeasurable
  refine logSh_integrable_of_ae_bound (A := ENNReal.ofReal C * ∫⁻ y in
      {x : Coord | |x.1| ≤ T + |h| ∧ |x.2.2| ≤ L}, ‖u y‖ₑ ∂(logMeas c)) hF
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM) hνfin ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with σ hσ
  exact hA σ hσ

/-- The a.e. identity of a function and its strongly measurable representative along all shifts. -/
theorem logSh_slice (c : ℝ) (G G' : Coord → ℂ) (hGG' : G =ᵐ[logMeas c] G') :
    ∀ᵐ x ∂(logMeas c), ∀ᵐ σ ∂(volume : Measure ℝ), G (x.1 + σ, x.2) = G' (x.1 + σ, x.2) := by
  have hmeasΨ : Measurable (fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) := by fun_prop
  have hN : logMeas c {y : Coord | ¬ (G y = G' y)} = 0 := ae_iff.mp hGG'
  obtain ⟨E, hNE, hEm, hE0⟩ := exists_measurable_superset_of_null hN
  have hprod0 : ((logMeas c).prod (volume : Measure ℝ))
      ((fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) ⁻¹' E) = 0 := by
    rw [Measure.prod_apply_symm (hEm.preimage hmeasΨ)]
    have hsl : ∀ σ : ℝ, logMeas c ((fun x : Coord => (x, σ)) ⁻¹'
        ((fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) ⁻¹' E)) = 0 := by
      intro σ
      have hpre : (fun x : Coord => (x, σ)) ⁻¹'
          ((fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) ⁻¹' E) =
            (fun x : Coord => (x.1 + σ, x.2)) ⁻¹' E := rfl
      rw [hpre, ← Measure.map_apply (logAL_measurePreserving c σ).measurable hEm,
        (logAL_measurePreserving c σ).map_eq]
      exact hE0
    simp only [hsl, lintegral_zero]
  have hae : ∀ᵐ z ∂((logMeas c).prod (volume : Measure ℝ)),
      z ∉ (fun p : Coord × ℝ => (p.1.1 + p.2, p.1.2)) ⁻¹' E := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hprod0
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with x hx
  filter_upwards [hx] with σ hσ
  by_contra hne
  have hmem : (x.1 + σ, x.2) ∈ {y : Coord | ¬ (G y = G' y)} := hne
  exact hσ (hNE hmem)

/-- Translates of a logarithmic test are logarithmic tests. -/
theorem logSh_shiftTest {c : ℝ} {Φ : Coord → ℝ} (hΦ : LogTest c Φ) (σ : ℝ) :
    LogTest c (fun y : Coord => Φ (y.1 - σ, y.2)) := by
  obtain ⟨T, L, hTL⟩ := hΦ.compact
  refine ⟨?_, ?_, ?_⟩
  · have hs : ContDiff ℝ ∞ (fun y : Coord => (y.1 - σ, y.2)) := by fun_prop
    exact hΦ.smooth.comp hs
  · intro y
    exact hΦ.periodic (y.1 - σ, y.2)
  · refine ⟨T + |σ|, L, fun y hy => ?_⟩
    apply hTL
    rcases hy with h | h
    · left
      have h1 := abs_sub_abs_le_abs_sub y.1 σ
      show T < |y.1 - σ|
      linarith
    · right
      exact h

/-! ## The main statement -/

theorem logShiftWeak : UnforcedLeray.Short.IIb.LogShiftWeak := by
  intro c u g hc hu hg hweak h Φ hΦ
  obtain ⟨T, L, hTL⟩ := hΦ.compact
  have hΦc : Continuous Φ := hΦ.smooth.continuous
  obtain ⟨⟨C₀, hC₀⟩, ⟨C₁, hC₁⟩, hintΦ⟩ := logTestBounds c Φ hc hΦ
  have hDc : Continuous (cpd 0 Φ) := logTestBounds_cpd_continuous hΦ.smooth
  have hDz : ∀ x : Coord, (T < |x.1| ∨ L < |x.2.2|) → cpd 0 Φ x = 0 :=
    logTestBounds_cpd_zero hTL
  have hI1 : Integrable (fun x : Coord => u x * (Φ x : ℂ)) (logMeas c) := (hintΦ u hu).1
  have hsh := logSh_shiftTest hΦ h
  have hI2 : Integrable (fun x : Coord => u x * ((Φ (x.1 - h, x.2) : ℝ) : ℂ)) (logMeas c) :=
    ((logTestBounds c _ hc hsh).2.2 u hu).1
  have hI2' : Integrable (fun x : Coord => u (x.1 + h, x.2) * (Φ x : ℂ)) (logMeas c) := by
    have key := ((logAL_measurePreserving c h).integrable_comp_emb (logSh_emb h)).2 hI2
    refine key.congr (ae_of_all _ fun x => ?_)
    simp only [Function.comp_apply, add_sub_cancel_right, Prod.mk.eta]
  have hT : ∫ x, u (x.1 + h, x.2) * (Φ x : ℂ) ∂(logMeas c)
      = ∫ y, u y * ((Φ (y.1 - h, y.2) : ℝ) : ℂ) ∂(logMeas c) := by
    have := (logAL_measurePreserving c h).integral_comp (logSh_emb h)
      (fun y : Coord => u y * ((Φ (y.1 - h, y.2) : ℝ) : ℂ))
    rw [← this]
    congr 1
    funext x
    simp only [add_sub_cancel_right, Prod.mk.eta]
  -- the `G = g - u/4` part
  have hu4 : MemLp (fun x : Coord => u x / 4) 2 (logMeas c) := by
    have h4 := hu.const_mul (4⁻¹ : ℂ)
    simpa only [div_eq_inv_mul] using h4
  have hGmem : MemLp (fun x : Coord => g x - u x / 4) 2 (logMeas c) := hg.sub hu4
  obtain ⟨G', hG'sm, hGG'⟩ : ∃ G' : Coord → ℂ, StronglyMeasurable G' ∧
      (fun x : Coord => g x - u x / 4) =ᵐ[logMeas c] G' :=
    ⟨hGmem.aestronglyMeasurable.mk _, hGmem.aestronglyMeasurable.stronglyMeasurable_mk,
      hGmem.aestronglyMeasurable.ae_eq_mk⟩
  have hG'L2 : MemLp G' 2 (logMeas c) := MemLp.ae_eq hGG' hGmem
  have hslice := logSh_slice c (fun x : Coord => g x - u x / 4) G' hGG'
  have hae_sh : ∀ σ : ℝ, ∀ᵐ x ∂(logMeas c),
      G' (x.1 + σ, x.2) = g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4 := by
    intro σ
    exact (logAL_measurePreserving c σ).quasiMeasurePreserving.ae
      (p := fun y => G' y = g y - u y / 4) hGG'.symm
  have hper : ∀ σ : ℝ, ∫ x, G' (x.1 + σ, x.2) * (Φ x : ℂ) ∂(logMeas c)
      = -∫ x, u x * ((cpd 0 Φ (x.1 - σ, x.2) : ℝ) : ℂ) ∂(logMeas c) := by
    intro σ
    have hcongr : (fun x : Coord => G' (x.1 + σ, x.2) * (Φ x : ℂ)) =ᵐ[logMeas c]
        (fun x : Coord => (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4) * (Φ x : ℂ)) := by
      filter_upwards [hae_sh σ] with x hx
      rw [hx]
    exact (integral_congr_ae hcongr).trans (logShiftTest c u g hc hu hg hweak σ Φ hΦ)
  have hJA : Integrable (fun p : Coord × ℝ => G' (p.1.1 + p.2, p.1.2) * ((Φ p.1 : ℝ) : ℂ))
      ((logMeas c).prod (volume.restrict (Set.uIoc 0 h))) :=
    logSh_jointA c h hG'sm hG'L2 hΦc hC₀ hTL
  have hJB : Integrable (fun p : Coord × ℝ => u p.1 * ((cpd 0 Φ (p.1.1 - p.2, p.1.2) : ℝ) : ℂ))
      ((logMeas c).prod (volume.restrict (Set.uIoc 0 h))) :=
    logSh_jointB c h hu hDc hC₁ hDz
  have hswA : ∫ x, (∫ σ in (0:ℝ)..h, G' (x.1 + σ, x.2) * (Φ x : ℂ)) ∂(logMeas c)
      = ∫ σ in (0:ℝ)..h, ∫ x, G' (x.1 + σ, x.2) * (Φ x : ℂ) ∂(logMeas c) :=
    logSh_swap h (fun x σ => G' (x.1 + σ, x.2) * (Φ x : ℂ)) hJA
  have hswB : ∫ x, (∫ σ in (0:ℝ)..h, u x * ((cpd 0 Φ (x.1 - σ, x.2) : ℝ) : ℂ)) ∂(logMeas c)
      = ∫ σ in (0:ℝ)..h, ∫ x, u x * ((cpd 0 Φ (x.1 - σ, x.2) : ℝ) : ℂ) ∂(logMeas c) :=
    logSh_swap h (fun x σ => u x * ((cpd 0 Φ (x.1 - σ, x.2) : ℝ) : ℂ)) hJB
  have hR1 : ∫ x, (∫ σ in (0:ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) * (Φ x : ℂ)
      ∂(logMeas c) = ∫ x, (∫ σ in (0:ℝ)..h, G' (x.1 + σ, x.2) * (Φ x : ℂ)) ∂(logMeas c) := by
    refine integral_congr_ae ?_
    filter_upwards [hslice] with x hx
    rw [← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hx] with σ hσ
    intro _
    rw [show (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4) = G' (x.1 + σ, x.2) from hσ]
  have hI : ∀ x : Coord, ∫ σ in (0:ℝ)..h, u x * ((cpd 0 Φ (x.1 - σ, x.2) : ℝ) : ℂ)
      = u x * ((Φ x - Φ (x.1 - h, x.2) : ℝ) : ℂ) := by
    intro x
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      logSh_ftc hΦ.smooth x h]
  have hRfin : ∫ x, (∫ σ in (0:ℝ)..h, (g (x.1 + σ, x.2) - u (x.1 + σ, x.2) / 4)) * (Φ x : ℂ)
      ∂(logMeas c) = -∫ x, u x * ((Φ x - Φ (x.1 - h, x.2) : ℝ) : ℂ) ∂(logMeas c) := by
    rw [hR1, hswA]
    simp only [hper]
    rw [intervalIntegral.integral_neg, ← hswB]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun x => hI x)
  have hsplit : ∫ x, u x * ((Φ x - Φ (x.1 - h, x.2) : ℝ) : ℂ) ∂(logMeas c)
      = ∫ x, u x * (Φ x : ℂ) ∂(logMeas c) - ∫ x, u x * ((Φ (x.1 - h, x.2) : ℝ) : ℂ) ∂(logMeas c) := by
    rw [← integral_sub hI1 hI2]
    congr 1
    funext x
    push_cast
    ring
  have hLHS : ∫ x, (u (x.1 + h, x.2) - u x) * (Φ x : ℂ) ∂(logMeas c)
      = ∫ x, u (x.1 + h, x.2) * (Φ x : ℂ) ∂(logMeas c) - ∫ x, u x * (Φ x : ℂ) ∂(logMeas c) := by
    rw [← integral_sub hI2' hI1]
    congr 1
    funext x
    ring
  rw [hLHS, hT, hRfin, hsplit]
  ring

end UnforcedLeray.Short.IIb
