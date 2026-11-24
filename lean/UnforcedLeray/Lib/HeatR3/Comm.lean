import UnforcedLeray.Lib.HeatR3.Continuity
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# The heat semigroup as an `L^p`-valued Gaussian average of translations (INF04 T3, BP2)


`heatLp_comm`, by bypass BP2: for `1 ≤ p < ∞` and `θ > 0`,

`e^{θΔ}u = ∫ G_θ(y) τ_{ιy}u dy`   (an `Lp E p μ`-valued Bochner integral, `heatLp_eq_integral`),

so every bounded operator commuting with the translations `τ_{ιy}` commutes with `e^{θΔ}`
(B0414(iv), tex 7336–7344: `P_σ e^{tΔ} = e^{tΔ}P_σ`; also B0420, B0688, B0727, B1025).
Scoping risk R2 (no packaged lemma turning an `Lp`-valued integral into a pointwise one) is
resolved by testing against sets of finite measure (`setIntegralLp`,
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`).
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal
open UnforcedLeray.Gaussian (Euc gaussKernel)

variable {d : ℕ} {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μ : Measure G} [SigmaFinite μ] [μ.IsAddRightInvariant]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {p : ℝ≥0∞} [hp1 : Fact (1 ≤ p)]

/-! ### Integration over a set of finite measure as a functional on `L^p` -/

theorem integrableOn_of_memLp {f : G → E} (hf : MemLp f p μ) {A : Set G} (hA : μ A < ∞) :
    IntegrableOn f A μ := by
  haveI : Fact (μ A < ∞) := ⟨hA⟩
  exact (hf.restrict A).integrable hp1.out

theorem norm_setIntegral_le_Lp (f : Lp E p μ) {A : Set G} (hA : μ A < ∞) :
    ‖∫ x in A, f x ∂μ‖ ≤ (μ A).toReal ^ (1 - 1 / p.toReal) * ‖f‖ := by
  haveI : Fact (μ A < ∞) := ⟨hA⟩
  have hint := integrableOn_of_memLp (Lp.memLp f) hA
  refine (norm_integral_le_integral_norm _).trans ?_
  have h1 : ∫ x in A, ‖f x‖ ∂μ = (eLpNorm f 1 (μ.restrict A)).toReal := by
    rw [integral_norm_eq_lintegral_enorm hint.1, eLpNorm_one_eq_lintegral_enorm]
  rw [h1]
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict A) (p := 1) (q := p)
    hp1.out (Lp.aestronglyMeasurable f).restrict
  rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one] at h2
  have h3 : eLpNorm f p (μ.restrict A) ≤ eLpNorm f p μ :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hfin : eLpNorm f p μ * μ A ^ (1 - 1 / p.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg (by
        have : 1 / p.toReal ≤ 1 := by
          rcases eq_or_ne p ∞ with rfl | hp
          · simp
          · have := ENNReal.toReal_mono hp hp1.out
            rw [ENNReal.toReal_one] at this
            exact div_le_one_of_le₀ this (by positivity)
        linarith) hA.ne)
  calc (eLpNorm f 1 (μ.restrict A)).toReal
      ≤ (eLpNorm f p μ * μ A ^ (1 - 1 / p.toReal)).toReal :=
        ENNReal.toReal_mono hfin (h2.trans (by gcongr))
    _ = (μ A).toReal ^ (1 - 1 / p.toReal) * ‖f‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_rpow, Lp.norm_def, mul_comm]

/-- `f ↦ ∫_A f dμ` as a bounded functional on `Lp E p μ` (`μ A < ∞`). -/
def setIntegralLp (A : Set G) (hA : μ A < ∞) : Lp E p μ →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x in A, f x ∂μ
      map_add' := fun f g => by
        rw [← integral_add (integrableOn_of_memLp (Lp.memLp f) hA)
          (integrableOn_of_memLp (Lp.memLp g) hA)]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← integral_smul]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f)) }
    ((μ A).toReal ^ (1 - 1 / p.toReal)) (fun f => norm_setIntegral_le_Lp f hA)

theorem setIntegralLp_apply (A : Set G) (hA : μ A < ∞) (f : Lp E p μ) :
    setIntegralLp A hA f = ∫ x in A, f x ∂μ := rfl

/-! ### The Bochner representation -/

variable [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G]

theorem continuous_translateLp (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞)
    (u : Lp E p μ) : Continuous fun y => translateLp ι hι y u :=
  Continuous.compMeasurePreservingLp (μ := μ) (ν := μ) (E := E) (p := p)
    (f := fun _ : Euc d => u) (g := shiftMap ι hι) continuous_const
    (continuous_shiftMap ι hι) (fun y => measurePreserving_sub_right μ (ι y)) hp

omit [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G] in
theorem norm_translateLp (ι : Euc d →+ G) (hι : Continuous ι) (y : Euc d) (u : Lp E p μ) :
    ‖translateLp ι hι y u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving _ _

theorem integrable_gauss_translateLp (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞)
    {θ : ℝ} (hθ : 0 < θ) (u : Lp E p μ) :
    Integrable (fun y : Euc d => gaussKernel d θ y • translateLp ι hι y u) := by
  refine ((Gaussian.integrable_gaussKernel hθ).mul_const ‖u‖).mono'
    ((Gaussian.continuous_gaussKernel θ).smul
      (continuous_translateLp ι hι hp u)).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul, norm_translateLp, Real.norm_of_nonneg (Gaussian.gaussKernel_nonneg hθ y)]

omit [μ.InnerRegularCompactLTTop] [IsLocallyFiniteMeasure μ] [R1Space G] in
/-- Fubini on `A × ℝ^d` for the heat integrand. -/
theorem setIntegral_heatConv_eq (ι : Euc d →+ G) (hι : Continuous ι) {θ : ℝ} (hθ : 0 < θ)
    (u : Lp E p μ) {A : Set G} (hA : μ A < ∞) :
    ∫ x in A, heatConv ι θ u x ∂μ =
      ∫ y : Euc d, gaussKernel d θ y • ∫ x in A, u (x - ι y) ∂μ := by
  haveI : Fact (μ A < ∞) := ⟨hA⟩
  set F : G → Euc d → E := fun x y => gaussKernel d θ y • u (x - ι y) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.restrict A).prod volume) := by
    have h := aestronglyMeasurable_heatIntegrand ι hι.measurable θ (Lp.aestronglyMeasurable u)
      (μ := μ)
    have hle : (μ.restrict A).prod (volume : Measure (Euc d)) ≤ μ.prod volume := by
      have h' := Measure.prod_restrict A (univ : Set (Euc d)) (μ := μ)
        (ν := (volume : Measure (Euc d)))
      rw [Measure.restrict_univ] at h'
      rw [h']
      exact Measure.restrict_le_self
    exact h.mono_measure hle
  have hfinA : ∫⁻ x in A, heatAbs ι θ u x ∂μ < ∞ := by
    have hm : AEStronglyMeasurable (heatAbs ι θ (u : G → E)) (μ.restrict A) :=
      (aemeasurable_heatAbs ι hι.measurable θ (Lp.aestronglyMeasurable u)).aestronglyMeasurable.restrict
    have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict A) (p := 1) (q := p)
      hp1.out hm
    rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one,
      eLpNorm_one_eq_lintegral_enorm] at h2
    simp only [enorm_eq_self] at h2
    refine h2.trans_lt (ENNReal.mul_lt_top ?_ ?_)
    · exact ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans
        (eLpNorm_heatAbs_le ι hι.measurable hθ (Lp.aestronglyMeasurable u) hp1.out)).trans_lt
        (Lp.eLpNorm_lt_top u)
    · exact ENNReal.rpow_lt_top_of_nonneg (by
        have : 1 / p.toReal ≤ 1 := by
          rcases eq_or_ne p ∞ with rfl | hp
          · simp
          · have := ENNReal.toReal_mono hp hp1.out
            rw [ENNReal.toReal_one] at this
            exact div_le_one_of_le₀ this (by positivity)
        linarith) hA.ne
  have hint : Integrable (Function.uncurry F) ((μ.restrict A).prod volume) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeas.enorm]
    refine lt_of_le_of_lt (le_of_eq ?_) hfinA
    refine lintegral_congr fun x => ?_
    simp only [Function.uncurry, hF, heatAbs, enorm_smul]
  rw [show (fun x => heatConv ι θ u x) = fun x => ∫ y : Euc d, F x y from rfl,
    integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hF]
  exact integral_smul _ _

/-- **INF04 T3 / BP2 `heatLp_eq_integral`.** For `1 ≤ p < ∞` and `θ > 0`,
`e^{θΔ}u = ∫ G_θ(y) • τ_{ιy}u dy` as an `Lp E p μ`-valued Bochner integral. -/
theorem heatLp_eq_integral (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞) {θ : ℝ}
    (hθ : 0 < θ) (u : Lp E p μ) :
    heatLp ι hι θ u = ∫ y : Euc d, gaussKernel d θ y • translateLp ι hι y u := by
  set I : Lp E p μ := ∫ y : Euc d, gaussKernel d θ y • translateLp ι hι y u with hI
  have hint := integrable_gauss_translateLp ι hι hp hθ u
  refine Lp.ext ((heatLp_rep ι hι hθ u).trans ?_)
  have hmem : MemLp (heatConv ι θ (u : G → E)) p μ :=
    memLp_heatConv ι hι.measurable hθ hp1.out (Lp.memLp u)
  refine (ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ hA => integrableOn_of_memLp hmem hA)
    (fun A _ hA => integrableOn_of_memLp (Lp.memLp I) hA) (fun A _ hA => ?_))
  rw [setIntegral_heatConv_eq ι hι hθ u hA, ← setIntegralLp_apply A hA I, hI,
    ← (setIntegralLp A hA).integral_comp_comm hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [map_smul, setIntegralLp_apply]
  congr 1
  exact (integral_congr_ae (ae_restrict_of_ae (coeFn_translateLp ι hι y u))).symm

/-- **INF04 T3 `heatLp_comm`** (BP2; B0414(iv)). For `1 ≤ p < ∞`, a bounded operator on
`Lp E p μ` that commutes with every translation `τ_{ιy}` commutes with `e^{θΔ}` for every `θ`. -/
theorem heatLp_comm (ι : Euc d →+ G) (hι : Continuous ι) (hp : p ≠ ∞)
    {T : Lp E p μ →L[ℝ] Lp E p μ}
    (hT : ∀ (y : Euc d) (u : Lp E p μ), T (translateLp ι hι y u) = translateLp ι hι y (T u))
    (θ : ℝ) : T.comp (heatLp ι hι θ) = (heatLp ι hι θ).comp T := by
  by_cases hθ : 0 < θ
  · ext1 u
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      heatLp_eq_integral ι hι hp hθ u, heatLp_eq_integral ι hι hp hθ (T u),
      ← T.integral_comp_comm (integrable_gauss_translateLp ι hι hp hθ u)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [map_smul, hT]
  · rw [heatLp_of_nonpos ι hι (not_lt.mp hθ), ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_comp]

end UnforcedLeray.Heat
