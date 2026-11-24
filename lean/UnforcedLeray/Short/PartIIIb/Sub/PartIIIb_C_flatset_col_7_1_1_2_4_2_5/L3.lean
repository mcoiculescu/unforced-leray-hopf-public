import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_5
import UnforcedLeray.Lib.HeatR3.Admissible
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# `GradIntegrandAEMeasP`: a.e. joint measurability of the heat-gradient integrand

Source `the November 2 reference manuscript`
1684-1689, 3426-3430.

1. `planeHeat_differentiableAt`: the planar heat of a bounded measurable datum is differentiable
   (differentiation under the integral sign on the Gaussian kernel).
2. `planeHeat_param_meas`: the heat of a jointly measurable datum is jointly measurable.
3. Assembly: difference quotients of the heat converge to the cell gradient for a.e. `σ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi Metric
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Gaussian (Euc gaussKernel)

theorem gaussKernel_fderiv_bound {θ : ℝ} (hθ : 0 < θ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : Euc 2,
      ‖fderiv ℝ (gaussKernel 2 θ) z‖ ≤ A * (1 + ‖z‖) ^ (-(3 : ℝ)) := by
  obtain ⟨A, hA, h⟩ := UnforcedLeray.Heat.norm_iteratedFDeriv_gaussKernel_le_weight 2 1 hθ
    (m := 3) (by norm_num)
  refine ⟨A, hA, fun z => ?_⟩
  have := h z
  rwa [norm_iteratedFDeriv_one] at this

theorem pow_neg_three_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b ≤ 2 * a) :
    a ^ (-(3 : ℝ)) ≤ 8 * b ^ (-(3 : ℝ)) := by
  have h3 : ∀ x : ℝ, 0 < x → x ^ (-(3 : ℝ)) = (x ^ 3)⁻¹ := fun x hx => by
    rw [Real.rpow_neg hx.le]
    norm_cast
  rw [h3 a ha, h3 b hb]
  have h1 : b ^ 3 ≤ 8 * a ^ 3 := by
    calc b ^ 3 ≤ (2 * a) ^ 3 := pow_le_pow_left₀ hb.le hab 3
      _ = 8 * a ^ 3 := by ring
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h1]

theorem hasFDerivAt_gaussConvBdd {θ : ℝ} (hθ : 0 < θ) {w : Euc 2 → UnforcedLeray.B0223.MeridC}
    (hw : Measurable w) {C : ℝ} (hC : ∀ v, ‖w v‖ ≤ C) (e0 : Euc 2) :
    HasFDerivAt (fun e : Euc 2 => ∫ v : Euc 2, gaussKernel 2 θ (e - v) • w v)
      (∫ v : Euc 2, (fderiv ℝ (gaussKernel 2 θ) (e0 - v)).smulRight (w v)) e0 := by
  obtain ⟨A, hA, hAb⟩ := gaussKernel_fderiv_bound hθ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hGd : Differentiable ℝ (gaussKernel 2 θ) :=
    (UnforcedLeray.Gaussian.contDiff_gaussKernel (n := 1) θ).differentiable (by norm_num)
  have hGc : Continuous (gaussKernel 2 θ) := UnforcedLeray.Gaussian.continuous_gaussKernel θ
  have hGc' : Continuous (fderiv ℝ (gaussKernel 2 θ)) :=
    (UnforcedLeray.Gaussian.contDiff_gaussKernel (n := 1) θ).continuous_fderiv (by norm_num)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := ball e0 1)
    (F := fun e v => gaussKernel 2 θ (e - v) • w v)
    (F' := fun e v => (fderiv ℝ (gaussKernel 2 θ) (e - v)).smulRight (w v))
    (bound := fun v => C * (A * 8 * (1 + ‖e0 - v‖) ^ (-(3 : ℝ))))
    (ball_mem_nhds e0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun e => ?_
    exact ((hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).smul
      hw.aestronglyMeasurable
  · refine Integrable.mono' (((UnforcedLeray.Gaussian.integrable_gaussKernel hθ).comp_sub_left e0).const_mul C) ?_ ?_
    · exact ((hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable).smul
        hw.aestronglyMeasurable
    · refine Eventually.of_forall fun v => ?_
      rw [norm_smul, Real.norm_of_nonneg (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ _)]
      rw [mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC v) (UnforcedLeray.Gaussian.gaussKernel_nonneg hθ _)
  · exact (ContinuousLinearMap.smulRightL ℝ (Euc 2) UnforcedLeray.B0223.MeridC).aestronglyMeasurable_comp₂
      ((hGc'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) hw.aestronglyMeasurable
  · refine Eventually.of_forall fun v e he => ?_
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have h1 : ‖e0 - v‖ ≤ 1 + ‖e - v‖ := by
      calc ‖e0 - v‖ = ‖(e0 - e) + (e - v)‖ := by congr 1; abel
        _ ≤ ‖e0 - e‖ + ‖e - v‖ := norm_add_le _ _
        _ ≤ 1 + ‖e - v‖ := by
          have : dist e e0 < 1 := mem_ball.1 he
          rw [dist_eq_norm, ← norm_neg, neg_sub] at this
          linarith
    have h2 := pow_neg_three_le (a := 1 + ‖e - v‖) (b := 1 + ‖e0 - v‖) (by positivity)
      (by positivity) (by linarith [norm_nonneg (e - v)])
    calc ‖fderiv ℝ (gaussKernel 2 θ) (e - v)‖ * ‖w v‖
        ≤ (A * (1 + ‖e - v‖) ^ (-(3 : ℝ))) * C :=
          mul_le_mul (hAb _) (hC v) (norm_nonneg _) (by positivity)
      _ ≤ (A * (8 * (1 + ‖e0 - v‖) ^ (-(3 : ℝ)))) * C := by gcongr
      _ = C * (A * 8 * (1 + ‖e0 - v‖) ^ (-(3 : ℝ))) := by ring
  · have hi : Integrable (fun v : Euc 2 => (1 + ‖v‖) ^ (-(3 : ℝ))) volume :=
      integrable_one_add_norm (by simp [finrank_euclideanSpace]; norm_num)
    exact ((hi.comp_sub_left e0).const_mul (A * 8)).const_mul C |>.congr
      (Eventually.of_forall fun v => by simp only [mul_assoc])
  · refine Eventually.of_forall fun v e _ => ?_
    have := ((hGd (e - v)).hasFDerivAt.comp e ((hasFDerivAt_id e).sub_const v)).smul_const (w v)
    simpa using this

/-- The coordinate identification `Euc 2 ≃L ℝ × ℝ` underlying `planeι`. -/
def planeΛ : Euc 2 ≃L[ℝ] ℝ × ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)

theorem planeΛ_apply (e : Euc 2) : planeΛ e = UnforcedLeray.B0224.planeι e := rfl

/-- The planar heat of a bounded measurable datum is differentiable. -/
theorem planeHeat_differentiableAt {θ : ℝ} (hθ : 0 < θ)
    {u : ℝ × ℝ → UnforcedLeray.B0223.MeridC} (hu : Measurable u) {C : ℝ}
    (hC : ∀ z, ‖u z‖ ≤ C) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (UnforcedLeray.B0224.planeHeat θ u) x := by
  set w : Euc 2 → UnforcedLeray.B0223.MeridC := fun v => u (planeΛ v) with hwdef
  have hw : Measurable w := hu.comp planeΛ.continuous.measurable
  have hwC : ∀ v, ‖w v‖ ≤ C := fun v => hC _
  set h : Euc 2 → UnforcedLeray.B0223.MeridC :=
    fun e => ∫ v : Euc 2, gaussKernel 2 θ (e - v) • w v with hh
  have hdiff : Differentiable ℝ h := fun e =>
    (hasFDerivAt_gaussConvBdd hθ hw hwC e).differentiableAt
  have key : ∀ e : Euc 2, UnforcedLeray.B0224.planeHeat θ u (planeΛ e) = h e := by
    intro e
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    have h1 : ∀ y : Euc 2, u (planeΛ e - UnforcedLeray.B0224.planeι y) = w (e - y) := by
      intro y
      simp only [hwdef, map_sub]
      rfl
    simp_rw [h1]
    rw [hh]
    simp only
    rw [← integral_sub_left_eq_self (fun v : Euc 2 => gaussKernel 2 θ (e - v) • w v) volume e]
    simp
  have hfun : UnforcedLeray.B0224.planeHeat θ u = fun y => h (planeΛ.symm y) := by
    funext y
    rw [← key, ContinuousLinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (hdiff _).comp x planeΛ.symm.differentiableAt

theorem periodize_meas (c : ℝ) {Gm : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC}
    (hGm : Measurable Gm) :
    Measurable (fun q : ℝ × (ℝ × ℝ) => UnforcedLeray.B0220.periodize c Gm q) := by
  unfold UnforcedLeray.B0220.periodize
  exact hGm.comp (measurable_fst.prodMk (((UnforcedLeray.B0220.measurable_reduceIoc c).comp
    (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd)))

/-- Joint measurability of the parametric heat. -/
theorem planeHeat_param_meas (c ν s : ℝ)
    {Gm : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC} (hGm : Measurable Gm) :
    Measurable (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0224.planeHeat (ν * (s - p.1))
      (fun z => UnforcedLeray.B0220.periodize c Gm (p.1, z)) p.2) := by
  have hper := periodize_meas c hGm
  have hX : Measurable (fun p : ℝ × (ℝ × ℝ) => ∫ y : Euc 2, gaussKernel 2 (ν * (s - p.1)) y •
      UnforcedLeray.B0220.periodize c Gm (p.1, p.2 - UnforcedLeray.B0224.planeι y)) := by
    have hf : StronglyMeasurable (fun q : (ℝ × (ℝ × ℝ)) × Euc 2 =>
        gaussKernel 2 (ν * (s - q.1.1)) q.2 •
          UnforcedLeray.B0220.periodize c Gm (q.1.1, q.1.2 - UnforcedLeray.B0224.planeι q.2)) := by
      refine Measurable.stronglyMeasurable (Measurable.fun_smul ?_ ?_)
      · unfold gaussKernel
        fun_prop
      · exact hper.comp (measurable_fst.comp (measurable_fst.comp measurable_id) |>.prodMk
          ((measurable_snd.comp measurable_fst).sub
            (UnforcedLeray.B0224.measurable_planeι.comp measurable_snd)))
    exact hf.integral_prod_right'.measurable
  have hY : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      UnforcedLeray.B0220.periodize c Gm (p.1, p.2)) := hper
  have hset : MeasurableSet {p : ℝ × (ℝ × ℝ) | 0 < ν * (s - p.1)} :=
    measurableSet_lt measurable_const (measurable_const.mul (measurable_const.sub measurable_fst))
  have heq : (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0224.planeHeat (ν * (s - p.1))
      (fun z => UnforcedLeray.B0220.periodize c Gm (p.1, z)) p.2) =
      fun p => if 0 < ν * (s - p.1) then
        ∫ y : Euc 2, gaussKernel 2 (ν * (s - p.1)) y •
          UnforcedLeray.B0220.periodize c Gm (p.1, p.2 - UnforcedLeray.B0224.planeι y)
        else UnforcedLeray.B0220.periodize c Gm (p.1, p.2) := by
    funext p
    by_cases h : 0 < ν * (s - p.1)
    · rw [if_pos h, UnforcedLeray.B0224.planeHeat_of_pos h]
    · rw [if_neg h, UnforcedLeray.B0224.planeHeat_of_nonpos (not_lt.1 h)]
  rw [heq]
  exact Measurable.ite hset hX hY

/-- `GradIntegrandAEMeasP` with the hypothesis `0 < ν` that the proof needs (for `ν ≤ 0` and
`σ < s` the heat is the identity, so the integrand is the gradient of the merely measurable
representative `Gm`, whose differentiability set has no elementary measurability). -/
def GradIntegrandAEMeasPosP : Prop :=
  ∀ (c ν s : ℝ) (hc : 0 < c) (Gm Gs : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC),
    0 < ν → Measurable Gm → Gm =ᵐ[UnforcedLeray.B0220.measureH c] Gs →
    (∀ᵐ σ ∂(volume.restrict (Ioc 0 s)),
      (∀ i, ContDiff ℝ ∞ fun y : ℝ × ℝ => (Gs (σ, y)) i) ∧
      (∀ q η, Gs (σ, (q + c, η)) = Gs (σ, (q, η))) ∧
      (∃ C' : ℝ, ∀ y : ℝ × ℝ, ‖Gs (σ, y)‖ ≤ C')) →
    ∀ i j : Fin 2, AEMeasurable (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun y : ℝ × ℝ => (UnforcedLeray.B0224.planeHeat (ν * (s - p.1))
        (fun z => UnforcedLeray.B0220.periodize c Gm (p.1, z)) y) i) p.2 (B0579.dir j))
      (volume.restrict (Ioc 0 s ×ˢ (univ : Set (ℝ × ℝ))))

theorem continuous_of_coords {f : ℝ × ℝ → UnforcedLeray.B0223.MeridC}
    (h : ∀ i, ContDiff ℝ ∞ fun y : ℝ × ℝ => (f y) i) : Continuous f := by
  have h1 : Continuous (fun y : ℝ × ℝ => WithLp.ofLp (f y)) :=
    continuous_pi fun i => (h i).continuous
  have h2 := (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℂ)).comp h1
  have e : f = fun y => WithLp.toLp 2 (WithLp.ofLp (f y)) := by funext y; simp
  rw [e]
  exact h2

theorem gradIntegrand_aemeas_pos : GradIntegrandAEMeasPosP := by
  intro c ν s hc Gm Gs hν hGm hGmGs hgood i j
  set F : ℝ × (ℝ × ℝ) → ℂ := fun p => (UnforcedLeray.B0224.planeHeat (ν * (s - p.1))
    (fun z => UnforcedLeray.B0220.periodize c Gm (p.1, z)) p.2) i with hFdef
  have hFm : Measurable F :=
    ((EuclideanSpace.proj i : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ).continuous.measurable).comp
      (planeHeat_param_meas c ν s hGm)
  set v : ℝ × ℝ := B0579.dir j with hv
  set D : ℕ → ℝ × (ℝ × ℝ) → ℂ := fun n p =>
    ((1 / ((n : ℝ) + 1))⁻¹) • (F (p.1, p.2 + (1 / ((n : ℝ) + 1)) • v) - F p) with hD
  have hDm : ∀ n, Measurable (D n) := by
    intro n
    have h1 : Measurable fun p : ℝ × (ℝ × ℝ) => F (p.1, p.2 + (1 / ((n : ℝ) + 1)) • v) :=
      hFm.comp (measurable_fst.prodMk (measurable_snd.add_const _))
    exact Measurable.const_smul (h1.sub hFm) ((1 / ((n : ℝ) + 1))⁻¹)
  refine aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hDm n).aemeasurable) ?_
  have hμ : (volume : Measure (ℝ × (ℝ × ℝ))).restrict (Ioc 0 s ×ˢ (univ : Set (ℝ × ℝ))) =
      (volume.restrict (Ioc 0 s)).prod (volume.restrict (univ : Set (ℝ × ℝ))) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have hS := ae_restrict_of_ae (μ := volume) (s := Ioc 0 s) (ae_slices_of_measureH hc hGmGs)
  have hne : ∀ᵐ σ ∂(volume.restrict (Ioc 0 s)), σ ≠ s :=
    ae_restrict_of_ae ((Set.countable_singleton s).ae_notMem volume)
  have hσ : ∀ᵐ σ ∂(volume.restrict (Ioc 0 s)), ∀ x : ℝ × ℝ,
      DifferentiableAt ℝ (fun y => F (σ, y)) x := by
    filter_upwards [hgood, hS, hne, ae_restrict_mem measurableSet_Ioc] with σ hg hS' hne' hmem x
    obtain ⟨hsm, -, C', hC'⟩ := hg
    have hlt : σ < s := lt_of_le_of_ne hmem.2 hne'
    have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hlt)
    have hu : (fun z => UnforcedLeray.B0220.periodize c Gm (σ, z)) =ᵐ[volume]
        (fun z => UnforcedLeray.B0220.periodize c Gs (σ, z)) := by
      filter_upwards [hS' hmem.1] with z hz
      exact hz
    have hcont := continuous_of_coords hsm
    have hum : Measurable (fun z : ℝ × ℝ => UnforcedLeray.B0220.periodize c Gs (σ, z)) := by
      unfold UnforcedLeray.B0220.periodize
      exact (hcont.measurable).comp
        (((UnforcedLeray.B0220.measurable_reduceIoc c).comp measurable_fst).prodMk measurable_snd)
    have hfun : (fun y => F (σ, y)) = fun y => (UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z => UnforcedLeray.B0220.periodize c Gs (σ, z)) y) i := by
      funext y
      simp only [hFdef]
      rw [planeHeat_congr_pt hθ hu y]
    rw [hfun]
    have hd := planeHeat_differentiableAt hθ hum
      (C := C') (fun z => hC' _) x
    exact ((EuclideanSpace.proj i : UnforcedLeray.B0223.MeridC →L[ℂ] ℂ).restrictScalars ℝ
      |>.differentiableAt).comp x hd
  rw [hμ]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hσ] with p hp
  have hd : DifferentiableAt ℝ (fun y => F (p.1, y)) p.2 := hp p.2
  have hlin : HasDerivAt (fun t : ℝ => p.2 + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p.2
  have hder : HasDerivAt (fun t : ℝ => F (p.1, p.2 + t • v))
      (fderiv ℝ (fun y => F (p.1, y)) p.2 v) 0 := by
    have hd' : HasFDerivAt (fun y => F (p.1, y)) (fderiv ℝ (fun y => F (p.1, y)) p.2)
        (p.2 + (0 : ℝ) • v) := by
      simpa using hd.hasFDerivAt
    exact hd'.comp_hasDerivAt (0 : ℝ) hlin
  have hsl := hder.tendsto_slope_zero
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Eventually.of_forall fun n => by simp only [mem_compl_iff, mem_singleton_iff]; positivity
  have := hsl.comp ht
  refine this.congr fun n => ?_
  simp only [Function.comp, hD, zero_add, zero_smul, add_zero]

theorem gradIntegrand_aemeas : GradIntegrandAEMeasP := gradIntegrand_aemeas_pos

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
