import UnforcedLeray.Short.PartI.Sub.T02_2_3
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressureBounded.SlicePartials
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Part I, task `PartI:T02/2/3`, leaf `pbParamDerivC1`: differentiation under a time integral

Source of record: `the November 2 reference manuscript`, line 447 (the decaying
pressure gauge is used here; the time-integrated pressure).  Target `pbParamDerivC1 :
PbParamDerivC1` (definition in `Sub/T02_2_3.lean`): if `(σ, z) ↦ F σ z` is `C¹` on `[0,T] × ℝ²`
with `T > 0`, and `a, b ∈ [0,T]`, then `z ↦ ∫_a^b F σ z dσ` is `C¹`, and its `q`- and
`η`-partials are the integrals of the partials of `F σ`.

Proof.  Write `S = [0,T] × ℝ²`, `H (σ, z) = F σ z` and `Φ p = (fderivWithin ℝ H S p).comp inr`.
* For `σ ∈ [0,T]` the slice `F σ` is `C¹` on the plane, and `fderiv ℝ (F σ) z = Φ (σ, z)`
  (`pbPD_fderiv_eq`: the within-`S` derivative of `H` along the path `w ↦ (σ, w)`, which stays in
  `S`).  `Φ` is continuous on `S` (`ContDiffOn.continuousOn_fderivWithin`,
  `ContinuousOn.clm_comp`).
* Dominated differentiation (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`) on
  the ball `closedBall z₀ 1`, with the constant bound `sup ‖Φ‖` over the compact set
  `uIcc a b ×ˢ closedBall z₀ 1`, gives `HasFDerivAt P (∫ σ, fderiv ℝ (F σ) z₀) z₀`.
* The clamped integrand `z ↦ ∫ σ, Φ (max 0 (min σ T), z)` is continuous (the clamp is continuous
  into `[0,T]` and equals the identity on `[a,b]`), so `fderiv ℝ P` is continuous and `P` is `C¹`
  (`contDiff_one_iff_fderiv`).
* The partials: `Cyl.partialQ_eq_fderiv`, `ContinuousLinearMap.intervalIntegral_apply` and
  `intervalIntegral.integral_congr` on `uIcc a b` (where the slice derivatives are the partials).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The clamp `σ ↦ max 0 (min σ T)` takes values in `[0,T]` when `0 < T`. -/
theorem pbPD_clamp_mem {T : ℝ} (hT : 0 < T) (σ : ℝ) : max 0 (min σ T) ∈ Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩

/-- The clamp is the identity on `[0,T]`. -/
theorem pbPD_clamp_eq {T σ : ℝ} (h : σ ∈ Icc (0 : ℝ) T) : max 0 (min σ T) = σ := by
  rw [min_eq_left h.2, max_eq_right h.1]

/-- A slice of a `C¹` family on `[0,T] × ℝ²` is `C¹` on the plane. -/
theorem pbPD_slice_contDiff {F : ℝ → Plane → ℝ} {T s : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    (hF : ContDiffOn ℝ 1 (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)) :
    ContDiff ℝ 1 (F s) := by
  have h1 : ContDiffOn ℝ 1 ((fun x : ℝ × Plane => F x.1 x.2) ∘ (fun z : Plane => (s, z)))
      univ :=
    hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun z _ => ⟨hs, mem_univ z⟩)
  exact contDiffOn_univ.mp h1

/-- The slice derivative is the within-`[0,T] × ℝ²` derivative of `H` composed with the
inclusion of the second factor. -/
theorem pbPD_fderiv_eq {F : ℝ → Plane → ℝ} {T : ℝ}
    (hF : ContDiffOn ℝ 1 (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (z : Plane) :
    fderiv ℝ (F s) z =
      (fderivWithin ℝ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ) (s, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ Plane) := by
  have hd : DifferentiableWithinAt ℝ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)
      (s, z) :=
    (hF.differentiableOn (by simp)) _ ⟨hs, mem_univ z⟩
  have hpath : HasFDerivAt (fun w : Plane => ((s, w) : ℝ × Plane))
      (ContinuousLinearMap.inr ℝ ℝ Plane) z :=
    hasFDerivAt_prodMk_right s z
  have hmaps : MapsTo (fun w : Plane => ((s, w) : ℝ × Plane)) univ (Icc 0 T ×ˢ univ) :=
    fun w _ => ⟨hs, mem_univ w⟩
  have hc := HasFDerivWithinAt.comp (x := z) hd.hasFDerivWithinAt hpath.hasFDerivWithinAt hmaps
  have key := hasFDerivWithinAt_univ.mp hc
  exact key.fderiv

/-- `Φ p = (fderivWithin ℝ H S p).comp inr` is continuous on `S = [0,T] × ℝ²`. -/
theorem pbPD_Phi_cont {F : ℝ → Plane → ℝ} {T : ℝ} (hT : 0 < T)
    (hF : ContDiffOn ℝ 1 (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × Plane =>
      (fderivWithin ℝ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ) p).comp
        (ContinuousLinearMap.inr ℝ ℝ Plane)) (Icc 0 T ×ˢ univ) := by
  have hS : UniqueDiffOn ℝ (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  exact (hF.continuousOn_fderivWithin hS le_rfl).clm_comp continuousOn_const

/-- A slice `σ ↦ F σ z` is continuous on `[0,T]`. -/
theorem pbPD_cont_slice {F : ℝ → Plane → ℝ} {T : ℝ}
    (hF : ContDiffOn ℝ 1 (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)) (z : Plane) :
    ContinuousOn (fun σ : ℝ => F σ z) (Icc 0 T) := by
  have hc : Continuous (fun σ : ℝ => ((σ, z) : ℝ × Plane)) :=
    continuous_id.prodMk continuous_const
  refine hF.continuousOn.comp hc.continuousOn ?_
  intro σ hσ
  exact ⟨hσ, mem_univ z⟩

/-- The slice derivative `σ ↦ fderiv ℝ (F σ) z` is continuous on `[0,T]`. -/
theorem pbPD_cont_fderiv {F : ℝ → Plane → ℝ} {T : ℝ} (hT : 0 < T)
    (hF : ContDiffOn ℝ 1 (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)) (z : Plane) :
    ContinuousOn (fun σ : ℝ => fderiv ℝ (F σ) z) (Icc 0 T) := by
  have hc : Continuous (fun σ : ℝ => ((σ, z) : ℝ × Plane)) :=
    continuous_id.prodMk continuous_const
  have h2 : ContinuousOn (fun σ : ℝ =>
      (fderivWithin ℝ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ) (σ, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ Plane)) (Icc 0 T) :=
    (pbPD_Phi_cont hT hF).comp hc.continuousOn (fun σ hσ => ⟨hσ, mem_univ z⟩)
  refine h2.congr ?_
  intro σ hσ
  exact pbPD_fderiv_eq hF hσ z

/-- **Differentiation under a time integral, first order** (leaf of `PbTimeAvgSmooth`, source line
447): if `(σ, z) ↦ F σ z` is `C¹` on `[0,T] × ℝ²` (`T > 0`) and `a, b ∈ [0,T]`, then
`z ↦ ∫_a^b F σ z dσ` is `C¹`, and its partials are the integrals of the partials of `F σ`.
Proof: dominated differentiation of the integral on `closedBall z₀ 1` (bound `sup ‖Φ‖` over the
compact `uIcc a b ×ˢ closedBall z₀ 1`), continuity of the clamped integrand, then the partial
identities through `Cyl.partialQ_eq_fderiv` and `Cyl.partialEta_eq_fderiv`. -/
theorem pbParamDerivC1 : PbParamDerivC1 := by
  intro T F a b hT ha hb hF
  have hab : uIcc a b ⊆ Icc (0 : ℝ) T := uIcc_subset_Icc ha hb
  have hIoc : uIoc a b ⊆ Icc (0 : ℝ) T := uIoc_subset_uIcc.trans hab
  have hdiffF : ∀ σ ∈ Icc (0 : ℝ) T, Differentiable ℝ (F σ) := fun σ hσ =>
    (pbPD_slice_contDiff hσ hF).differentiable (by simp)
  -- the integral is differentiable, with derivative the integral of the slice derivatives
  have hP : ∀ z0 : Plane, HasFDerivAt (fun z => ∫ σ in a..b, F σ z)
      (∫ σ in a..b, fderiv ℝ (F σ) z0) z0 := by
    intro z0
    obtain ⟨C, hC⟩ := (isCompact_uIcc.prod (isCompact_closedBall z0 1)).exists_bound_of_continuousOn
      ((pbPD_Phi_cont hT hF).mono (Set.prod_mono hab (subset_univ _)))
    have hbound : ∀ t ∈ uIcc a b, ∀ x ∈ Metric.closedBall z0 1, ‖fderiv ℝ (F t) x‖ ≤ C := by
      intro t ht x hx
      rw [pbPD_fderiv_eq hF (hab ht) x]
      exact hC (t, x) ⟨ht, hx⟩
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun z σ => F σ z) (F' := fun z σ => fderiv ℝ (F σ) z) (bound := fun _ => C)
      (Metric.closedBall_mem_nhds z0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x =>
        ((pbPD_cont_slice hF x).mono hIoc).aestronglyMeasurable measurableSet_uIoc
    · exact ContinuousOn.intervalIntegrable ((pbPD_cont_slice hF z0).mono hab)
    · exact ((pbPD_cont_fderiv hT hF z0).mono hIoc).aestronglyMeasurable measurableSet_uIoc
    · exact ae_of_all _ fun t ht x hx => hbound t (uIoc_subset_uIcc ht) x hx
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun t ht x _ => (hdiffF t (hIoc ht) x).hasFDerivAt
  have hPdiff : Differentiable ℝ (fun z => ∫ σ in a..b, F σ z) :=
    fun z => (hP z).differentiableAt
  have hfd : ∀ z : Plane, fderiv ℝ (fun w => ∫ σ in a..b, F σ w) z =
      ∫ σ in a..b, fderiv ℝ (F σ) z :=
    fun z => (hP z).fderiv
  -- the slice derivatives agree with the clamped (continuous) family on `[a,b]`
  have hcongr : ∀ z : Plane, (∫ σ in a..b, fderiv ℝ (F σ) z) =
      ∫ σ in a..b, (fderivWithin ℝ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)
        (max 0 (min σ T), z)).comp (ContinuousLinearMap.inr ℝ ℝ Plane) := by
    intro z
    refine intervalIntegral.integral_congr ?_
    intro σ hσ
    have hσI : σ ∈ Icc (0 : ℝ) T := hab hσ
    simp only [pbPD_clamp_eq hσI]
    exact pbPD_fderiv_eq hF hσI z
  -- continuity of the derivative of the integral
  have hcont : Continuous (fun z : Plane => ∫ σ in a..b, fderiv ℝ (F σ) z) := by
    have h1 : Continuous (fun p : ℝ × Plane =>
        (fderivWithin ℝ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)
          (max 0 (min p.1 T), p.2)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) := by
      have hcl : Continuous (fun p : ℝ × Plane => ((max 0 (min p.1 T), p.2) : ℝ × Plane)) := by
        fun_prop
      exact (pbPD_Phi_cont hT hF).comp_continuous hcl fun p =>
        ⟨pbPD_clamp_mem hT p.1, mem_univ _⟩
    have hsw : Continuous (fun p : Plane × ℝ => ((p.2, p.1) : ℝ × Plane)) :=
      continuous_snd.prodMk continuous_fst
    have hU : Continuous (Function.uncurry fun (z : Plane) (σ : ℝ) =>
        (fderivWithin ℝ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)
          (max 0 (min σ T), z)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)) :=
      h1.comp hsw
    have hfun : (fun z : Plane => ∫ σ in a..b, fderiv ℝ (F σ) z) = fun z : Plane =>
        ∫ σ in a..b, (fderivWithin ℝ (fun x : ℝ × Plane => F x.1 x.2) (Icc 0 T ×ˢ univ)
          (max 0 (min σ T), z)).comp (ContinuousLinearMap.inr ℝ ℝ Plane) :=
      funext hcongr
    rw [hfun]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hU a b
  -- first conjunct: the integral is C¹
  have hC1 : ContDiff ℝ 1 (fun z => ∫ σ in a..b, F σ z) := by
    refine contDiff_one_iff_fderiv.mpr ⟨hPdiff, ?_⟩
    have hfd' : fderiv ℝ (fun w => ∫ σ in a..b, F σ w) =
        fun z => ∫ σ in a..b, fderiv ℝ (F σ) z :=
      funext hfd
    rw [hfd']
    exact hcont
  have hint : ∀ z : Plane, IntervalIntegrable (fun σ => fderiv ℝ (F σ) z) volume a b :=
    fun z => ContinuousOn.intervalIntegrable ((pbPD_cont_fderiv hT hF z).mono hab)
  refine ⟨hC1, fun z => ?_, fun z => ?_⟩
  · rw [Cyl.partialQ_eq_fderiv hPdiff z, hfd z,
      ContinuousLinearMap.intervalIntegral_apply (hint z)]
    refine intervalIntegral.integral_congr ?_
    intro σ hσ
    show fderiv ℝ (F σ) z (1, 0) = Cyl.partialQ (F σ) z
    rw [Cyl.partialQ_eq_fderiv (hdiffF σ (hab hσ)) z]
  · rw [Cyl.partialEta_eq_fderiv hPdiff z, hfd z,
      ContinuousLinearMap.intervalIntegral_apply (hint z)]
    refine intervalIntegral.integral_congr ?_
    intro σ hσ
    show fderiv ℝ (F σ) z (0, 1) = Cyl.partialEta (F σ) z
    rw [Cyl.partialEta_eq_fderiv (hdiffF σ (hab hσ)) z]

end UnforcedLeray.Short.PartI
