import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep.RayU
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# From the ray identity to the distributional comoving derivative
(helper of `PartII-b:S3/1/1/2/1/2/1`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523.

* `ray_FTC`: the fundamental theorem of calculus along comoving rays for jointly smooth fields
  (`d/ds F(s, e^{-s/2}x) = T₀F`);
* `transpose_of_ray`: if `F(s₂, e^{-s₂/2}x) - F(s₁, e^{-s₁/2}x) = ∫_{s₁}^{s₂} H(r, e^{-r/2}x) dr`
  with `F, H` jointly continuous, then `∫∫ T₀ᵗK · F = ∫∫ K · H` for every smooth compactly
  supported test `K` (chart change of variables and integration by parts along the rays).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff BigOperators

namespace UnforcedLeray.Short.IIb.BaseRepSub

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.B0411 UnforcedLeray.B0412 UnforcedLeray.BochnerTime UnforcedLeray.RieszLp

/-! ## 1. FTC along rays for jointly smooth fields -/

theorem hasDerivAt_dilScale (r : ℝ) : HasDerivAt dilScale (-(1 / 2) * dilScale r) r := by
  have h : HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (Real.exp (-r / 2) * (-1 / 2)) r :=
    (((hasDerivAt_id' r).neg).div_const 2).exp
  unfold dilScale
  convert h using 1
  ring

theorem hasDerivAt_ray {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2)) (x : Space) (r : ℝ) :
    HasDerivAt (fun r => F r (dilScale r • x)) (comovingPartial F r (dilScale r • x)) r := by
  have hF' : ContDiff ℝ ∞ (PhaseDerivStepSub.uncurriedField F) := hF
  have hγ : HasDerivAt (fun r : ℝ => ((r, dilScale r • x) : ℝ × Space))
      ((1 : ℝ), (-(1 / 2) * dilScale r) • x) r :=
    (hasDerivAt_id r).prodMk ((hasDerivAt_dilScale r).smul_const x)
  have hFd := (hF'.differentiable (by simp) (r, dilScale r • x)).hasFDerivAt
  have h := hFd.comp_hasDerivAt r hγ
  refine h.congr_deriv ?_
  have hsplit : ((1 : ℝ), (-(1 / 2) * dilScale r) • x) =
      ((1 : ℝ), (0 : Space)) + ((0 : ℝ), (-(1 / 2) : ℝ) • (dilScale r • x)) := by
    refine Prod.ext (by simp) ?_
    simp [smul_smul]
  rw [hsplit, map_add]
  have h2 := PhaseDerivStepSub.dirSpatialJet_singleton_eq_joint_fderiv hF'
    ((-(1 / 2) : ℝ) • (dilScale r • x)) r (dilScale r • x)
  rw [← h2]
  simp only [comovingPartial, PhaseDerivStepSub.phasePartial, dirSpatialJet_cons, dirSpatialJet_nil,
    spatialRadialDrift, Pi.sub_apply, Pi.smul_apply, map_smul]
  rw [sub_eq_add_neg, neg_smul]

/-- **FTC along comoving rays.** -/
theorem ray_FTC {F : ℝ → SpatialField} (hF : ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2))
    (s₁ s₂ : ℝ) (x : Space) :
    F s₂ (dilScale s₂ • x) - F s₁ (dilScale s₁ • x) =
      ∫ r in s₁..s₂, comovingPartial F r (dilScale r • x) := by
  have hc : Continuous fun r => comovingPartial F r (dilScale r • x) :=
    (CorrComovingSub.contDiff_joint_comovingPartial hF).continuous.comp
      (continuous_id.prodMk (continuous_dilScale.smul continuous_const))
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hasDerivAt_ray hF x r)
    (hc.intervalIntegrable _ _)).symm

/-! ## 2. Transposition -/

theorem hasDerivAt_of_ray {F H : ℝ → SpatialField}
    (hHc : Continuous fun x : ℝ × Space => H x.1 x.2)
    (hray : ∀ s₁ s₂ x, F s₂ (dilScale s₂ • x) - F s₁ (dilScale s₁ • x) =
      ∫ r in s₁..s₂, H r (dilScale r • x)) (x : Space) (t : ℝ) :
    HasDerivAt (fun s => F s (dilScale s • x)) (H t (dilScale t • x)) t := by
  have hc : Continuous fun r => H r (dilScale r • x) :=
    hHc.comp (continuous_id.prodMk (continuous_dilScale.smul continuous_const))
  have hprim : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, H r (dilScale r • x))
      (H t (dilScale t • x)) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have heq : (fun s => F s (dilScale s • x)) =
      fun s => F 0 (dilScale 0 • x) + ∫ r in (0 : ℝ)..s, H r (dilScale r • x) := by
    funext s
    rw [← hray 0 s x]
    abel
  rw [heq]
  exact hprim.const_add _

/-- **Transposition.** The ray identity gives `∫∫ T₀ᵗK · F = ∫∫ K · H` on compactly supported
smooth tests. -/
theorem transpose_of_ray {F H : ℝ → SpatialField}
    (hFc : Continuous fun x : ℝ × Space => F x.1 x.2)
    (hHc : Continuous fun x : ℝ × Space => H x.1 x.2)
    (hray : ∀ s₁ s₂ x, F s₂ (dilScale s₂ • x) - F s₁ (dilScale s₁ • x) =
      ∫ r in s₁..s₂, H r (dilScale r • x))
    {K : ℝ × Space → CVec3} (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) :
    ∫ t, ∫ y, dotL (driftT K (t, y)) (realC (F t y)) =
      ∫ t, ∫ y, dotL (K (t, y)) (realC (H t y)) := by
  set k : ℝ × Space → CVec3 := chartPull K with hkdef
  have hk : ContDiff ℝ ∞ k := contDiff_chartPull hK
  have hkc : HasCompactSupport k := hasCompactSupport_chartPull hKc
  have hKk : K = chartLift k := (chartLift_chartPull K).symm
  have hdk : ContDiff ℝ ∞ (fun q => dτ k q) :=
    (hk.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdkc : HasCompactSupport (fun q => dτ k q) := hkc.fderiv_apply ℝ ((1 : ℝ), (0 : Space))
  rw [hKk, driftT_chartLift hk]
  simp only [integral_chartLift]
  set Ft : ℝ → Space → CVec3 := fun t x => realC (F t (dilScale t • x)) with hFt
  set Ht : ℝ → Space → CVec3 := fun t x => realC (H t (dilScale t • x)) with hHt
  have hFtc : Continuous (Function.uncurry Ft) :=
    continuous_realC.comp (continuous_uncurry_ray (V := F) hFc)
  have hHtc : Continuous (Function.uncurry Ht) :=
    continuous_realC.comp (continuous_uncurry_ray (V := H) hHc)
  -- integrability on the product
  have hint1 : Integrable (Function.uncurry fun (t : ℝ) (x : Space) =>
      dotL (-dτ k (t, x)) (Ft t x)) ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((dotL.continuous.comp (hdk.continuous.neg)).clm_apply hFtc) ?_
    refine (hdkc.neg).mono' fun q hq => subset_tsupport _ ?_
    intro h0
    apply hq
    change dotL ((fun q => -dτ k q) q) (Ft q.1 q.2) = 0
    rw [show (fun q => -dτ k q) q = 0 from h0, map_zero, ContinuousLinearMap.zero_apply]
  have hint2 : Integrable (Function.uncurry fun (t : ℝ) (x : Space) =>
      dotL (k (t, x)) (Ht t x)) ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    refine Continuous.integrable_of_hasCompactSupport
      ((dotL.continuous.comp hk.continuous).clm_apply hHtc) ?_
    refine hkc.mono' fun q hq => subset_tsupport _ ?_
    intro h0
    apply hq
    change dotL (k q) (Ht q.1 q.2) = 0
    rw [show k q = 0 from h0, map_zero, ContinuousLinearMap.zero_apply]
  change ∫ t, ∫ x, dotL (-dτ k (t, x)) (Ft t x) = ∫ t, ∫ x, dotL (k (t, x)) (Ht t x)
  rw [integral_integral_swap hint1, integral_integral_swap hint2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  -- integration by parts along the ray through `x`
  have hdkt : ∀ t, HasDerivAt (fun s => k (s, x)) (dτ k (t, x)) t := by
    intro t
    have hγ : HasDerivAt (fun s : ℝ => ((s, x) : ℝ × Space)) ((1 : ℝ), (0 : Space)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact (hk.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t hγ
  have hFt' : ∀ t, HasDerivAt (fun s => Ft s x) (Ht t x) t := by
    intro t
    have h := hasDerivAt_of_ray hHc hray x t
    have h2 := (ofReV.hasFDerivAt (x := F t (dilScale t • x))).comp_hasDerivAt t h
    simpa [hFt, hHt, Function.comp_def, PointwiseDerivSub.realC_eq_ofReV] using h2
  have hderiv : ∀ t, HasDerivAt (fun s => dotLR (k (s, x)) (Ft s x))
      (dotLR (k (t, x)) (Ht t x) + dotLR (dτ k (t, x)) (Ft t x)) t := fun t =>
    dotLR.hasDerivAt_of_bilinear (fun _ => hdkt t) (fun _ => hFt' t)
  have hc1 : Continuous fun t => dotL (k (t, x)) (Ht t x) :=
    (dotL.continuous.comp (hk.continuous.comp (continuous_id.prodMk continuous_const))).clm_apply
      (hHtc.comp (continuous_id.prodMk continuous_const))
  have hc2 : Continuous fun t => dotL (dτ k (t, x)) (Ft t x) :=
    (dotL.continuous.comp (hdk.continuous.comp (continuous_id.prodMk continuous_const))).clm_apply
      (hFtc.comp (continuous_id.prodMk continuous_const))
  have hc0 : Continuous fun t => dotL (k (t, x)) (Ft t x) :=
    (dotL.continuous.comp (hk.continuous.comp (continuous_id.prodMk continuous_const))).clm_apply
      (hFtc.comp (continuous_id.prodMk continuous_const))
  have hsupp : ∀ (G : ℝ × Space → CVec3), HasCompactSupport G → ∀ (W : ℝ → CVec3),
      Continuous (fun t => dotL (G (t, x)) (W t)) → Integrable fun t => dotL (G (t, x)) (W t) := by
    intro G hG W hW
    refine hW.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro ((hG.isCompact.image continuous_fst)) fun t ht => ?_
    have h0 : G (t, x) = 0 := by
      by_contra hne
      exact ht ⟨(t, x), subset_tsupport _ hne, rfl⟩
    rw [h0, map_zero, ContinuousLinearMap.zero_apply]
  have hI1 := hsupp k hkc (fun t => Ht t x) hc1
  have hI2 := hsupp (fun q => dτ k q) hdkc (fun t => Ft t x) hc2
  have hI0 := hsupp k hkc (fun t => Ft t x) hc0
  have hI12 : Integrable (fun t => dotLR (k (t, x)) (Ht t x) + dotLR (dτ k (t, x)) (Ft t x))
      volume := hI1.add hI2
  have hI0' : Integrable (fun t => dotLR (k (t, x)) (Ft t x)) volume := hI0
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hI12 hI0'
  simp only [dotLR_apply] at hzero
  rw [integral_add hI1 hI2] at hzero
  have hneg : ∫ t, dotL (-dτ k (t, x)) (Ft t x) = -∫ t, dotL (dτ k (t, x)) (Ft t x) := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp
  simp only [Function.uncurry_apply_pair]
  rw [hneg]
  linear_combination -hzero

end UnforcedLeray.Short.IIb.BaseRepSub

end
