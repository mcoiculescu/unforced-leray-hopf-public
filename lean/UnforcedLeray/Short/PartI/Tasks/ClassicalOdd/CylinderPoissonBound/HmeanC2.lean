import UnforcedLeray.Short.PartI.Sub.T02_3_8

/-!
# Part I, task `PartI:T02/3/8/HmeanC2`: the horizontal average is `C²` (leaf M1 of `CylinderPoissonBound`)

Source of record: `the November 2 reference manuscript`, lines 276-288 and line 447
(the `q`-mean of the pressure).

Target: `CylPoisHmeanC2` (`Short/PartI/Sub/T02_3_8.lean`): for `c > 0` and `f` of class `C²`, the
horizontal average `hmean c f` is `C²` and its second `η`-derivative is the average of `∂_η² f`.

Proof.  For a `C¹` function `G`, differentiation under the `q`-integral over the compact cell
`Ioc (-c/2) (c/2)` gives `(hmean c G)' = hmean c (∂_η G)` (`cpH2_hasDerivAt_hmean`; the domination
bound is the sup of the continuous function `∂_η G` over a compact box).  Applying this to `f` and
then to `∂_η f` (which is `C¹` because `f` is `C²`) gives the second derivative.  Continuity of the
averages of a continuous function is the parametric interval integral.  The `C²` regularity follows
from `contDiff_succ_iff_deriv` and `contDiff_one_iff_deriv`.

All auxiliary names start with `cpH2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- The horizontal average of a continuous function is continuous in `η`. -/
theorem cpH2_continuous_hmean {c : ℝ} (hc : 0 < c) {G : Plane → ℝ} (hG : Continuous G) :
    Continuous (fun e => hmean c G e) := by
  have hf : Continuous (fun p : ℝ × ℝ => G (p.2, p.1)) :=
    hG.comp (continuous_snd.prodMk continuous_fst)
  have hint : Continuous (fun e : ℝ => ∫ q in (-c / 2)..(c / 2), G (q, e)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun e q => G (q, e)) hf _ _
  have heq : (fun e : ℝ => hmean c G e) =
      fun e => c⁻¹ • ∫ q in (-c / 2)..(c / 2), G (q, e) := by
    funext e
    unfold hmean
    rw [intervalIntegral.integral_of_le (show -c / 2 ≤ c / 2 by linarith)]
  rw [heq]
  exact hint.const_smul c⁻¹

/-- Differentiation under the `q`-integral: for a `C¹` function `G`, the horizontal average is
differentiable in `η`, with derivative the horizontal average of `∂_η G`. -/
theorem cpH2_hasDerivAt_hmean {c : ℝ} {G : Plane → ℝ} (hG : ContDiff ℝ 1 G)
    (e : ℝ) : HasDerivAt (fun e' => hmean c G e') (hmean c (Cyl.partialEta G) e) e := by
  have hd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hGc : Continuous G := hG.continuous
  have h01 : ContDiff ℝ (0 + 1) G := by simpa using hG
  have hpc : Continuous (Cyl.partialEta G) := (Cyl.contDiff_partialEta h01).continuous
  have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (e - 1) (e + 1) : Set Plane) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hpc.continuousOn
  have hmeas : ∀ x : ℝ, Continuous (fun q : ℝ => G (q, x)) := fun x =>
    hGc.comp (continuous_id.prodMk continuous_const)
  have hmeasF : ∀ x : ℝ, Continuous (fun q : ℝ => Cyl.partialEta G (q, x)) := fun x =>
    hpc.comp (continuous_id.prodMk continuous_const)
  have hint : Integrable (fun q : ℝ => G (q, e)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    ((hmeas e).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hF'meas : AEStronglyMeasurable (fun q : ℝ => Cyl.partialEta G (q, e))
      (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (hmeasF e).aestronglyMeasurable
  have hbound : ∀ᵐ q ∂(volume.restrict (Ioc (-c / 2) (c / 2))), ∀ x ∈ Ioo (e - 1) (e + 1),
      ‖Cyl.partialEta G (q, x)‖ ≤ (fun _ : ℝ => C) q := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun q hq x hx => ?_)
    exact hC (q, x) ⟨⟨hq.1.le, hq.2⟩, ⟨hx.1.le, hx.2.le⟩⟩
  have hdiffs : ∀ᵐ q ∂(volume.restrict (Ioc (-c / 2) (c / 2))), ∀ x ∈ Ioo (e - 1) (e + 1),
      HasDerivAt (fun y => G (q, y)) (Cyl.partialEta G (q, x)) x := by
    refine ae_of_all _ fun q x _ => ?_
    exact Cyl.hasDerivAt_sliceEta hd q x
  have hnhds : Ioo (e - 1) (e + 1) ∈ 𝓝 e := Ioo_mem_nhds (by linarith) (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (-c / 2) (c / 2)))
    (F := fun x q => G (q, x)) (F' := fun x q => Cyl.partialEta G (q, x))
    (bound := fun _ : ℝ => C) hnhds
    (Filter.Eventually.of_forall fun x => (hmeas x).aestronglyMeasurable) hint hF'meas hbound
    (integrable_const C) hdiffs
  exact key.2.const_smul c⁻¹

/-- The `η`-derivative of the horizontal average of a `C¹` function is the average of `∂_η`. -/
theorem cpH2_deriv_hmean {c : ℝ} {f : Plane → ℝ} (hf : ContDiff ℝ 1 f) :
    deriv (hmean c f) = hmean c (Cyl.partialEta f) := by
  funext e
  exact (cpH2_hasDerivAt_hmean hf e).deriv

/-- **Target** `CylPoisHmeanC2`: the horizontal average of a `C²` function is `C²`, and its second
`η`-derivative is the horizontal average of `∂_η² f`. -/
theorem cylPoisHmeanC2 : CylPoisHmeanC2 := by
  unfold CylPoisHmeanC2
  intro c f hc hf
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have h11 : ContDiff ℝ (1 + 1) f := by rwa [one_add_one_eq_two]
  have hY1 : ContDiff ℝ 1 (Cyl.partialEta f) := Cyl.contDiff_partialEta h11
  have hY0 : ContDiff ℝ (0 + 1) (Cyl.partialEta f) := by simpa using hY1
  have hYY0 : Continuous (Cyl.partialEta (Cyl.partialEta f)) :=
    (Cyl.contDiff_partialEta hY0).continuous
  have hdiffH : Differentiable ℝ (hmean c f) := fun e =>
    (cpH2_hasDerivAt_hmean hf1 e).differentiableAt
  have hderiv : deriv (hmean c f) = hmean c (Cyl.partialEta f) := cpH2_deriv_hmean hf1
  have hdiffY : Differentiable ℝ (hmean c (Cyl.partialEta f)) := fun e =>
    (cpH2_hasDerivAt_hmean hY1 e).differentiableAt
  have hderivY : deriv (hmean c (Cyl.partialEta f)) =
      hmean c (Cyl.partialEta (Cyl.partialEta f)) :=
    cpH2_deriv_hmean hY1
  have hcontY : Continuous (hmean c (Cyl.partialEta (Cyl.partialEta f))) :=
    cpH2_continuous_hmean hc hYY0
  have hC1Y : ContDiff ℝ 1 (hmean c (Cyl.partialEta f)) :=
    contDiff_one_iff_deriv.2 ⟨hdiffY, by rw [hderivY]; exact hcontY⟩
  have hC2 : ContDiff ℝ (1 + 1) (hmean c f) := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨hdiffH, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · rw [hderiv]; exact hC1Y
  rw [one_add_one_eq_two] at hC2
  have hsecond : deriv (deriv (hmean c f)) = hmean c (Cyl.partialEta (Cyl.partialEta f)) := by
    rw [hderiv, hderivY]
  exact ⟨hC2, fun η => congrFun hsecond η⟩

end UnforcedLeray.Short.PartI
