import UnforcedLeray.Short.PartI.Sub.T02_2_4

/-!
# Part I, shared helper `SliceIntegralCalculus` (differentiation of the `q`-integral in `η`)

Source of record: `the November 2 reference manuscript`, line 447 (the `q`-average
of `u` and the slice energy are differentiated in `η`). Statement: `SliceIntegralCalculus`
(`Short/PartI/Sub/T02_2_4.lean`, line 359).

Proof.

* Part 1 (differentiation under the integral). Fix `c > 0`, a `C¹` function `F` and `η`. The
  derivative `(q, η') ↦ ∂_η F(q, η')` is continuous (`Cyl.C1_partial_of_contDiff`), hence bounded
  on the compact box `Icc (-c/2) (c/2) ×ˢ Icc (η-1) (η+1)`. Apply
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the measure `volume.restrict (Ioc ..)`,
  the constant bound, and the slice derivatives `Cyl.hasDerivAt_sliceEta`.
* Part 2 (continuity). The `q`-integral over `Ioc (-c/2) (c/2)` equals the interval integral
  (`intervalIntegral.integral_of_le`), which is continuous in the parameter by
  `continuous_parametric_intervalIntegral_of_continuous'`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Real

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

theorem sliceIntegralCalculus : SliceIntegralCalculus := by
  intro c hc
  constructor
  · intro F hF η
    have hFc : Continuous F := hF.continuous
    have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
    have hEtaC : Continuous (Cyl.partialEta F) := (Cyl.C1_partial_of_contDiff hF).2
    -- the slices `q ↦ F (q, x)` and `q ↦ ∂_η F (q, x)` are continuous
    have hslice : ∀ x : ℝ, Continuous (fun q : ℝ => F (q, x)) :=
      fun x => hFc.comp (continuous_id.prodMk (continuous_const (y := x)))
    have hsliceC : ∀ x : ℝ, Continuous (fun q : ℝ => Cyl.partialEta F (q, x)) :=
      fun x => hEtaC.comp (continuous_id.prodMk (continuous_const (y := x)))
    -- uniform bound of `∂_η F` on a compact box around `(Ioc (-c/2) (c/2)) × {η}`
    have hK : IsCompact (Icc (-c / 2) (c / 2) ×ˢ Icc (η - 1) (η + 1)) :=
      isCompact_Icc.prod isCompact_Icc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hEtaC.continuousOn
    have hs : Ioo (η - 1) (η + 1) ∈ 𝓝 η := Ioo_mem_nhds (by linarith) (by linarith)
    have hFint : Integrable (fun q : ℝ => F (q, η))
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      ((hslice η).integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hFmeas : ∀ᶠ x in 𝓝 η,
        AEStronglyMeasurable (fun q : ℝ => F (q, x)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      Eventually.of_forall fun x => (hslice x).aestronglyMeasurable
    have hF'meas : AEStronglyMeasurable (fun q : ℝ => Cyl.partialEta F (q, η))
        (volume.restrict (Ioc (-c / 2) (c / 2))) :=
      (hsliceC η).aestronglyMeasurable
    have hbound : ∀ᵐ q ∂(volume.restrict (Ioc (-c / 2) (c / 2))),
        ∀ x ∈ Ioo (η - 1) (η + 1), ‖Cyl.partialEta F (q, x)‖ ≤ C := by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun q hq x hx => ?_)
      exact hC (q, x) (mk_mem_prod ⟨hq.1.le, hq.2⟩ ⟨hx.1.le, hx.2.le⟩)
    have hdiff : ∀ᵐ q ∂(volume.restrict (Ioc (-c / 2) (c / 2))),
        ∀ x ∈ Ioo (η - 1) (η + 1),
          HasDerivAt (fun y : ℝ => F (q, y)) (Cyl.partialEta F (q, x)) x := by
      refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun q _ x _ => ?_)
      exact Cyl.hasDerivAt_sliceEta hFd q x
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioc (-c / 2) (c / 2)))
      (F := fun x q => F (q, x)) (F' := fun x q => Cyl.partialEta F (q, x))
      (bound := fun _ : ℝ => C) hs hFmeas hFint hF'meas hbound (integrable_const C) hdiff
    exact key.2
  · intro F hF
    have hfc : Continuous (Function.uncurry fun (η : ℝ) (q : ℝ) => F (q, η)) :=
      hF.comp (continuous_snd.prodMk continuous_fst)
    have hle : -c / 2 ≤ c / 2 := by linarith
    have heq : (fun η : ℝ => ∫ q in Ioc (-c / 2) (c / 2), F (q, η)) =
        fun η : ℝ => ∫ q in (-c / 2)..(c / 2), F (q, η) :=
      funext fun η => (intervalIntegral.integral_of_le hle).symm
    rw [heq]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hfc (-c / 2) (c / 2)

end UnforcedLeray.Short.PartI
