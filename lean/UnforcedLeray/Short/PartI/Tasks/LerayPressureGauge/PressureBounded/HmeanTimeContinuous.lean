import UnforcedLeray.Short.PartI.Sub.T02_2_3

/-!
# Part I, task `PartI:T02/2/3`, leaf `PbHmeanTimeContinuous` (continuity in time of the horizontal average)

Source of record: `the November 2 reference manuscript`, line 447 (the limit step
`PbAvgLimit`, of which this is a leaf, hence of `PressureBounded`).

Statement: `PbHmeanTimeContinuous` (`Sub/T02_2_3.lean`): for `0 < c`, `T`, and `F` continuous on
`[0,T] × ℝ²`, the map `σ ↦ hmean c (F σ) η` is continuous on `[0,T]`, for every `η`.

Proof.  Clamp the time variable, `σ ↦ max 0 (min σ T)`, so that the integrand
`(σ,q) ↦ F (clamp σ) (q,η)` is continuous on all of `ℝ × ℝ` (`ContinuousOn.comp_continuous`).
The parametric interval integral of a jointly continuous integrand is continuous in the parameter
(`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`).  On `[0,T]` the clamp is
the identity, and `Ioc` versus interval integral is `intervalIntegral.integral_of_le`.  For `T < 0`
the set `[0,T]` is empty and the claim is trivial.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

theorem pbHC_clamp_mem {T : ℝ} (hT : 0 ≤ T) (σ : ℝ) : max 0 (min σ T) ∈ Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem pbHC_clamp_eq {T σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) T) : max 0 (min σ T) = σ := by
  rw [min_eq_left hσ.2, max_eq_right hσ.1]

theorem pbHC_clamp_continuous (T : ℝ) : Continuous fun σ : ℝ => max 0 (min σ T) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem pbHmeanTimeContinuous : PbHmeanTimeContinuous := by
  intro c T F hc hF η
  rcases lt_or_ge T 0 with hT | hT
  · rw [Set.Icc_eq_empty (not_le.mpr hT)]
    exact continuousOn_empty _
  · have hmap : Continuous fun p : ℝ × ℝ => (max 0 (min p.1 T), (p.2, η)) :=
      ((pbHC_clamp_continuous T).comp continuous_fst).prodMk
        (continuous_snd.prodMk continuous_const)
    have hmem : ∀ p : ℝ × ℝ, (max 0 (min p.1 T), (p.2, η)) ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
      fun p => Set.mk_mem_prod (pbHC_clamp_mem hT p.1) (Set.mem_univ _)
    have hG : Continuous fun p : ℝ × ℝ => F (max 0 (min p.1 T)) (p.2, η) :=
      hF.comp_continuous hmap hmem
    have hI : Continuous fun σ : ℝ => ∫ q in (-c / 2)..(c / 2), F (max 0 (min σ T)) (q, η) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun σ q => F (max 0 (min σ T)) (q, η)) hG (-c / 2) (c / 2)
    have hcongr : ContinuousOn
        (fun σ : ℝ => c⁻¹ • ∫ q in (-c / 2)..(c / 2), F (max 0 (min σ T)) (q, η)) (Icc 0 T) :=
      (hI.const_smul c⁻¹).continuousOn
    refine hcongr.congr ?_
    intro σ hσ
    show c⁻¹ • ∫ q in Ioc (-c / 2) (c / 2), F σ (q, η)
        = c⁻¹ • ∫ q in (-c / 2)..(c / 2), F (max 0 (min σ T)) (q, η)
    rw [pbHC_clamp_eq hσ, intervalIntegral.integral_of_le (show -c / 2 ≤ c / 2 by linarith)]

end UnforcedLeray.Short.PartI
