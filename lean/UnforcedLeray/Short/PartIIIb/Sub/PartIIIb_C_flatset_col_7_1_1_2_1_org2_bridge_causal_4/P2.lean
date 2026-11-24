import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge_causal_4
import UnforcedLeray.Units.B0224.PlaneHeat
import UnforcedLeray.Lib.HeatR3.ConvOp
import UnforcedLeray.Lib.HeatR3.Bounded
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Leaf `DuhamelIntegrable` (source `shorter-proof-2026-11-02.tex` 1684-1689)

The driving `G` vanishes for `σ < s₀` (`IsDriving`, third conjunct), so on `(0, s)` the integrand
is zero on `(0, s₀)`. On `[s₀, s]` the factor `(σ/s)^μ` is continuous, hence bounded, and the
planar heat of a field bounded by `M = sup |G(σ,·) i|` is bounded by `M` (Gaussian mass `1`).
Measurability in `σ` comes from the parametric integral of a jointly measurable integrand.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff Interval
open UnforcedLeray.Gaussian (Euc gaussKernel)

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem duhamelIntegrable : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.DuhamelIntegrable := by
  intro c ν μ G hG hν s hs x i
  obtain ⟨s0, s1, hs0, hsupp⟩ := hG.2.2.1
  have hGc : Continuous fun p : UnforcedLeray.Short.PartIIIb.Concrete.Chart => G p i :=
    (hG.1 i).continuous
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ p : UnforcedLeray.Short.PartIIIb.Concrete.Chart,
      ‖G p i‖ ≤ M := by
    obtain ⟨C, hC⟩ := hG.2.2.2 i 0
    exact ⟨C, fun p => by simpa [norm_iteratedFDeriv_zero] using hC p⟩
  -- the factor (σ/s)^μ is bounded on [s₀, s]
  have hfac_cont : ContinuousOn (fun σ : ℝ => (((σ / s : ℝ) : ℂ) ^ (μ : ℂ))) (Icc s0 s) := by
    apply ContinuousOn.cpow
    · exact (Complex.continuous_ofReal.comp (continuous_id.div_const s)).continuousOn
    · exact continuousOn_const
    · intro σ hσ
      exact Complex.ofReal_mem_slitPlane.2 (div_pos (lt_of_lt_of_le hs0 hσ.1) hs)
  obtain ⟨Kf, hKf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfac_cont
  -- measurability of the factor on (0, s]
  have hfac_meas : AEStronglyMeasurable (fun σ : ℝ => (((σ / s : ℝ) : ℂ) ^ (μ : ℂ)))
      (volume.restrict (Ioc 0 s)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    apply ContinuousOn.cpow
    · exact (Complex.continuous_ofReal.comp (continuous_id.div_const s)).continuousOn
    · exact continuousOn_const
    · intro σ hσ
      exact Complex.ofReal_mem_slitPlane.2 (div_pos hσ.1 hs)
  -- measurability of the parametric integral
  have hΦ : StronglyMeasurable (fun q : ℝ × Euc 2 =>
      gaussKernel 2 (ν * (s - q.1)) q.2 • ((G (q.1, x - UnforcedLeray.B0224.planeι q.2) i : ℝ) : ℂ)) := by
    have hk : Measurable (fun q : ℝ × Euc 2 => gaussKernel 2 (ν * (s - q.1)) q.2) :=
      (UnforcedLeray.B0224.measurable_gaussKernel_two).comp
        ((measurable_const.mul (measurable_const.sub measurable_fst)).prodMk measurable_snd)
    have hg : Measurable (fun q : ℝ × Euc 2 => ((G (q.1, x - UnforcedLeray.B0224.planeι q.2) i : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp (hGc.measurable.comp (measurable_fst.prodMk
        (measurable_const.sub (UnforcedLeray.B0224.measurable_planeι.comp measurable_snd))))
    exact (Measurable.smul hk hg).stronglyMeasurable
  have hI : StronglyMeasurable (fun σ : ℝ => ∫ y : Euc 2,
      gaussKernel 2 (ν * (s - σ)) y • ((G (σ, x - UnforcedLeray.B0224.planeι y) i : ℝ) : ℂ)) :=
    hΦ.integral_prod_right'
  have hne : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∉ ({s} : Set ℝ) :=
    (Set.countable_singleton s).ae_notMem volume
  -- the integrand equals the factor times the parametric integral, a.e. on (0, s]
  have hFeq : (fun σ : ℝ => (((σ / s : ℝ) : ℂ) ^ (μ : ℂ)) •
        UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) x) =ᵐ[volume.restrict (Ioc 0 s)]
      (fun σ : ℝ => (((σ / s : ℝ) : ℂ) ^ (μ : ℂ)) • ∫ y : Euc 2,
        gaussKernel 2 (ν * (s - σ)) y • ((G (σ, x - UnforcedLeray.B0224.planeι y) i : ℝ) : ℂ)) := by
    filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Ioc] with σ hσn hσI
    have hlt : σ < s := lt_of_le_of_ne hσI.2 (by simpa using hσn)
    simp only [UnforcedLeray.B0224.planeHeat_of_pos (mul_pos hν (sub_pos.2 hlt))]
  have hFmeas : AEStronglyMeasurable (fun σ : ℝ => (((σ / s : ℝ) : ℂ) ^ (μ : ℂ)) •
        UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) x)
      (volume.restrict (Ioc 0 s)) :=
    (hfac_meas.smul hI.aestronglyMeasurable).congr hFeq.symm
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le]
  refine Integrable.mono' (g := fun _ => max Kf 0 * max M 0) (integrable_const _) hFmeas ?_
  filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Ioc] with σ hσn hσI
  have hlt : σ < s := lt_of_le_of_ne hσI.2 (by simpa using hσn)
  have hθ : 0 < ν * (s - σ) := mul_pos hν (sub_pos.2 hlt)
  show ‖(((σ / s : ℝ) : ℂ) ^ (μ : ℂ)) •
      UnforcedLeray.B0224.planeHeat (ν * (s - σ)) (fun z => ((G (σ, z) i : ℝ) : ℂ)) x‖ ≤
      max Kf 0 * max M 0
  by_cases h0 : σ < s0
  · -- the driving vanishes on this slice
    have hz : ∀ z : ℝ × ℝ, G (σ, z) i = 0 := by
      intro z
      by_contra hne'
      have hGne : G (σ, z) ≠ 0 := fun h => hne' (by simp [h])
      exact absurd (hsupp (σ, z) hGne).1 (not_le.2 h0)
    rw [UnforcedLeray.B0224.planeHeat_of_pos hθ]
    simp only [hz, Complex.ofReal_zero, smul_zero, integral_zero, smul_eq_mul, mul_zero, norm_zero]
    exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
  · rw [not_lt] at h0
    have hσs : σ ∈ Icc s0 s := ⟨h0, hlt.le⟩
    have hfac : ‖(((σ / s : ℝ) : ℂ) ^ (μ : ℂ))‖ ≤ max Kf 0 :=
      le_max_of_le_left (hKf σ hσs)
    have hu : ∀ z : ℝ × ℝ, ‖((G (σ, z) i : ℝ) : ℂ)‖ ≤ max M 0 := fun z => by
      rw [Complex.norm_real]
      exact (hM (σ, z)).trans (le_max_left _ _)
    have hplane : ‖UnforcedLeray.B0224.planeHeat (ν * (s - σ))
        (fun z => ((G (σ, z) i : ℝ) : ℂ)) x‖ ≤ max M 0 := by
      have h1 := UnforcedLeray.Heat.norm_heatConv_le_of_bound UnforcedLeray.B0224.planeι hθ
        (u := fun z : ℝ × ℝ => ((G (σ, z) i : ℝ) : ℂ)) hu x
      have h2 : UnforcedLeray.B0224.planeHeat (ν * (s - σ))
          (fun z => ((G (σ, z) i : ℝ) : ℂ)) x =
          UnforcedLeray.Heat.heatConv UnforcedLeray.B0224.planeι (ν * (s - σ))
            (fun z => ((G (σ, z) i : ℝ) : ℂ)) x := by
        simp only [UnforcedLeray.B0224.planeHeat, if_pos hθ]
      rw [h2]
      exact h1
    rw [norm_smul]
    exact mul_le_mul hfac hplane (norm_nonneg _) (le_max_right _ _)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
