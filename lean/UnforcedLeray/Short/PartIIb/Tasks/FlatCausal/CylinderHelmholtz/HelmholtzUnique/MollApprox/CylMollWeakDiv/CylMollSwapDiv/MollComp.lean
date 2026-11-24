import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_5_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylLocInt

/-!


Source: `the November 2 reference manuscript` lines 1670, 1923-1926.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem cylMollComp : UnforcedLeray.Short.IIb.CylMollComp := by
  intro c r hc hr D hD ρ z i
  have hloc : LocallyIntegrable D volume := cylLocInt c r hc hr D hD
  set K : Set (ℝ × ℝ) := (fun y => z - y) '' tsupport (ρ.normed volume) with hK
  have hKc : IsCompact K :=
    (ρ.hasCompactSupport_normed (μ := volume)).image (by fun_prop)
  have h1 : IntegrableOn D K volume := hloc.integrableOn_isCompact hKc
  have h2 : Integrable (K.indicator D) volume := by
    rw [integrable_indicator_iff hKc.measurableSet]; exact h1
  have h3 : Integrable (fun y : ℝ × ℝ => K.indicator D (z - y)) volume :=
    h2.comp_sub_left z
  have hρc : Continuous (ρ.normed volume) := ρ.continuous_normed
  obtain ⟨C, hC⟩ := hρc.bounded_above_of_compact_support (ρ.hasCompactSupport_normed (μ := volume))
  have hEq : ∀ y : ℝ × ℝ, ρ.normed volume y • D (z - y) = ρ.normed volume y • K.indicator D (z - y) := by
    intro y
    by_cases hy : ρ.normed volume y = 0
    · simp [hy]
    · have hmem : z - y ∈ K := ⟨y, subset_tsupport _ hy, rfl⟩
      rw [Set.indicator_of_mem hmem]
  have h4 : Integrable (fun y : ℝ × ℝ => ρ.normed volume y • D (z - y)) volume := by
    simp_rw [hEq]
    refine Integrable.mono' (h3.norm.const_mul C) ?_ ?_
    · exact (hρc.aestronglyMeasurable).smul h3.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _ ▸ hC y)) (norm_nonneg _)
  unfold cylMoll
  have := ContinuousLinearMap.integral_comp_comm
    (((EuclideanSpace.proj (𝕜 := ℂ) i : CMerid →L[ℂ] ℂ)).restrictScalars ℝ) h4
  simp only [ContinuousLinearMap.coe_restrictScalars'] at this
  show (EuclideanSpace.proj (𝕜 := ℂ) i : CMerid →L[ℂ] ℂ) _ = _
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [Complex.real_smul]

end UnforcedLeray.Short.IIb
