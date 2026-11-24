import UnforcedLeray.Short.PartIIIa.Clock.Sub.ZeroCircLeaves

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem zcChiDeriv : ZCChiDeriv := by
  obtain ⟨M, hM⟩ := ((B0285.chi0.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
    B0285.chi0.hasCompactSupport.deriv
  refine ⟨max M 0, le_max_right _ _, fun y => ⟨?_, ?_⟩⟩
  · rw [← Real.norm_eq_abs]
    exact (hM y).trans (le_max_left _ _)
  · intro h
    have hev : B0285.chi0 =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds h] with z hz
      apply B0285.chi0.zero_of_le_dist
      rw [Real.dist_eq, sub_zero]
      exact hz.le
    rw [hev.deriv_eq]
    simp

end UnforcedLeray.Short.IIIa
