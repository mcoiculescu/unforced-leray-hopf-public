import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_5.Defs

/-!
# Smoothness of mollification (`mollify_contDiff`)

Source `the November 2 reference manuscript` lines 1351-1362, 1470-1480.
The convolution `mollify ρ u = ρ ⋆[lsmul] u` of a compactly supported smooth kernel with an
`L⁶` (hence locally integrable) field is smooth.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem mollify_contDiff {ρ : Space → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    {u : Space → CVec3} (hu : MemLp u 6 volume) : ContDiff ℝ ∞ (mollify ρ u) := by
  have hconv : mollify ρ u = MeasureTheory.convolution ρ u (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp [mollify, MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply]
  rw [hconv]
  exact hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ (hu.locallyIntegrable (by norm_num))

end UnforcedLeray.Short.PartIIIb.Concrete
