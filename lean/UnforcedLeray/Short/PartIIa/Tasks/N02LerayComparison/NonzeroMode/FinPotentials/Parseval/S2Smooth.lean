import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N02_4_4_7

/-!

Source: `the November 2 reference manuscript`, lines 1713-1727, 1744-1745.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- `nzS2 g = s ∂_s g` is smooth when `g` is. -/
theorem nzFpS2Smooth : UnforcedLeray.Short.PartIIa.NzFpS2Smooth := by
  unfold NzFpS2Smooth
  intro g hg
  unfold nzS2
  have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  exact contDiff_fst.smul (hfd.clm_apply contDiff_const)

end UnforcedLeray.Short.PartIIa
