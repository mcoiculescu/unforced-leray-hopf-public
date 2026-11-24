import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.XGInt

/-!
# Part II-b, task `PartII-b:G4/2/2/3/2`: `GreenRemTail`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: `xGInt` gives integrability of `s³ q` on `(0,∞)`; split the quadrupole at `r` with
`intervalIntegral.integral_interval_add_Ioi`; unfold `greenRem`, `greenInverse`, `quadrupole`
and close by `ring` (the `M r⁻²` terms cancel).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Blueprint

theorem greenRemTail : UnforcedLeray.Short.IIb.GreenRemTail := by
  intro q hq r hr
  have h3 : IntegrableOn (fun s : ℝ => (s : ℂ) ^ 3 * q s) (Ioi 0) := (xGInt q hq).1
  have hsplit : (∫ s in (0 : ℝ)..r, (s : ℂ) ^ 3 * q s) + (∫ s in Ioi r, (s : ℂ) ^ 3 * q s)
      = ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ 3 * q s :=
    intervalIntegral.integral_interval_add_Ioi h3 (h3.mono_set (Ioi_subset_Ioi hr.le))
  unfold greenRem Planar.greenInverse
  unfold Planar.quadrupole
  rw [← hsplit]
  ring

end UnforcedLeray.Short.IIb

end
