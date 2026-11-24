import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.ProfileUnique.WindowZero
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.ProfileUnique.LocInt
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.ProfileUnique.StripExtend
import UnforcedLeray.Short.PartIIb.Tasks.GradLapNvC.DivVanish.FundWindow

/-!
# Part II-b, task `PartII-b:G4/3/5` (`ProfileUnique`): assembly

`profileUnique` is `profileUnique_of` (Sub file `PartII-b_G4_3_5`) applied to the three leaves
`profileWindowZero`, `profileLocInt`, `profileStripExtend` and to `fundWindow_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`ProfileUnique`** (SP 1897-2663, Part II-b `G4/3/5`): assembled from the leaves. -/
theorem profileUnique : UnforcedLeray.Short.IIb.ProfileUnique :=
  profileUnique_of profileWindowZero profileLocInt profileStripExtend fundWindow_proof

end UnforcedLeray.Short.IIb
