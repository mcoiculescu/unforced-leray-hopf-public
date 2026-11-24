import UnforcedLeray.Short.PartIIb.Sub.T22_4
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Int1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Int2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.CutId
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Cutoff
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Limit

/-!
# Part II-b, task `PartII-b:T22/4`: `CylDiffusionBound`

Source of record: `the November 2 reference manuscript`, lines 2092-2104.

Assembly of the five leaves (`dbInt1`, `dbInt2`, `dbCutId`, `dbCutoff`, `dbLimit`) with
`cylDiffusionBound_of` from `Sub/T22_4.lean`:
`cylDiffusionBound_of dbInt1 dbInt2 (dbLimit dbInt1 dbInt2 dbCutId dbCutoff)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylDiffusionBound : UnforcedLeray.Short.IIb.CylDiffusionBound :=
  cylDiffusionBound_of dbInt1 dbInt2 (dbLimit dbInt1 dbInt2 dbCutId dbCutoff)

end UnforcedLeray.Short.IIb
