import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_2_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.SliceT2.DuComponents
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APElliptic
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation

/-!
# Part I, `PartI:T04/10/2/2/2/2`: `SliceDuSup` (assembly)

Source of record: `the November 2 reference manuscript`, lines 285-288.
`SliceDuSup` follows from `sliceDuComponents` (the structural component fact), the first conjunct
of `cylinder_interpolation_uniform` (giving `CylSupInterp`), and `apElliptic` (giving `APElliptic`),
via `sliceDuSup_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem sliceDuSup : SliceDuSup :=
  sliceDuSup_of sliceDuComponents cylinder_interpolation_uniform.1 apElliptic

end UnforcedLeray.Short.PartI
