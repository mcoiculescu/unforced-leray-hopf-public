import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6.Identity

/-!
# `PartII-a:N01/6`: the norm of the tensor lift (`CartLiftNorm`)

Source of record: `the November 2 reference manuscript` lines 1644-1648.
The proof is the composition of the slab-Frobenius identity `slabFrobIdentity` (task `/5`,
in `Sub/PartII-a_N01_6/Identity.lean`) with the reduction `cartLiftNorm_of` (`/6` umbrella).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01

theorem cartLiftNorm : UnforcedLeray.Short.PartIIa.N01.CartLiftNorm :=
  cartLiftNorm_of slabFrobIdentity

end UnforcedLeray.Short.PartIIa.N01
