import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.Slice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.Mollify
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.Assemble

/-!
# `GradL2pIBP`: the phase-space integration-by-parts inequality (source 2531, 1515-1531, 1415-1424)

Source of record `the November 2 reference manuscript`.
The statement `GradL2pIBP` is proved by assembling the three pieces:
`gradL2pAssemble` (integration over the period, Hölder, Fatou), `gradL2pMollify`
(spatial mollification) and `gradL2pSlice` (the classical slice inequality).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradL2pIBP : GradL2pIBP :=
  gradL2pAssemble gradL2pMollify gradL2pSlice

end UnforcedLeray.Short.PartIIIb.Concrete
