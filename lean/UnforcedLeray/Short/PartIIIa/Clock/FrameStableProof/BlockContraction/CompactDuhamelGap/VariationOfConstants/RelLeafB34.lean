import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_2_2_loc

/-!
# `PartIII-a:T21/c3/2/1/2/2/2`: leaf `RelB4s` of `RelRegularityOrg2` (assembly)

Source of record: `the November 2 reference manuscript` (SP), lines 2941-2970.

`RelB4s` is obtained from the local dense continuity `RelB4loc` (`relB4loc_leaf`) by the
reduction `relB4s_of_loc`; the definitions and the 3-epsilon lemma live in the imported Sub files.
-/

set_option autoImplicit false

noncomputable section

/-- Leaf `RelB4s` (SP 2941-2970): the uniform bound plus local dense continuity give `RelB4s`. -/
theorem relB4s_leaf (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.RelRegularityOrg2.RelB4s κ :=
  UnforcedLeray.Short.IIIa.RelRegularityOrg2.relB4s_of_loc κ
    (UnforcedLeray.Short.IIIa.RelRegularityOrg2.relB4loc_leaf κ)
