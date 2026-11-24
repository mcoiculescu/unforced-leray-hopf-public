import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_1
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch

/-!
# `planarReferenceExists` (item `PartIII-b:C/near/delta/8/2/3/1`)

The planar reference exists unconditionally: the canonical branch hypothesis
`Cons.C01.CanonicalBranchHyp` is supplied by the task `Spine:SP-CAN`
(`UnforcedLeray.Short.Spine.canonicalBranchHyp`), and `planarReferenceExists_of` turns it into
`PlanarReferenceExists`.

Source of record: `the November 2 reference manuscript`,
`prop:short-gaussian-seed` (592-634) and `prop:short-canonical` (1075-1150).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

/-- A planar reference exists (Part I, 592-634, 1075-1150). -/
theorem planarReferenceExists : PlanarReferenceExists :=
  planarReferenceExists_of UnforcedLeray.Short.Spine.canonicalBranchHyp

end UnforcedLeray.Short.PartIIIb.NearInst.Delta

#print axioms UnforcedLeray.Short.PartIIIb.NearInst.Delta.planarReferenceExists
