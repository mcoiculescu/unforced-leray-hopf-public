import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_3
import UnforcedLeray.Cons.C01ReferenceChoice

/-!
# Decomposition of `planarReferenceExists` (item `PartIII-b:C/near/delta/8/2/3/1`)

Source `the November 2 reference manuscript`,
Part I: `prop:short-gaussian-seed` (592-634), `prop:short-canonical` (1075-1150).  The planar
reference is built from the canonical branch (G3b = `Cons.C01.CanonicalBranchHyp`), whose
unconditional proof is the task `Spine:SP-CAN` (`Short/Spine/Proofs/CanonicalBranch.lean`,
`theorem canonicalBranchHyp`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Blueprint.Planar

/-- A planar reference exists, given the canonical branch hypothesis (Part I, 592-634, 1075-1150). -/
theorem planarReferenceExists_of (hcan : UnforcedLeray.Cons.C01.CanonicalBranchHyp) :
    PlanarReferenceExists := by
  obtain ⟨P, σ₀, h⟩ := UnforcedLeray.Cons.C01.exists_referenceChoice hcan
  exact ⟨P, h.1⟩

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
