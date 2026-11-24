import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf1
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf3
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf4
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf5
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf6
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftNoSwirl.Leaf7
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6_1

/-!
# `PartII-b:T10/6/1`: `DriftNoSwirl` (assembly of the seven leaves through `driftNoSwirl_of`)

Source of record: `the November 2 reference manuscript`, lines 1912-1915.
-/

set_option autoImplicit false

theorem driftNoSwirl_proof : UnforcedLeray.Short.IIb.DriftNoSwirl :=
  UnforcedLeray.Short.IIb.driftNoSwirl_of gActPhaseTest gActDrift gActPair gActInv
    UnforcedLeray.Short.IIb.nvCInvariant UnforcedLeray.Short.IIb.gActInYr
    UnforcedLeray.Short.IIb.phaseFundamental
