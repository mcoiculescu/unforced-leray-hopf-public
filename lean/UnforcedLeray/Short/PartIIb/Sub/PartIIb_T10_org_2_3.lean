import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_of
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_4

/-!
# `PartII-b:T10/org/2/3` (`SolSepSpatial`): decomposition

Source `the November 2 reference manuscript` (SP, the solenoidal-separation step).
Assembly: `solSepSpatial_of` applied to the four unconditional inputs `lerayCFixed_proof`
(`PartII-b_T10_org_2_3_1`), `lerayCSymm_proof` (`PartII-b_T10_org_2_3_2`), `lerayCDensity_proof`
(`PartII-b_T10_org_2_3_3`) and `fundLemmaC_proof` (`PartII-b_T10_org_2_3_4`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:T10/org/2/3`: spatial solenoidal separation.** -/
theorem solSepSpatial : UnforcedLeray.Short.IIb.SolSepSpatial :=
  solSepSpatial_of lerayCFixed_proof lerayCSymm_proof lerayCDensity_proof fundLemmaC_proof

end UnforcedLeray.Short.IIb
