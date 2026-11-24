import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.Tested
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntFinal

/-!
# `PartIII-b:IIIb-D3/2/G4`: Assembly of `FlatUnif.GroupTested` (SP 4665–4690)

Assembles `FlatUnif.GroupTested D` from `FlatUnif.G4.flatGroupTested_of`,
`FlatUnif.G4.flatTestedConj`, and `FlatUnif.G4.flatITInt`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem flatGroupTested (D : SeqData) : FlatUnif.GroupTested D :=
  FlatUnif.G4.flatGroupTested_of FlatUnif.G4.flatTestedConj FlatUnif.G4.flatITInt D

end UnforcedLeray.Short.PartIIIb.Concrete
