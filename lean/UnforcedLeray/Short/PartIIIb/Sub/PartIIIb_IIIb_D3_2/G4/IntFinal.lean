import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntInt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntLeaf1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntLeaf2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4.IntLeaf3

/-!
# `PartIII-b:IIIb-D3/2/G4/4`: Assembly of `IntConj` (`flatITInt`)

Assembles `IntConj D` from `IntConj_of`, `flatPieceMeas D`, `flatUpperMaj D`, and `flatLowerMaj D`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

theorem flatITInt (D : SeqData) : IntConj D :=
  IntConj_of D (flatPieceMeas D) (flatUpperMaj D) (flatLowerMaj D)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
