import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.NearUnit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.Newton
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G5.Moments

/-!
# `PartIII-b:IIIb-D3/2/G5`: Assembly of `FlatUnif.FlatNewtonComparison` (SP 4846–4907)

Assembles `FlatUnif.FlatNewtonComparison D` from `FlatUnif.G5.flatNewtonComparison_of`,
`FlatUnif.G5.flatNearUnit`, `FlatUnif.G5.newtonTaylor`, and `FlatUnif.G5.frakTMoments`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem flatNewtonComparison (D : SeqData) : FlatUnif.FlatNewtonComparison D :=
  FlatUnif.G5.flatNewtonComparison_of D (FlatUnif.G5.flatNearUnit D)
    FlatUnif.G5.newtonTaylor (FlatUnif.G5.frakTMoments D)

end UnforcedLeray.Short.PartIIIb.Concrete
