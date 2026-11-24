import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSmooth.Defs

/-!
# `PartIII-a:T21/2/7/2/1/1/8`: `STSobolevSmoothRep` from the local version and gluing
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- `STSobolevSmoothRep` from the local smooth versions (`STLocalSmoothOfSob`) and their gluing
(`STGlueLocal`). -/
theorem stSobolevSmoothRep_of (h3 : STLocalSmoothOfSob) (h4 : STGlueLocal) :
    STSobolevSmoothRep := fun U hU F hF => h4 U hU F (h3 U hU F hF)

end UnforcedLeray.Short.IIIa
