import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.STSmooth.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSmoothRep.LocalSmooth
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.STSmoothRep.GlueLocal

/-!
# `PartIII-a:T21/2/7/2/1/1/8`: `STSobolevSmoothRep`

Source: SP 3060-3061 (`the November 2 reference manuscript`).

`STSobolevSmoothRep` follows from the local `C^∞` versions (`stLocalSmoothOfSob`) and their
gluing (`stGlueLocal`) via `stSobolevSmoothRep_of`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem stSobolevSmoothRep : STSobolevSmoothRep :=
  stSobolevSmoothRep_of stLocalSmoothOfSob stGlueLocal

end UnforcedLeray.Short.IIIa
