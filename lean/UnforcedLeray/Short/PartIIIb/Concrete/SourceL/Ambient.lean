import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.Scale
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.JetEps1

/-!
# Part III-b, task `PartIII-b:C/srcL/9` (`sourceLAmbient`)

`sourceLAmbient` is `sourceLAmbient_of` (Sub/PartIII-b_C_srcL_9.lean) applied to the exact
scaling `Scale.lptScale` and the `ε = 1` jet bound `jetEps1`. Source:
`the November 2 reference manuscript` lines 4917-4937.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sourceLAmbient (as : ℝ) (K : Set ℝ) (χo χy : ℝ → ℝ) : SourceLAmbient as K χo χy :=
  sourceLAmbient_of Scale.lptScale (jetEps1 K χo χy)

end UnforcedLeray.Short.PartIIIb.Concrete
