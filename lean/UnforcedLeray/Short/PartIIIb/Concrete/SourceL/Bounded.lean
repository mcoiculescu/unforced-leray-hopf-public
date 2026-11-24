import UnforcedLeray.Short.PartIIIb.Concrete.SourceL
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0

/-!
# Part III-b, task `PartIII-b:C/srcL/16` (`sourceLBounded`)

`sourceLBounded` is `sourceLBounded_of` (Concrete/SourceL.lean) applied to the ambient bound
`sourceLAmbient` (task C/srcL/9) and the `N₀` bound `sourceLN0` (task C/srcL/2).
Source: `the November 2 reference manuscript` lines 4930-4937, 5883-5890.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sourceLBounded (as mZ γ : ℝ) (K : Set ℝ) (χo χy : ℝ → ℝ) : SourceLBounded as mZ γ K χo χy :=
  sourceLBounded_of (sourceLAmbient as K χo χy) (sourceLN0 mZ γ)

end UnforcedLeray.Short.PartIIIb.Concrete
