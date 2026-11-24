import UnforcedLeray.Short.PartIIIb.Concrete.SourceL
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0CS
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0Trans

/-!
# `N₀` finiteness for the source stress space (source 4924-4936)

Assembles the Cauchy-Schwarz bound `SLLint` (N0CS, from the transverse weight integral `SLTrans`
of N0Trans) into the bound `SourceLN0` via `sourceLN0_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`N₀` bound** (source 4924-4936): the stress space satisfies `SourceLN0`. -/
theorem sourceLN0 (mZ γ : ℝ) : SourceLN0 mZ γ :=
  sourceLN0_of (slLint mZ γ (slTrans mZ))

end UnforcedLeray.Short.PartIIIb.Concrete
