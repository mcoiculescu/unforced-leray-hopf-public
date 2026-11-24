import UnforcedLeray.Short.PartIIIb.Concrete.SourceL
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Smooth
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.TraceFree
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Azimuthal
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0

/-!
# Part III-b, task `PartIII-b:C/srcL/15` (`sourceLInAff`)

`𝓛T ∈ 𝒜` for every stress `T` of the concrete space (source 4797-4799 of
`the November 2 reference manuscript`).  The membership follows from
`sourceLInAff_of` applied to the five source facts: smoothness (`sourceLSmooth`, C/srcL/10),
trace freeness (`sourceLTraceFree`, C/srcL/11), azimuthal symmetry (`sourceLAzimuthal`,
C/srcL/12), the ambient bound at the single age `μ` (`sourceLAmbient`, C/srcL/9) and the
`N₀` bound (`sourceLN0`, C/srcL/2).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `𝓛T ∈ 𝒜` for all stresses `T` (source 4797-4799). -/
theorem sourceLInAff (as c mZ ρb γ ν ε μ : ℝ) (χo χy : ℝ → ℝ) :
    SourceLInAff as c mZ ρb γ ν ε μ χo χy :=
  sourceLInAff_of (sourceLSmooth c mZ ρb γ ν ε μ χo χy)
    (sourceLTraceFree c mZ ρb γ ν ε μ χo χy)
    (sourceLAzimuthal c mZ ρb γ ν ε μ χo χy)
    (sourceLAmbient as {μ} χo χy)
    (sourceLN0 mZ γ)

end UnforcedLeray.Short.PartIIIb.Concrete
