import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c1_b
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramUnfold
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.GramTail
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.EBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts.Lam0Bound

/-!
# Part III-a, task `PartIII-a:T21/c1/b`: uniform frame facts (SP 2891-2897)

`perFrameFactsAll` is the assembly `perFrameFactsAll_of` applied to the four planar leaves
`perGramUnfold`, `perGramTail`, `perEBound`, `perLam0Bound`. The hypothesis `IsSeedKernels κ` is not
needed by the leaves and is not used.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- Uniform frame facts for the seed kernels (SP 2891-2897). -/
theorem perFrameFactsAll (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels)
    (h : UnforcedLeray.Short.IIIa.IsSeedKernels κ) :
    UnforcedLeray.Short.IIIa.PerFrameFactsAll κ :=
  UnforcedLeray.Short.IIIa.perFrameFactsAll_of κ
    (UnforcedLeray.Short.IIIa.perGramUnfold κ)
    (UnforcedLeray.Short.IIIa.perGramTail κ)
    (UnforcedLeray.Short.IIIa.perEBound κ)
    (UnforcedLeray.Short.IIIa.perLam0Bound κ)

end UnforcedLeray.Short.IIIa
