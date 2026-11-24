import UnforcedLeray.Short.Spine.ComposeFinal
import UnforcedLeray.Short.Interface.Compose

/-!
# Theorem A from the three part outputs and the interface leaves

`Spine.constructionClaimShort_of_outputs` (Parts I, II, III give `prop:unstable-background` in the
energy class) followed by the Interface area's compiled bridge
`Interface.mainClaim_of_constructionClaimShort` (the energy-class proposition gives the graph-mode
package, then the compiled localization half `Loc.Assembly.mainClaim_of_constructionClaim` gives
`MainClaim`, manuscript Theorem A, lines 84-115).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

/-- **Theorem A** (`UnforcedLeray.MainClaim`) from `PartIOutput`, `PartIIOutput`, `PartIIIOutput` and
the five leaves of the Interface bridge. -/
theorem mainClaim_of_outputs (L : Interface.InterfaceLeaves) (hI : PartIOutput)
    (hII : PartIIOutput) (hIII : PartIIIOutput) : MainClaim :=
  Interface.mainClaim_of_constructionClaimShort L (constructionClaimShort_of_outputs hI hII hIII)

end UnforcedLeray.Short.Spine

#print axioms UnforcedLeray.Short.Spine.mainClaim_of_outputs
