import UnforcedLeray.Short.Spine.Compose
import UnforcedLeray.Short.Spine.ParamsProofs
import UnforcedLeray.Short.Spine.RefProofs

/-!
# `prop:unstable-background` (shorter proof) from the three part outputs

Source: `the November 2 reference manuscript`, lines 190-222 (the four interfaces),
5922-5988 (phase selection, scalar crossing, "this proves Proposition
`prop:unstable-background`").

The only inputs are the three part outputs: `ReferenceFromInstability` (choice of
`σ₀ ∈ (1/16,1/8)` with `𝒞(σ₀) ≠ 0` and continuity of `𝒥` at `σ₀`) is proved in
`RefProofs.lean` and `ParameterAsymptotics` in `ParamsProofs.lean`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

/-- **Spine theorem.** Parts I, II, III, and the choice of `σ₀`, give the existence of the data of
`prop:unstable-background` in the energy class. -/
theorem constructionClaimShort_of_partOutputs (hRef : ReferenceFromInstability)
    (hI : PartIOutput) (hII : PartIIOutput) (hIII : PartIIIOutput) : Interface.ConstructionClaimShort :=
  constructionClaimShort_of_parts hRef parameterAsymptotics hI hII hIII

/-- **Spine theorem, final form**: `prop:unstable-background` of the shorter proof (energy class, `Interface.ConstructionClaimShort`)
from Part I, Part II and Part III outputs alone. -/
theorem constructionClaimShort_of_outputs (hI : PartIOutput) (hII : PartIIOutput)
    (hIII : PartIIIOutput) : Interface.ConstructionClaimShort :=
  constructionClaimShort_of_partOutputs referenceFromInstability hI hII hIII

end UnforcedLeray.Short.Spine

#print axioms UnforcedLeray.Short.Spine.constructionClaimShort_of_outputs
