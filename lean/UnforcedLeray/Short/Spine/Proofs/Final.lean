import UnforcedLeray.Short.Spine.Final
import UnforcedLeray.Short.Interface.Final
import UnforcedLeray.Short.Spine.Proofs.PartIOutput
import UnforcedLeray.Short.Spine.Proofs.PartIIOutput
import UnforcedLeray.Short.Spine.Proofs.PartIIIOutput

/-!
# Spine, task `Spine:SP-FINAL` — Final Assembly of `UnforcedLeray.MainClaim`

Assembles `UnforcedLeray.MainClaim` from `mainClaim_of_outputs`,
`UnforcedLeray.Short.Interface.interfaceLeaves`, `partIOutput`,
`partIIOutput`, and `partIIIOutput`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

theorem mainClaim : UnforcedLeray.MainClaim :=
  mainClaim_of_outputs
    UnforcedLeray.Short.Interface.interfaceLeaves
    partIOutput
    partIIOutput
    partIIIOutput

end UnforcedLeray.Short.Spine
