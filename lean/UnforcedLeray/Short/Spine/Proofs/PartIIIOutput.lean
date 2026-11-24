import UnforcedLeray.Short.PartIIIb.Proofs.Wiring

/-!
# Spine, task `Spine:SP-PIII` — Assembly of `PartIIIOutput`

Assembles `UnforcedLeray.Short.Spine.PartIIIOutput` from
`UnforcedLeray.Short.PartIIIb.Concrete.partIIIOutput_proof`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

theorem partIIIOutput : UnforcedLeray.Short.Spine.PartIIIOutput :=
  UnforcedLeray.Short.PartIIIb.Concrete.partIIIOutput_proof

end UnforcedLeray.Short.Spine
