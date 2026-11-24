import UnforcedLeray.Short.Spine.Assembly
import UnforcedLeray.Short.Spine.Proofs.CanonicalBranch
import UnforcedLeray.Short.Spine.Proofs.TrainGlobalExistence

/-!
# Spine: `PartIOutput` (task `Spine:SP-PI`)

Source of record: `the November 2 reference manuscript`, lines 1075-1150
(`prop:short-canonical`) and lines 261-288 (Gallay-Slijepcevic global existence of the train).

`PartIOutput` is `(∃ P, GaussianInstability P) ∧ TrainBUCExistence`. The first component comes from
the canonical branch `Spine.canonicalBranchHyp` (task `Spine:SP-CAN`) through
`Spine.partIOutput_of_canonical`. The second component is the BUC-class train existence, which is
`Spine.trainBUCExistence_of_global` applied to the global existence `Spine.trainGlobalExistence`
(task `Spine:SP-TRAIN`). The BUC-class form is the one `partIOutput_of_canonical` takes; the
library form `B0140.TrainExistence` is not the right argument here.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

/-- Part I output of the Spine: the Gaussian planar reference and the BUC-class train existence. -/
theorem partIOutput : UnforcedLeray.Short.Spine.PartIOutput :=
  partIOutput_of_canonical UnforcedLeray.Short.Spine.canonicalBranchHyp
    (trainBUCExistence_of_global UnforcedLeray.Short.Spine.trainGlobalExistence)

end UnforcedLeray.Short.Spine
