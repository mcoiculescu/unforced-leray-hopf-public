import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.LerayForceProj.Slices
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.LerayForceProj.Parts

/-!
# `LerayYq` from the six leaves (`PartII-b:G4/4/2/1`)

Source: `the November 2 reference manuscript` lines 119-120 (the Leray projection
`𝔓 = I + R ⊗ R`), 1307-1308 (boundedness on `W^{1,p}`), 2370-2383 (`𝔓` applied phase by phase is
bounded on `Y_p` and commutes with `∂_j`).

The six leaves are proved in `Slices.lean` (`aeSliceDy`, `aeForallSliceDy`, `hasPhaseOpDyOfAe`) and
`Parts.lean` (`weakDyCOfComp`, `compOfWeakDyC`, `testDyOfComp`); `lerayYq_of` (in `Reduction.lean`)
assembles them into `LerayYq` with `T = lerayY P q₀` and `Cl = ‖lerayC q₀‖ + 1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **The phase-space Leray projection `LerayYq`** (SP 2370-2383, 1307-1308), proved from the
six leaves with no hypothesis. -/
theorem lerayYq : UnforcedLeray.Short.IIb.LerayYq :=
  lerayYq_of aeSliceDy aeForallSliceDy weakDyCOfComp compOfWeakDyC testDyOfComp
    hasPhaseOpDyOfAe

#print axioms lerayYq

end UnforcedLeray.Short.IIb
