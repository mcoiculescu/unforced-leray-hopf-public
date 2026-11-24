import UnforcedLeray.Short.PartIIIb.Scalar
import UnforcedLeray.Cons.C02PhaseLocked

/-!
# `PhaseLockedSequence` (lines 5928-5934), reusing `Blueprint.PhaseLock.lockedNu`

The sequence `ν_n` with `ω/ν_n - b log ν_n + c = 2π n sign ω` is the existing
`UnforcedLeray.Blueprint.PhaseLock.lockedNu` (`Cons/C02PhaseLocked.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

theorem phaseLockedSequence : PhaseLockedSequence := by
  intro ω b c hω
  exact ⟨UnforcedLeray.Blueprint.PhaseLock.lockedNu ω b c,
    UnforcedLeray.Blueprint.PhaseLock.lockedNu_pos ω b c,
    UnforcedLeray.Blueprint.PhaseLock.tendsto_lockedNu hω b c,
    UnforcedLeray.Blueprint.PhaseLock.eventually_phase_lockedNu hω b c⟩

end UnforcedLeray.Short.PartIIIb
