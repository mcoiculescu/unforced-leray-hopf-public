import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctionalDual.SolDiv

/-!
# `PairFunctionalDual` (task `PartIII-b:C/near/pins/3/4/1`)

The dual test `L₀ᵗΦ + μΦ` of a solenoidal phase test is again a solenoidal phase test
(`PairFunctionalDual/SolDiv.lean`, `isSolTest_L0T_add`). So the bounded functional of
`pairFunctional` (`Proofs/PairFunctional.lean`) applies to it directly.
Source 4139-4146.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem pairFunctionalDual : PairFunctionalDual := by
  intro p μ Φ hΦ
  have hS := PairDualAux.isSolTest_L0T_add (ν := p.ν) (μ := μ) hΦ
  obtain ⟨ℓ, hℓ⟩ := pairFunctional p.c p.ε p.c_pos p.ε_pos _ hS
  exact ⟨ℓ, hℓ⟩

end UnforcedLeray.Short.PartIIIb.NearInst
