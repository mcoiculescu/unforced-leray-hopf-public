import UnforcedLeray.Short.PartI.Sub.T02_1_2_2.HeatWeakDeriv
import UnforcedLeray.Short.PartI.Sub.T02_1_2_2.P0WeakDeriv

/-!
# Part I, task `PartI:T02/1/2/2`: `SeedDerivative`

Source of record: `the November 2 reference manuscript`, lines 261-288.

`∂_j` commutes with the projected heat orbit `t ↦ P₀ e^{νtΔ} x`: this is `seedDerivative_of`
(`Short/PartI/Sub/T02_1_2_2.lean`) applied to the two commutation leaves, `heatWeakDeriv_proof`
(the Gaussian heat on `H³`) and `p0WeakDeriv_proof` (the Leray projection on `H³`), both resting on
the bridge `weakDerivCell_proof` between weak derivatives and `L²`-cell classes.

No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **`SeedDerivative`**: if `x' = ∂_j x` weakly in `H³`, then `t ↦ P₀ e^{νtΔ} x'` is the
`∂_j`-derivative path of `t ↦ P₀ e^{νtΔ} x`. -/
theorem seedDerivative : SeedDerivative :=
  seedDerivative_of heatWeakDeriv_proof p0WeakDeriv_proof

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.seedDerivative
