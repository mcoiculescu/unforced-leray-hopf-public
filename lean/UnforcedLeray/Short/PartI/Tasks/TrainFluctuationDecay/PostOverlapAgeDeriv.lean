import UnforcedLeray.Short.PartI.Sub.PartI_T22_2
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecay.PostOverlapAgeDeriv.VelFluctHigherStep
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecay.PostOverlapAgeDeriv.PressureHigherStep

/-!
# `PartI:T22/2`: Post-overlap higher age-derivative (`ℓ ≥ 1`) fluctuation decay

Source of record: `the November 2 reference manuscript`, lines 439-446, 523-526.

All unconditional base-case (`ℓ = 0`) bounds (`trainPostOverlapAgeDeriv_zero`,
`trainPostOverlapVelPressOrderSup_zero`), the general-`r` upgrade from unweighted `(v_fluct, tr.p)`
bounds to full `(wCellL2 c 0 ∧ wSupNorm 0)` bounds for `(ψ_fluct, v_fluct, tr.p)`
(`trainPostOverlapFullOrder_of_velPressSup`), the unconditional viscous and pressure-gradient step
bounds (`trainPostOverlapViscFluct_of_order`, `trainPostOverlapGradSPress_of_order`), the strong
induction in `ℓ` (`trainPostOverlapVelPressOrderSup_all`), and the conditional assembly
`trainPostOverlapAgeDerivFromZero_of` from the two step leaves
`TrainPostOverlapVelFluctHigherStep` (`PartI:T22/2/1`) and
`TrainPostOverlapPressureHigherStep` (`PartI:T22/2/2`) are proved in
`UnforcedLeray.Short.PartI.Sub.PartI_T22_2`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem trainPostOverlapAgeDerivFromZero_proof (hTails : TrainStreamVelocityPressureTails) :
    TrainPostOverlapAgeDerivFromZero := by
  exact trainPostOverlapAgeDerivFromZero_of
    trainPostOverlapVelFluctHigherStep_proof trainPostOverlapPressureHigherStep_proof hTails

end UnforcedLeray.Short.PartI
