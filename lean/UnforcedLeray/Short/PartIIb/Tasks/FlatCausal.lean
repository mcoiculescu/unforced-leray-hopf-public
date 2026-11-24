import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelMeasurable
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelSolenoidal
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation

/-!
# Part II-b, task `PartII-b:T12`: existence and `H_r` bound of the flat response (assembly)

Source of record: `the November 2 reference manuscript`, lines 1920-1930.
The conditional assembly `flatCausalExists_of` (`Sub/T12.lean`) is applied to the seven proved leaves
`cylinderHelmholtzLr`, `flatLerayLiftOfSlice`, `duhamelMeasurable`, `duhamelBound`, `duhamelPeriodic`,
`duhamelSolenoidal`, `duhamelEquation`. No added hypotheses.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12`** (`FlatCausalExists`): existence of the flat response with the `H_r`
bound, assembled from the seven leaves. -/
theorem flatCausalExists : UnforcedLeray.Short.IIb.FlatCausalExists :=
  flatCausalExists_of cylinderHelmholtzLr flatLerayLiftOfSlice duhamelMeasurable duhamelBound
    duhamelPeriodic duhamelSolenoidal duhamelEquation

end UnforcedLeray.Short.IIb

end
