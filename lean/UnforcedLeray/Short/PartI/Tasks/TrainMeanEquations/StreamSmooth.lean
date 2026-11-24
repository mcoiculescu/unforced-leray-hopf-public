import UnforcedLeray.Short.PartI.Sub.T01Class
import UnforcedLeray.Short.PartI.Tasks.TrainClass.FluctStreamSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainClass.BUCMeanStreamSmooth

/-!
# Part I, task `PartI:T01/1`: the stream of a BUC train is jointly smooth

Source of record: `the November 2 reference manuscript`, lines 397-404 and
261-288.  The target `TrainStreamSmooth` (`Sub/T01.lean`) is obtained from the two leaf
results `FluctStreamSmooth` (`PartI:TC/7`) and `BUCMeanStreamSmooth` (`PartI:TC/8`) through
`trainStreamSmooth_of` (`Sub/T01Class.lean`): `ψ = (ψ - S) + S`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T01/1`. The stream of a BUC train is jointly smooth** (lines 397-404, 261-288). -/
theorem trainStreamSmooth : TrainStreamSmooth :=
  trainStreamSmooth_of fluctStreamSmooth bucMeanStreamSmooth

end UnforcedLeray.Short.PartI
