import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Volterra
import UnforcedLeray.Units.B0238.Partials

/-!
# Spatial regularity of the actual train coefficients

The train's defining one-sided smoothness supplies the spatial continuity fields required by the
physical flux map at every nonnegative age. This does not supply global coefficient bounds or
weighted vorticity estimates.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- The actual B0238 train velocity is spatially continuous on every nonnegative age slice. -/
theorem continuous_actualTrainVelocity_slice {ν c s : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) (hs : 0 ≤ s) :
    Continuous (UnforcedLeray.B0238.Vc tr s) :=
  (UnforcedLeray.B0238.contDiff_Vc tr hs).continuous

/-- The actual train curl is spatially continuous on every nonnegative age slice, by taking the
curl of the same B0238 velocity rather than introducing another coefficient field. -/
theorem continuous_actualTrainCurl_slice {ν c s : ℝ}
    (tr : UnforcedLeray.B0140.TrainSol ν c) (hs : 0 ≤ s) :
    Continuous (UnforcedLeray.B0238.Ec tr s) := by
  change Continuous (UnforcedLeray.Cyl.curl (UnforcedLeray.B0238.Vc tr s))
  exact UnforcedLeray.B0238.continuous_curl
    ((UnforcedLeray.B0238.contDiff_Vc tr hs).of_le (by exact_mod_cast le_top))

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.continuous_actualTrainVelocity_slice
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.continuous_actualTrainCurl_slice
