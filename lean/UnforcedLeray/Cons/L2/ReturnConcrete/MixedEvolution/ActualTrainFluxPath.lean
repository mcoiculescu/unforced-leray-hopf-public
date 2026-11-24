import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.TrainCoefficientSlices
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.Volterra

/-!
# Train-linked physical flux path constructor

This constructor fixes the coefficient fields to B0238's actual Vc and Ec. Its remaining inputs
are the all-age coefficient bounds and strong continuity estimate; the spatial continuity fields
are derived from the TrainSol smoothness.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane
open UnforcedLeray.Train (Vec)

/-- The physical flux operator of B0238's actual train coefficients at a nonnegative age. -/
def actualTrainFluxAtNonneg {ν c m s : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (hs : 0 ≤ s)
    {Cv CE : ℝ} (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hV : ∀ x i, |UnforcedLeray.B0238.Vc tr s x i| ≤ Cv)
    (hE : ∀ x ∈ cell c, |bracket x ^ m * UnforcedLeray.B0238.Ec tr s x| ≤ CE) :
    ActualVorticity (c := c) (m := m) hm →L[ℝ] ActualFlux (c := c) (m := m) :=
  physicalFluxKernelCLM hm (UnforcedLeray.B0238.Vc tr s)
    (UnforcedLeray.B0238.Ec tr s)
    (continuous_actualTrainVelocity_slice tr hs)
    (continuous_actualTrainCurl_slice tr hs) hCv hCE hV hE

/-- Build the fixed-cylinder train flux path using only explicit source-coefficient bounds and
strong continuity of its actual physical flux operator. No unrelated velocity/curl fields can be
substituted. -/
def actualTrainFluxPathOfBounds {ν c m : ℝ} [Fact (0 < c)]
    (hm : 1 ≤ m) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (Cv CE : ℝ) (hCv : 0 ≤ Cv) (hCE : 0 ≤ CE)
    (hV : ∀ t, 0 ≤ t → ∀ x i, |UnforcedLeray.B0238.Vc tr t x i| ≤ Cv)
    (hE : ∀ t, 0 ≤ t → ∀ x ∈ cell c,
      |bracket x ^ m * UnforcedLeray.B0238.Ec tr t x| ≤ CE)
    (hflux : ∀ w : ActualVorticity (c := c) (m := m) hm,
      Continuous (fun t => actualTrainFluxAtNonneg (s := max t 0) hm tr
        (le_max_right t 0) hCv hCE
        (hV (max t 0) (le_max_right t 0))
        (hE (max t 0) (le_max_right t 0)) w)) :
    ActualTrainFluxPath (c := c) (m := m) hm (ν := ν) tr where
  Cv := Cv
  CE := CE
  hCv := hCv
  hCE := hCE
  v := UnforcedLeray.B0238.Vc tr
  E := UnforcedLeray.B0238.Ec tr
  continuous_v := fun t ht => continuous_actualTrainVelocity_slice tr ht
  continuous_E := fun t ht => continuous_actualTrainCurl_slice tr ht
  velocity_eq := fun t ht => rfl
  curl_eq := fun t ht => rfl
  velocity_bound := hV
  weighted_curl_bound := hE
  continuous_flux_apply := by
    intro w
    simpa [actualTrainFluxAtNonneg] using hflux w

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualTrainFluxAtNonneg
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualTrainFluxPathOfBounds
