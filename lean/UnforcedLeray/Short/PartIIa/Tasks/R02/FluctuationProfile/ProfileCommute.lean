import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import UnforcedLeray.Units.B0184

/-!
# Helper for `PartII-a:R02`, target `lateFluctuationProfile_of`: local commutation of profile partials

`Analysis/RingLift/ProfileCalculus.lean` (`partial_comm`) proves `∂_v ∂_w G = ∂_w ∂_v G` for a
globally `C²` profile `G`.  The fluctuation profile is only `C^∞` on `{s > 0}`, so this helper is the
pointwise version: `ContDiffAt ℝ 2 G x` at the point suffices.  Source of the mixed-derivative
identities used: `the November 2 reference manuscript`, lines 439-446 (`sct:fluctuation`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.FluctuationProfile

open UnforcedLeray.B0184

/-- Pointwise symmetry of second directional derivatives of a profile `G` that is `C²` at `x`. -/
theorem profile_fderiv_comm_at {G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hG : ContDiffAt ℝ 2 G x) (v w : ProfilePoint) :
    fderiv ℝ (fun y => fderiv ℝ G y v) x w = fderiv ℝ (fun y => fderiv ℝ G y w) x v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ G) x :=
    (hG.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hv : fderiv ℝ (fun y => fderiv ℝ G y v) x w = fderiv ℝ (fderiv ℝ G) x w v := by
    rw [fderiv_clm_apply hD (differentiableAt_const (x := x) v)]
    simp
  have hw : fderiv ℝ (fun y => fderiv ℝ G y w) x v = fderiv ℝ (fderiv ℝ G) x v w := by
    rw [fderiv_clm_apply hD (differentiableAt_const (x := x) w)]
    simp
  rw [hv, hw]
  exact (hG.isSymmSndFDerivAt (by norm_num : minSmoothness ℝ 2 ≤ (2 : ℕ∞ω))) w v

/-- The profile age and `η` partial derivatives commute at a point where the profile is `C²`. -/
theorem partialEta_partialAge_comm_at {G : ProfilePoint → ℝ} {x : ProfilePoint}
    (hG : ContDiffAt ℝ 2 G x) :
    partialEta (partialAge G) x = partialAge (partialEta G) x := by
  unfold partialEta partialAge
  exact (profile_fderiv_comm_at hG eηDir esDir).symm

end UnforcedLeray.Short.PartIIa.FluctuationProfile
