import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedCurlIsLeray
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialLp
import UnforcedLeray.Units.B0005.Bridge.Solenoidal

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp
open UnforcedLeray.B0412

local instance dual_ge_one_projectionLp : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

/-- The actual Newton-curl representative of the Leray projection belongs to the dual exponent
for every phase. This is the value-space input needed before taking compact curl cutoffs. -/
theorem memLp_projectedTestNewtonCurl_dual_q0
    {P : ℝ} {Φ : SpaceTime → Space} (hΦ : IsPhaseTest P Φ) (τ : ℝ) :
    MemLp (fun y : Space =>
      spatialCurlST (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z)
        (τ, y)) (conjExp q0E) volume := by
  let f : Fin 3 → Space → ℝ := fun i y => Φ (τ, y) i
  have hf : ∀ i, IsSpatialTest (f i) := fun i => by
    refine ⟨(EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp
      (hΦ.smooth.comp (contDiff_const.prodMk contDiff_id)), ?_⟩
    obtain ⟨R, hR⟩ := hΦ.bounded_support
    exact UnforcedLeray.B0005.hasCompactSupport_of_bound (R := R) fun y hy => by
      simp [f, hR τ y hy]
  have hvec : MemLp (vecField f) (conjExp q0E) volume :=
    memLp_vecField hf (conjExp q0E)
  have hgrad : MemLp (gradField (lerayPotential f)) (conjExp q0E) volume :=
    memLp_lerayPotentialGradient_dual_q0 hf
  have hsum : MemLp (vecField f + gradField (lerayPotential f))
      (conjExp q0E) volume := hvec.add hgrad
  have hEq : (fun y : Space =>
      spatialCurlST (fun z => spatialCurlST (projectedTestNewtonVectorPotential Φ) z)
        (τ, y)) = vecField f + gradField (lerayPotential f) := by
    funext y
    simpa [f] using projectedTestNewtonCurl_eq_projectionFormula hΦ τ y
  rw [hEq]
  exact hsum

#print axioms memLp_projectedTestNewtonCurl_dual_q0

end UnforcedLeray.Cons.C03.Concrete

end
