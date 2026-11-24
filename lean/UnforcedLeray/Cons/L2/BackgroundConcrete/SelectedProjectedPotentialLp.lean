import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotential
import UnforcedLeray.Lib.LerayLp.Cutoff

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.RieszLp

local instance dual_q0_ge_one : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

/-- The Newton correction in the actual Leray projection has an integrable dual-space tail.
The exponent is the manuscript dual exponent `11/7`; decay is supplied by the explicit
Riesz-pair gradient bound, not assumed as regularity of the projected test. -/
theorem memLp_lerayPotentialGradient_dual_q0
    {f : Fin 3 → Space → ℝ} (hf : ∀ i, IsSpatialTest (f i)) :
    MemLp (gradField (lerayPotential f)) (conjExp q0E) volume := by
  obtain ⟨M, hM⟩ := lerayPotential_grad_decay hf
  have hM0 : 0 ≤ M := by
    have h := hM 0 0
    have hw := powWeight_pos 3 (0 : Space)
    nlinarith [abs_nonneg (spatialTestDerivative 0 (lerayPotential f) 0)]
  have hpow : MemLp (powWeight 3) (conjExp q0E) volume :=
    memLp_powWeight (by norm_num) (by simp [PhaseSpace.conjExp]) (Or.inr (by
      norm_num [PhaseSpace.conjExp, q0E, B0281.q0]))
  have hmajor : MemLp ((3 * M) • powWeight 3) (conjExp q0E) volume :=
    hpow.const_smul (3 * M)
  have hbound : ∀ y, ‖gradField (lerayPotential f) y‖ ≤ (3 * M) * powWeight 3 y := by
    intro y
    calc
      ‖gradField (lerayPotential f) y‖ ≤
          ∑ i : Fin 3, |spatialTestDerivative i (lerayPotential f) y| := by
        simpa [gradField] using
          norm_sum_smul_coordinateVector_le
            (fun i => spatialTestDerivative i (lerayPotential f) y)
      _ ≤ ∑ i : Fin 3, M * powWeight 3 y :=
        Finset.sum_le_sum fun i _ => hM i y
      _ = (3 * M) * powWeight 3 y := by norm_num [Fin.sum_univ_succ]; ring
  have hbound' : ∀ y, ‖gradField (lerayPotential f) y‖ ≤
      ‖((3 * M) • powWeight 3) y‖ := by
    intro y
    calc
      ‖gradField (lerayPotential f) y‖ ≤ (3 * M) * powWeight 3 y := hbound y
      _ = ‖(3 * M) • powWeight 3 y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (3 : ℝ) * M),
          Real.norm_of_nonneg (powWeight_nonneg 3 y)]
  exact hmajor.of_le (continuous_gradField (lerayPotential_contDiff hf)).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound')

#print axioms memLp_lerayPotentialGradient_dual_q0

end UnforcedLeray.Cons.C03.Concrete

end
