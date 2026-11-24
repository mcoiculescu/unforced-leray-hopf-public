import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Units.B0412

/-!
# The phase pairing is `pairF` on the periodic representative
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

/-- For a genuine phase test, the abstract phase-space pairing agrees with the explicit period
integral `pairF` applied to the canonical phase representative. -/
theorem phasePair_eq_pairF_rep {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    (f : Yq P q0E) :
    phasePair P q0E Φ f =
      pairF P Φ (fun x => rep f x.1 x.2) := by
  rw [phasePair_eq_periodIntegral hΦ f]
  simp only [zero_add, pairF, phaseInt]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro t _
  apply MeasureTheory.integral_congr_ae
  filter_upwards [rep_slice f t] with y hy
  rw [hy]

#print axioms rep_slice
#print axioms stronglyMeasurable_rep
#print axioms rep_add_period
#print axioms contRep_ae
#print axioms contRep_periodic
#print axioms phasePair_eq_pairF_rep

end UnforcedLeray.Cons.C03.Concrete
