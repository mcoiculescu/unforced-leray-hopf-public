import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Lib.PhaseSpace.Pairing
import UnforcedLeray.Units.B0412

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.B0412

/-- For any genuine slice test, the abstract phase pairing agrees with the normalized iterated
integral against the actual canonical representative of the second argument. -/
theorem phasePair_eq_periodIntegral_of_sliceTest {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsSliceTest P (conjExp q0E) Φ)
    (w : Yq P q0E) :
    phasePair P q0E Φ w = (P⁻¹ : ℝ) •
      ∫ t in Ioc (0 : ℝ) (0 + P),
        ∫ y, dotL (Φ (t, y)) ((w (t : AddCircle P) : Space → CVec3) y) := by
  rw [phasePair, phasePairing_apply, testElem_of hΦ]
  have h1 : (fun τ : AddCircle P => innerPair q0E
      ((ContinuousMap.toLp (E := Lp CVec3 (conjExp q0E) (volume : Measure Space))
        (conjExp q0E) AddCircle.haarAddCircle ℂ (circleSlice hΦ)) τ) (w τ)) =ᵐ[AddCircle.haarAddCircle]
      fun τ => innerPair q0E (circleSlice hΦ τ) (w τ) := by
    filter_upwards [ContinuousMap.coeFn_toLp
      (E := Lp CVec3 (conjExp q0E) (volume : Measure Space))
      (p := conjExp q0E) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hΦ)] with τ hτ
    rw [hτ]
  rw [integral_congr_ae h1, AddCircle.integral_haarAddCircle,
    ← AddCircle.integral_preimage (T := P) (0 : ℝ)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [circleSlice_coe, innerPair_apply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (hΦ.2.memLp t)] with y hy
  simp only [sliceMap]
  rw [hy]

/-- The slice-test period formula is `pairF` on the selected joint representative. -/
theorem phasePair_eq_pairF_rep_of_sliceTest {P : ℝ} [Fact (0 < P)]
    {Φ : ℝ × Space → CVec3} (hΦ : IsSliceTest P (conjExp q0E) Φ)
    (w : Yq P q0E) :
    phasePair P q0E Φ w = pairF P Φ (fun x => rep w x.1 x.2) := by
  rw [phasePair_eq_periodIntegral_of_sliceTest hΦ w]
  simp only [zero_add, pairF, phaseInt]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  apply integral_congr_ae
  filter_upwards [rep_slice w t] with y hy
  rw [hy]

#print axioms phasePair_eq_periodIntegral_of_sliceTest
#print axioms phasePair_eq_pairF_rep_of_sliceTest

end UnforcedLeray.Cons.C03.Concrete

end
