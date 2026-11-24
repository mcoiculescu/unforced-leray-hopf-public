import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairingJointRep
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCutoffUncutPairing
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotential
import UnforcedLeray.Lib.LerayLp.Leray

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace
open UnforcedLeray.RieszLp
open UnforcedLeray.B0412

local instance dual_ge_one_phasePair : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

/-- A compact smooth phase test and its actual slice-wise Leray projection have the same pairing
against every phase-solenoidal `Y_{11/4}` field. The only correction used is the canonical
Re/Im Newton-gradient field, whose uncut pairing was proved by cutoff limits. -/
theorem phasePair_lerayProjected_eq_of_phaseSolenoidal
    {P : ℝ} [Fact (0 < P)] {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ)
    {w : Yq P q0E} (hw : IsPhaseSolenoidal w) :
    phasePair P q0E (lerayProjectedPhaseTest
      (one_lt_of_holderConjugate q0E_ne_top) (conjExp_ne_top one_lt_q0E)
      (hΦ.isSliceTest (conjExp q0E))) w = phasePair P q0E Φ w := by
  let hr1 : 1 < conjExp q0E := one_lt_of_holderConjugate q0E_ne_top
  let hrtop : conjExp q0E ≠ ⊤ := conjExp_ne_top one_lt_q0E
  let hs : IsSliceTest P (conjExp q0E) Φ := hΦ.isSliceTest (conjExp q0E)
  let Ψ : SpaceTime → CVec3 := lerayProjectedPhaseTest hr1 hrtop hs
  let hproj : IsSliceTest P (conjExp q0E) Ψ := isSliceTest_lerayProjectedPhaseTest hr1 hrtop hs
  let hneg : IsSliceTest P (conjExp q0E) ((-1 : ℂ) • Φ) := hs.const_smul (-1)
  let D : SpaceTime → CVec3 := fun z => Ψ z + (-1 : ℂ) • Φ z
  have hD : IsSliceTest P (conjExp q0E) D := by
    change IsSliceTest P (conjExp q0E) (Ψ + (-1 : ℂ) • Φ)
    exact hproj.add hneg
  let G : SpaceTime → CVec3 := projectedPotentialNewtonCorrectionField Φ
  let W : SpaceTime → CVec3 := fun z => rep w z.1 z.2
  have hDae (τ : ℝ) : (fun y : Space => D (τ, y)) =ᵐ[volume]
      fun y => G (τ, y) := by
    have hnewton := lerayProjectedPhaseTest_eq_newtonPotentialGrad_ae hr1 hrtop hΦ τ
    filter_upwards [hnewton] with y hy
    change Ψ (τ, y) + (-1 : ℂ) • Φ (τ, y) = G (τ, y)
    simp only [Ψ, G, projectedPotentialNewtonCorrectionField,
      projectedPotentialRePath, projectedPotentialImPath]
    rw [hy]
    simp [smul_eq_mul, add_assoc, add_comm, add_left_comm]
  have hpair : pairF P D W = pairF P G W := by
    unfold pairF phaseInt
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro τ _
    apply integral_congr_ae
    filter_upwards [hDae τ, rep_slice w τ] with y hdy hwrep
    rw [hdy]
  have hphaseD : phasePair P q0E D w = 0 := by
    rw [phasePair_eq_pairF_rep_of_sliceTest hD w, hpair]
    exact pairF_projectedNewtonCorrection_eq_zero_of_phaseSolenoidal hΦ hw
  have htestElemD : testElem P (conjExp q0E) D =
      testElem P (conjExp q0E) Ψ + (-1 : ℂ) • testElem P (conjExp q0E) Φ := by
    change testElem P (conjExp q0E) (Ψ + (-1 : ℂ) • Φ) = _
    rw [testElem_add hproj hneg, testElem_const_smul hs (-1)]
  have hlinear : phasePair P q0E D w =
      phasePair P q0E Ψ w - phasePair P q0E Φ w := by
    simp only [phasePair]
    rw [htestElemD, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hEq := hlinear.symm.trans hphaseD
  exact sub_eq_zero.mp hEq

#print axioms phasePair_lerayProjected_eq_of_phaseSolenoidal

end UnforcedLeray.Cons.C03.Concrete

end
