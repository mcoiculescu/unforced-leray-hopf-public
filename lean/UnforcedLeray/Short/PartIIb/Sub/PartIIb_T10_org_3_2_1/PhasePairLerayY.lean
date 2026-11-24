import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1_defs
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_2

/-!
# `PartII-b:T10/org/3/2/1`: the phase pairing transposes the Leray projection (`PhasePairLerayY`)

Source of record `the November 2 reference manuscript`,
line 1364 (the projected inverse applies the Cartesian Leray projection to the datum) and lines
1365-1366 (at `r = 2` the adjoint has the same graph: `ℙ` is symmetric).

Both pairings are phase integrals of the slice pairing `innerPair 2` (`phasePairing_apply`); the
slices of `ℙf` are `lerayC 2 (f τ)` a.e. (`coeFn_lerayY`), those of the projected test are
`lerayC 2' (Φ(τ))`, and the slice symmetry `LerayCSymm` (`lerayCSymm_proof`) moves `ℙ` across.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb.LTS

open UnforcedLeray.PhaseSpace UnforcedLeray.RieszLp UnforcedLeray.Cons.C03.Concrete

set_option maxHeartbeats 1600000 in
/-- **`PhasePairLerayY`**: `⟪Φ, ℙf⟫ = ⟪ℙΦ, f⟫` for a slice test `Φ` in `L^{2'}` and `f ∈ Y_2`. -/
theorem phasePairLerayY_proof : PhasePairLerayY := by
  intro P _ Φ hΦ f
  have hp := isSliceTest_lerayProjectedPhaseTest one_lt_conjExp_two conjExp_two_ne_top hΦ
  have hslice : ∀ τ : AddCircle P, circleSlice hp τ =
      lerayC (conjExp 2) one_lt_conjExp_two conjExp_two_ne_top (circleSlice hΦ τ) := by
    intro τ
    induction τ using QuotientAddGroup.induction_on with
    | H t =>
      rw [circleSlice_coe, circleSlice_coe]
      exact Lp.toLp_coeFn
        (lerayC (conjExp 2) one_lt_conjExp_two conjExp_two_ne_top (sliceMap hΦ.2 t)) _
  simp only [phasePair]
  rw [phasePairing_apply, phasePairing_apply, testElem_of hΦ, testElem_of hp]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp 2) (volume : Measure Space))
      (p := conjExp 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hΦ),
    ContinuousMap.coeFn_toLp (E := Lp CVec3 (conjExp 2) (volume : Measure Space))
      (p := conjExp 2) (𝕜 := ℂ) AddCircle.haarAddCircle (circleSlice hp),
    coeFn_lerayY ENNReal.one_lt_two ENNReal.ofNat_ne_top f] with τ hτΦ hτp hτf
  rw [hτΦ, hτp, hτf, hslice τ]
  exact lerayCSymm_proof 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top one_lt_conjExp_two
    conjExp_two_ne_top (circleSlice hΦ τ) (f τ)

#print axioms phasePairLerayY_proof

end UnforcedLeray.Short.IIb.LTS
