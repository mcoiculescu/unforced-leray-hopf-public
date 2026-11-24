import UnforcedLeray.Short.PartI.Sub.T02_1_2_2

/-!
# Part I, task `PartI:T02/1/2/2`, leaf L1: `WeakDerivCell`

Source of record: `the November 2 reference manuscript`, lines 261-288.
For `x, x' ∈ H³`, `x'` is the periodic weak `∂_j`-derivative of `x` iff the `∂_j` component of `x`
and the value component of `x'` have the same `L²`-cell class.  No `sorry`, `admit`, `axiom` or
`native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem weakDerivCell_proof : WeakDerivCell := by
  intro c _hc j x x'
  have hw := Sob.W.hasWeakDeriv x (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2))
  rw [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero] at hw
  have hxloc : LocallyIntegrable (Cyl.H.val x' : Plane → Vec) (Sob.cylinder c).μ :=
    Sob.locallyIntegrable_of_memLp (Lp.memLp _)
  have hdloc : LocallyIntegrable
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) x : Plane → Vec) (Sob.cylinder c).μ :=
    Sob.locallyIntegrable_of_memLp (Lp.memLp _)
  constructor
  · intro h
    have hae := h.ae_unique hw hxloc hdloc
    have hlp : Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) x =
        Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 Sob.Idx.zero x' := by
      apply Lp.ext
      exact ((Sob.ae_eq_wμ_iff _ _).mpr hae).symm
    exact congrArg (weightedToCellL2Isometry c) hlp
  · intro h
    have hlp : Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) x =
        Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 Sob.Idx.zero x' :=
      (weightedToCellL2Isometry c).injective h
    have hae : (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
        (Sob.Idx.cons j (Sob.Idx.zero : Sob.Idx 2 2)) x : Plane → Vec) =ᵐ[(Sob.cylinder c).μ]
        (Cyl.H.val x' : Plane → Vec) := by
      rw [← Sob.ae_eq_wμ_iff]
      exact (Lp.ext_iff.mp hlp)
    exact hw.congr_ae (Filter.EventuallyEq.refl _ _) hae

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.weakDerivCell_proof
