import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductActualIBP
import UnforcedLeray.Lib.Sobolev.TestDomain
import UnforcedLeray.Lib.Sobolev.WeakDeriv

/-! Actual whole-spacetime weak spatial derivative of the compact-test/background product. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint
open UnforcedLeray.PhaseSpace
open UnforcedLeray.Sob

/-- The three spatial directions embedded into spacetime with zero phase component. -/
def scalarTestSpaceTimeDir (j : Fin 3) : SpaceTime :=
  (0, EuclideanSpace.single j (1 : ℝ))

/-- The scalar product `Φ·U` has its actual weak spatial derivatives on whole spacetime. -/
theorem hasWeakSpatialDerivative_scalarTestBackground {P : ℝ}
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ)
    {U : ℝ → SpatialField} (hU : IsBoundedBackground U) (j : Fin 3) :
    HasWeakDeriv
      (wholeSpaceOf SpaceTime volume scalarTestSpaceTimeDir)
      [scalarTestSpaceTimeDir j]
      (fun z : SpaceTime => scalarTestBackground Φ U z)
      (fun z : SpaceTime =>
        fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2
          (EuclideanSpace.single j (1 : ℝ))) := by
  let e : Space := EuclideanSpace.single j (1 : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · intro ψ hψ
    rcases hψ with ⟨hψs, hψc⟩
    obtain ⟨hleft, hright, _⟩ := scalarTestBackground_linePairings_integrable hΦ hU hψs hψc j
    simpa [e, scalarTestSpaceTimeDir, iterDirDeriv_singleton, wholeSpaceOf_μ] using hleft
  · intro ψ hψ
    rcases hψ with ⟨hψs, hψc⟩
    obtain ⟨_, hright, _⟩ := scalarTestBackground_linePairings_integrable hΦ hU hψs hψc j
    simpa [e, scalarTestSpaceTimeDir, wholeSpaceOf_μ] using hright
  · intro ψ hψ
    rcases hψ with ⟨hψs, hψc⟩
    have hIBP := integral_spatialIBP_scalarTestBackground hΦ hU hψs hψc j
    have hrev :
        ∫ z : SpaceTime, fderiv ℝ ψ z (scalarTestSpaceTimeDir j) •
          scalarTestBackground Φ U z =
        -∫ z : SpaceTime, ψ z •
          fderiv ℝ (fun x : Space => scalarTestBackground Φ U (z.1, x)) z.2 e := by
      have hneg := congrArg (fun w : ℂ => -w) hIBP
      simpa [e, scalarTestSpaceTimeDir, neg_neg] using hneg.symm
    simpa [e, scalarTestSpaceTimeDir, iterDirDeriv_singleton,
      wholeSpaceOf_μ, List.length_singleton, pow_one, neg_smul, one_smul] using hrev

#print axioms hasWeakSpatialDerivative_scalarTestBackground

end UnforcedLeray.Cons.C03.Concrete
