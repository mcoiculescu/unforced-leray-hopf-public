import UnforcedLeray.Analysis.Heat.KernelEvolution
import UnforcedLeray.Analysis.SobolevGraph.MixedPartials

/-!
# Commuting the scalar Laplacian with spatial test derivatives

The scalar Laplacian and coordinate derivatives are the actual Fréchet
expressions used by the heat kernel and pressure identities. Finite-sum
differentiation and the proved symmetry of smooth test derivatives show that
taking one coordinate derivative commutes with the Laplacian.
-/

noncomputable section
open scoped ContDiff
namespace UnforcedLeray

/-- Differentiating a finite sum of smooth spatial tests differentiates each
summand. -/
lemma spatialTestDerivative_sum (f : Fin 3 → Space → ℝ)
    (hf : ∀ j, IsSpatialTest (f j)) (i : Fin 3) (x : Space) :
    spatialTestDerivative i (fun y => ∑ j : Fin 3, f j y) x =
      ∑ j : Fin 3, spatialTestDerivative i (f j) x := by
  unfold spatialTestDerivative
  rw [(HasFDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    (((hf j).smooth.differentiable (by simp)).differentiableAt).hasFDerivAt)).fderiv]
  simp

/-- The actual scalar Laplacian commutes with each coordinate derivative of
a compact smooth spatial test. -/
lemma Heat.laplacian_spatialTestDerivative {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) (i : Fin 3) (x : Space) :
    Heat.laplacian (spatialTestDerivative i φ) x =
      spatialTestDerivative i (Heat.laplacian φ) x := by
  change (∑ j : Fin 3, spatialTestDerivative j
      (spatialTestDerivative j (spatialTestDerivative i φ)) x) =
    spatialTestDerivative i
      (fun y => ∑ j : Fin 3, spatialTestDerivative j (spatialTestDerivative j φ) y) x
  rw [spatialTestDerivative_sum _ (fun j => (hφ.derivative j).derivative j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [SobolevGraph.spatialTestDerivative_comm hφ j i]
  exact congrFun (SobolevGraph.spatialTestDerivative_comm (hφ.derivative j) j i) x

end UnforcedLeray
