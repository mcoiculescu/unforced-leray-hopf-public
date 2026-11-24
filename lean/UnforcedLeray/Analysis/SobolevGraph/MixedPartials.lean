import UnforcedLeray.Analysis.WeakDerivative
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Commutation of actual weak mixed partials

The ordered second derivatives used in the target's H² representation are
symmetric almost everywhere. This follows from symmetry of the second
Fréchet derivative of smooth scalar test functions and uniqueness of locally
integrable distributions, with actual L² hypotheses on the second derivatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.SobolevGraph

private theorem test_second_derivative_formula {φ : Space → ℝ}
    (hφ : IsSpatialTest φ) (i j : Fin 3) (x : Space) :
    spatialTestDerivative i (spatialTestDerivative j φ) x =
      fderiv ℝ (fderiv ℝ φ) x (coordinateVector i) (coordinateVector j) := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (ContDiff.fderiv_right (m := ∞) hφ.smooth (by simp)).differentiable (by simp)
  have hx : HasFDerivAt (fun y => fderiv ℝ φ y (coordinateVector j))
      ((fderiv ℝ (fderiv ℝ φ) x).flip (coordinateVector j)) x := by
    simpa using (hd x).hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector j) x)
  unfold spatialTestDerivative
  rw [hx.fderiv]
  rfl

/-- The smooth coordinate test derivatives commute as actual functions. -/
theorem spatialTestDerivative_comm {φ : Space → ℝ} (hφ : IsSpatialTest φ) (i j : Fin 3) :
    spatialTestDerivative i (spatialTestDerivative j φ) =
      spatialTestDerivative j (spatialTestDerivative i φ) := by
  funext x
  rw [test_second_derivative_formula hφ i j x, test_second_derivative_formula hφ j i x]
  exact (hφ.smooth.contDiffAt.isSymmSndFDerivAt (by simp)).eq
    (coordinateVector i) (coordinateVector j)

/-- If q=∂j∂i f and r=∂i∂j f are genuine L² weak derivatives, they agree a.e. -/
theorem weak_second_symmetry {i j : Fin 3} {f gi gj q r : SpatialField}
    (hi : HasWeakSpatialDerivative i f gi) (hj : HasWeakSpatialDerivative j f gj)
    (hij : HasWeakSpatialDerivative j gi q) (hji : HasWeakSpatialDerivative i gj r)
    (hq : MemLp q 2 volume) (hr : MemLp r 2 volume) : q =ᵐ[volume] r := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (hq.locallyIntegrable (by norm_num)) (hr.locallyIntegrable (by norm_num))
  intro φ hφs hφc
  let hφ : IsSpatialTest φ := ⟨hφs, hφc⟩
  have hleft := hi.identity (spatialTestDerivative j φ) (hφ.derivative j)
  rw [hij.identity φ hφ, neg_neg] at hleft
  have hright := hj.identity (spatialTestDerivative i φ) (hφ.derivative i)
  rw [hji.identity φ hφ, neg_neg] at hright
  calc
    (∫ x, φ x • q x) = ∫ x, spatialTestDerivative i (spatialTestDerivative j φ) x • f x :=
      hleft.symm
    _ = ∫ x, spatialTestDerivative j (spatialTestDerivative i φ) x • f x := by
      rw [spatialTestDerivative_comm hφ i j]
    _ = ∫ x, φ x • r x := hright

end UnforcedLeray.SobolevGraph
