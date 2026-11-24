import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Laplacian commutes with isometries (source 4138-4141)

Proves `PhysLapEquivar`: for `f ∈ C²` and a linear isometry `g` with `f ∘ g = g ∘ f`,
`Δf(gy) = g Δf(y)`.  The physical Laplacian `physLap` is the Mathlib Laplacian, and the Mathlib
formula from any orthonormal basis (here the image of the standard basis under `g`) gives the
equivariance.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The derivative of `y' ↦ ∂f(y') u` in direction `v` at a point is `D²f(y)[v, u]`. -/
theorem fderiv_coord_apply (f : Space → Space) (hf : ContDiff ℝ 2 f) (y v u : Space) :
    fderiv ℝ (fun y' => fderiv ℝ f y' u) y v = fderiv ℝ (fderiv ℝ f) y v u := by
  have hc : DifferentiableAt ℝ (fderiv ℝ f) y :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  rw [fderiv_clm_apply hc (differentiableAt_const u)]
  simp

/-- The physical Laplacian is the Mathlib Laplacian of a `C²` map. -/
theorem physLap_eq_laplacian (f : Space → Space) (hf : ContDiff ℝ 2 f) (y : Space) :
    physLap f y = Laplacian.laplacian f y := by
  have hB := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)) y
  rw [hB]
  unfold physLap
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.basisFun_apply]
  unfold physPd2 physPd
  exact fderiv_coord_apply f hf y (coordinateVector j) (coordinateVector j)

theorem physLapEquivar_proved : PhysLapEquivar := by
  intro f g hf hfg y
  set G : Space →L[ℝ] Space := g.toContinuousLinearEquiv.toContinuousLinearMap with hGdef
  have hfun : f ∘ G = G ∘ f := by
    funext x
    exact hfg x
  have hEq := congrArg (fun F => iteratedFDeriv ℝ 2 F y) hfun
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right G hf y (le_refl 2),
    ContinuousLinearMap.iteratedFDeriv_comp_left G (hf.contDiffAt : ContDiffAt ℝ 2 f y)
      (le_refl 2)] at hEq
  have key : ∀ a : Space, iteratedFDeriv ℝ 2 f (g y) ![g a, g a] =
      g (iteratedFDeriv ℝ 2 f y ![a, a]) := by
    intro a
    have h2 := congrArg (fun T => T ![a, a]) hEq
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h2
    have hv : (fun i => G (![a, a] i)) = ![G a, G a] := by
      funext i
      fin_cases i <;> rfl
    have h3 : iteratedFDeriv ℝ 2 f (G y) ![G a, G a] = G (iteratedFDeriv ℝ 2 f y ![a, a]) := by
      rw [← hv]
      simpa using h2
    exact h3
  rw [physLap_eq_laplacian f hf (g y), physLap_eq_laplacian f hf y]
  have hA := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    ((EuclideanSpace.basisFun (Fin 3) ℝ).map g)) (g y)
  have hB := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)) y
  rw [hA, hB, map_sum]
  simp only [OrthonormalBasis.map_apply]
  exact Finset.sum_congr rfl fun i _ => key _

end UnforcedLeray.Short.PartIIIb.Concrete
