import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1

/-!
# Part I, `PartI:T02/1/4/4/1/5/1/1/3`: pointwise tensor divergence

Target: `RowDivTensorPointwise` (`Sub/PartI_T02_1_4_4_1_5_1_1.lean`), source lines 3594-3625.

For smooth `u`, `∂_q(u₀ u) + ∂_η(u₁ u) = (u·∇)u + (div u) u`, pointwise, without solenoidality.
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

theorem rowDivTensorPointwise : RowDivTensorPointwise := by
  intro c u hu z
  have hA : Differentiable ℝ (fun x => u x 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
      hu.smooth).differentiable (by simp)
  have hB : Differentiable ℝ (fun x => u x 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
      hu.smooth).differentiable (by simp)
  have e11 : (fun x => (planeRowTensorValue u u x).1.1) = fun x => u x 0 * u x 0 := by
    funext x; simp [planeRowTensorValue, planeOfVec]
  have e21 : (fun x => (planeRowTensorValue u u x).2.1) = fun x => u x 1 * u x 0 := by
    funext x; simp [planeRowTensorValue, planeOfVec]
  have e12 : (fun x => (planeRowTensorValue u u x).1.2) = fun x => u x 0 * u x 1 := by
    funext x; simp [planeRowTensorValue, planeOfVec]
  have e22 : (fun x => (planeRowTensorValue u u x).2.2) = fun x => u x 1 * u x 1 := by
    funext x; simp [planeRowTensorValue, planeOfVec]
  have prod : ∀ (f g : Plane → ℝ), Differentiable ℝ f → Differentiable ℝ g → ∀ v : Plane,
      fderiv ℝ (fun x => f x * g x) z v = f z * fderiv ℝ g z v + g z * fderiv ℝ f z v := by
    intro f g hf hg v
    rw [show (fun x => f x * g x) = f * g from rfl, fderiv_mul hf.differentiableAt hg.differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp only [rowDivergence, e11, e21, e12, e22, prod _ _ hA hA, prod _ _ hB hA,
    prod _ _ hA hB, prod _ _ hB hB, Train.advection, Cyl.divergence,
    Cyl.partialQ_eq_fderiv hA, Cyl.partialEta_eq_fderiv hA,
    Cyl.partialQ_eq_fderiv hB, Cyl.partialEta_eq_fderiv hB]
  ext i
  fin_cases i <;> simp <;> ring

end UnforcedLeray.Short.PartI
