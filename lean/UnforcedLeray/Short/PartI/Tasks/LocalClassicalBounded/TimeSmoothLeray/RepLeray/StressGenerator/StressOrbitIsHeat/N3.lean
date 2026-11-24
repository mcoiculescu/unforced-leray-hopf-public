import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Needed

/-!
# N3: pointwise divergence of the row stress `w ⊗ w` is the advection

Proof of `NeedRowTensorDivergence` from `Needed.lean`, mirroring
`RowTensorDivergence.lean` (`rowTensorDivergence_eq_advection`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-- The product rule for a pointwise product of two differentiable real functions. -/
theorem fderiv_mul_apply_plane_N3 {f g : Plane → ℝ} (z : Plane) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v : Plane) :
    fderiv ℝ (fun x => f x * g x) z v =
      f z * fderiv ℝ g z v + g z * fderiv ℝ f z v := by
  rw [fderiv_fun_mul (hf z) (hg z)]
  simp only [add_apply, smul_apply, smul_eq_mul]

theorem needRowTensorDivergence : NeedRowTensorDivergence := by
  intro w hw hdiv z
  have h0 : ContDiff ℝ ∞ (fun x => w x 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).contDiff.comp hw
  have h1 : ContDiff ℝ ∞ (fun x => w x 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).contDiff.comp hw
  have d0 : Differentiable ℝ (fun x => w x 0) := h0.differentiable (by simp)
  have d1 : Differentiable ℝ (fun x => w x 1) := h1.differentiable (by simp)
  have hd : fderiv ℝ (fun x => w x 0) z (1, 0) + fderiv ℝ (fun x => w x 1) z (0, 1) = 0 := by
    have hz := hdiv z
    unfold Cyl.divergence at hz
    rwa [Cyl.partialQ_eq_fderiv d0 z, Cyl.partialEta_eq_fderiv d1 z] at hz
  have e11 : (fun x => (planeRowTensorValue w w x).1.1) = fun x => w x 0 * w x 0 := by
    funext x
    simp [planeRowTensorValue, planeOfVec, smul_eq_mul]
  have e12 : (fun x => (planeRowTensorValue w w x).1.2) = fun x => w x 0 * w x 1 := by
    funext x
    simp [planeRowTensorValue, planeOfVec, smul_eq_mul]
  have e21 : (fun x => (planeRowTensorValue w w x).2.1) = fun x => w x 1 * w x 0 := by
    funext x
    simp [planeRowTensorValue, planeOfVec, smul_eq_mul]
  have e22 : (fun x => (planeRowTensorValue w w x).2.2) = fun x => w x 1 * w x 1 := by
    funext x
    simp [planeRowTensorValue, planeOfVec, smul_eq_mul]
  have p11 : fderiv ℝ (fun x => w x 0 * w x 0) z (1, 0) =
      w z 0 * fderiv ℝ (fun x => w x 0) z (1, 0) + w z 0 * fderiv ℝ (fun x => w x 0) z (1, 0) :=
    fderiv_mul_apply_plane_N3 z d0 d0 _
  have p21 : fderiv ℝ (fun x => w x 1 * w x 0) z (0, 1) =
      w z 1 * fderiv ℝ (fun x => w x 0) z (0, 1) + w z 0 * fderiv ℝ (fun x => w x 1) z (0, 1) :=
    fderiv_mul_apply_plane_N3 z d1 d0 _
  have p12 : fderiv ℝ (fun x => w x 0 * w x 1) z (1, 0) =
      w z 0 * fderiv ℝ (fun x => w x 1) z (1, 0) + w z 1 * fderiv ℝ (fun x => w x 0) z (1, 0) :=
    fderiv_mul_apply_plane_N3 z d0 d1 _
  have p22 : fderiv ℝ (fun x => w x 1 * w x 1) z (0, 1) =
      w z 1 * fderiv ℝ (fun x => w x 1) z (0, 1) + w z 1 * fderiv ℝ (fun x => w x 1) z (0, 1) :=
    fderiv_mul_apply_plane_N3 z d1 d1 _
  unfold rowDivergence Train.advection
  simp only [e11, e12, e21, e22]
  rw [p11, p12, p21, p22, Cyl.partialQ_eq_fderiv d0 z, Cyl.partialEta_eq_fderiv d0 z,
    Cyl.partialQ_eq_fderiv d1 z, Cyl.partialEta_eq_fderiv d1 z]
  congr 1
  refine Prod.ext ?_ ?_
  · dsimp only
    linear_combination (w z 0) * hd
  · dsimp only
    linear_combination (w z 1) * hd

end UnforcedLeray.Short.PartI
