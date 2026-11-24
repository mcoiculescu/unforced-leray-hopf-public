import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_1.Compose

/-!
# `RowTensorFDerivBound`: the derivative of the row stress `w ⊗ w` is bounded

Source: `the November 2 reference manuscript`, lines 261-288. For a smooth field
`w` with `‖w‖ ≤ M` and `‖Dw‖ ≤ M'`, the derivative of `planeRowTensorValue w w` is bounded by
`B = 2 M M'`. Each row is `w z i • planeOfVec (w z)`, whose derivative is
`w z i • D p + (D w_i) • p`, with `p = planeOfVec ∘ w`.
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
open UnforcedLeray.HeatCylinder

theorem rowTensorFDerivBound : RowTensorFDerivBound := by
  intro w M M' hw hM hM'
  have hwd : Differentiable ℝ w := hw.differentiable (by simp)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0)
  have hB0 : 0 ≤ 2 * M * M' := mul_nonneg (mul_nonneg (by norm_num) hM0) hM'0
  refine ⟨2 * M * M', hB0, fun z => ?_⟩
  have ha : HasFDerivAt (fun x => w x 0)
      ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
        (fderiv ℝ w z)) z :=
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp z
      (hwd z).hasFDerivAt
  have hb : HasFDerivAt (fun x => w x 1)
      ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
        (fderiv ℝ w z)) z :=
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp z
      (hwd z).hasFDerivAt
  have hp := ha.prodMk hb
  have hT : HasFDerivAt (planeRowTensorValue w w) _ z :=
    (ha.smul hp).prodMk (hb.smul hp)
  set La := (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
    (fderiv ℝ w z) with hLa_def
  set Lb := (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp
    (fderiv ℝ w z) with hLb_def
  have hw0 : ‖w z 0‖ ≤ M := (PiLp.norm_apply_le (w z) 0).trans (hM z)
  have hw1 : ‖w z 1‖ ≤ M := (PiLp.norm_apply_le (w z) 1).trans (hM z)
  have hp1 : ‖((w z 0, w z 1) : Plane)‖ ≤ M := (norm_planeOfVec_le_hdsi (w z)).trans (hM z)
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 (fun h => ?_)
  have hq : ‖fderiv ℝ w z h‖ ≤ M' * ‖h‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hM' z) (norm_nonneg _))
  have hLa : ‖La h‖ ≤ ‖fderiv ℝ w z h‖ := PiLp.norm_apply_le (fderiv ℝ w z h) 0
  have hLb : ‖Lb h‖ ≤ ‖fderiv ℝ w z h‖ := PiLp.norm_apply_le (fderiv ℝ w z h) 1
  have hpair : ‖((La h, Lb h) : Plane)‖ ≤ ‖fderiv ℝ w z h‖ := by
    rw [Prod.norm_mk]
    exact max_le hLa hLb
  rw [hT.fderiv]
  simp only [ContinuousLinearMap.prod_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [Prod.norm_mk]
  refine max_le ?_ ?_
  · calc ‖w z 0 • (La h, Lb h) + La h • (w z 0, w z 1)‖
        ≤ ‖w z 0 • (La h, Lb h)‖ + ‖La h • (w z 0, w z 1)‖ := norm_add_le _ _
      _ = ‖w z 0‖ * ‖((La h, Lb h) : Plane)‖ + ‖La h‖ * ‖((w z 0, w z 1) : Plane)‖ := by
          rw [norm_smul, norm_smul]
      _ ≤ M * ‖fderiv ℝ w z h‖ + ‖fderiv ℝ w z h‖ * M :=
          add_le_add (mul_le_mul hw0 hpair (norm_nonneg _) hM0)
            (mul_le_mul hLa hp1 (norm_nonneg _) (norm_nonneg _))
      _ ≤ 2 * M * M' * ‖h‖ := by nlinarith [mul_le_mul_of_nonneg_left hq hM0]
  · calc ‖w z 1 • (La h, Lb h) + Lb h • (w z 0, w z 1)‖
        ≤ ‖w z 1 • (La h, Lb h)‖ + ‖Lb h • (w z 0, w z 1)‖ := norm_add_le _ _
      _ = ‖w z 1‖ * ‖((La h, Lb h) : Plane)‖ + ‖Lb h‖ * ‖((w z 0, w z 1) : Plane)‖ := by
          rw [norm_smul, norm_smul]
      _ ≤ M * ‖fderiv ℝ w z h‖ + ‖fderiv ℝ w z h‖ * M :=
          add_le_add (mul_le_mul hw1 hpair (norm_nonneg _) hM0)
            (mul_le_mul hLb hp1 (norm_nonneg _) (norm_nonneg _))
      _ ≤ 2 * M * M' * ‖h‖ := by nlinarith [mul_le_mul_of_nonneg_left hq hM0]

end UnforcedLeray.Short.PartI
