import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1

/-!
# Part I, `PartI:T02/1/4/4/1/5/1/1/1`: the smooth representative of `res w ⊗ res w`

Target: `SmoothTensorRep` (`Sub/PartI_T02_1_4_4_1_5_1_1.lean`), source lines 3594-3625.

For `u` a smooth cylinder representative of `w ∈ H^5`, the tensor `u ⊗ u` (as a `TensorVal`
through `tensorToPlaneCLE`) is smooth and periodic, and `tensorH3Bilinear` of two copies of
`res₃ w` is its `ofCylSmooth` class.
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

/-- The plane row tensor of a smooth periodic field is smooth. -/
private theorem contDiff_prt {w : Plane → Cyl.Vec2} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (planeRowTensorValue w w) := by
  have h0 : ContDiff ℝ ∞ (fun x => w x 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).contDiff.comp hw
  have h1 : ContDiff ℝ ∞ (fun x => w x 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).contDiff.comp hw
  have hp : ContDiff ℝ ∞ (fun x => planeOfVec (w x)) := h0.prodMk h1
  exact (h0.smul hp).prodMk (h1.smul hp)

theorem smoothTensorRep : SmoothTensorRep := by
  intro c hc hc1 w u hus hwu
  have hwu' : hVal w =ᵐ[Cyl.cellμ c] u := by
    rwa [Cyl.cylinder_μ_eq] at hwu
  have hP : Sob.IsCylSmooth c (planeRowTensorValue u u) := by
    refine ⟨contDiff_prt hus.smooth, fun z => ?_, ?_⟩
    · simp only [planeRowTensorValue, hus.periodic z]
    · obtain ⟨R, hR⟩ := hus.bounded
      exact ⟨R, fun z hz => by simp [planeRowTensorValue, hR z hz, planeOfVec]⟩
  let T : Plane → TensorVal := fun z => tensorToPlaneCLE.symm (planeRowTensorValue u u z)
  have hT : Sob.IsCylSmooth c T :=
    HeatCylinder.isCylSmooth_postcomp_clm hP tensorToPlaneCLE.symm.toContinuousLinearMap
  refine ⟨T, hT, ?_, ?_⟩
  · apply Sob.W.value_injective
    apply MeasureTheory.Lp.ext
    have hA := tensorH3Bilinear_value_ae hc1
      (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)
      (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)
    have hB := Sob.W.value_ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := TensorVal) (k := 3) (p := 2) hc T hT
    have hxu : ∀ᵐ z ∂(Cyl.cellμ c),
        (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 3 2
          (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) : Plane → Cyl.Vec2) z
          = u z :=
      hwu'
    have hcell : (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
          (tensorH3Bilinear hc1
            (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)
            (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)) : Plane → TensorVal)
        =ᵐ[Cyl.cellμ c]
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2
          (Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := TensorVal) (k := 3)
            (p := 2) hc T hT) : Plane → TensorVal) := by
      filter_upwards [hA, hB.filter_mono (ae_cell_le c), hxu] with z h1 h2 h3
      rw [h1, h2]
      apply tensorToPlaneCLE.injective
      simp only [T, tensorToPlaneCLE_rowTensorValue, ContinuousLinearEquiv.apply_symm_apply,
        planeRowTensorValue, h3]
    exact hcell.filter_mono (ae_wμ_le c)
  · intro z
    simp [T]
end UnforcedLeray.Short.PartI
