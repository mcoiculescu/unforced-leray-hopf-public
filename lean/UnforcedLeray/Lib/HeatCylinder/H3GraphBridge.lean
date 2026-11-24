import UnforcedLeray.Lib.HeatCylinder.H3Density
import UnforcedLeray.Lib.HeatCylinder.TensorEnergy

/-!
# Exact graph norm for smooth row-tensor representatives

The derivative-energy distance used by the concrete heat estimate is exactly the `W` graph norm
of a smooth TensorVal difference. This is the bridge from a genuine TensorH3 Cauchy sequence to
the heat estimate's concrete input metric.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.TrainB (TensorVal)

/-- For smooth periodic compact-axial TensorVal inputs, the centered-cell derivative-energy
distance is the exact norm of their `W.ofCylSmooth` difference. -/
theorem cylinderDerivativeEnergyDistance_eq_norm_ofCylSmooth {c : ℝ} (hc : 0 < c)
    {T U : Plane → TensorVal} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U) :
    cylinderDerivativeEnergyDistance c T U =
      ‖UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := TensorVal) (k := 3) (p := 2) hc (fun z => T z - U z)
        (UnforcedLeray.HeatCylinder.isCylSmooth_sub hT hU)‖ := by
  let hsub : UnforcedLeray.Sob.IsCylSmooth c (fun z => T z - U z) :=
    UnforcedLeray.HeatCylinder.isCylSmooth_sub hT hU
  let x := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := TensorVal) (k := 3) (p := 2) hc (fun z => T z - U z) hsub
  have hμ : UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
    rw [UnforcedLeray.Cyl.wμ_ρwW]
    simp [UnforcedLeray.Cyl.wμ]
  have hterm (α : UnforcedLeray.Sob.Idx 2 3) :
      ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 α x‖ =
        (eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) (fun z => T z - U z)) 2
          (UnforcedLeray.Cyl.cellμ c)).toReal := by
    calc
      _ = (eLpNorm (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 α x) 2
          (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)))).toReal := by rw [Lp.norm_def]
      _ = (eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) (fun z => T z - U z)) 2
          (UnforcedLeray.Cyl.cellμ c)).toReal := by
        rw [eLpNorm_congr_ae
          (UnforcedLeray.Sob.W.deriv_ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
            (F := TensorVal) (k := 3) (p := 2) hc
            (fun z => T z - U z) hsub α), hμ]
  have hnormSq : ‖x‖ ^ 2 =
      ∑ α : UnforcedLeray.Sob.Idx 2 3,
        (eLpNorm (UnforcedLeray.Sob.iterD
          ((UnforcedLeray.Sob.cylinder c).word α) (fun z => T z - U z)) 2
          (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2 := by
    rw [UnforcedLeray.Sob.W.norm_sq]
    apply Finset.sum_congr rfl
    intro α hα
    rw [hterm α]
  have hE_nonneg : 0 ≤ ∑ α : UnforcedLeray.Sob.Idx 2 3,
      (eLpNorm (UnforcedLeray.Sob.iterD
        ((UnforcedLeray.Sob.cylinder c).word α) (fun z => T z - U z)) 2
        (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2 :=
    Finset.sum_nonneg fun α hα => sq_nonneg _
  have hroot : Real.sqrt (∑ α : UnforcedLeray.Sob.Idx 2 3,
      (eLpNorm (UnforcedLeray.Sob.iterD
        ((UnforcedLeray.Sob.cylinder c).word α) (fun z => T z - U z)) 2
        (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2) = Real.sqrt (‖x‖ ^ 2) :=
    (Real.sqrt_inj hE_nonneg (sq_nonneg _)).2 hnormSq.symm
  have hrootNorm : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
  have hdistNorm : cylinderDerivativeEnergyDistance c T U = ‖x‖ := by
    dsimp [cylinderDerivativeEnergyDistance]
    rw [hroot, hrootNorm]
    exact Submodule.norm_coe x
  simpa [x, hsub] using hdistNorm


/-- The smooth Sobolev construction is linear with respect to subtraction of its actual fields. -/
theorem ofCylSmooth_tensor_sub_eq {c : ℝ} (hc : 0 < c)
    {T U : Plane → TensorVal} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U) :
    UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := TensorVal) (k := 3) (p := 2) hc (fun z => T z - U z)
      (UnforcedLeray.HeatCylinder.isCylSmooth_sub hT hU) =
    UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := TensorVal) (k := 3) (p := 2) hc T hT -
    UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := TensorVal) (k := 3) (p := 2) hc U hU := by
  let X := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := TensorVal) (k := 3) (p := 2) hc T hT
  let Y := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := TensorVal) (k := 3) (p := 2) hc U hU
  have hmap := map_sub (UnforcedLeray.Sob.W.value
      (UnforcedLeray.Sob.cylinder c) (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))
      ℝ TensorVal 3 2) X Y
  apply UnforcedLeray.Sob.W.value_injective
  apply Lp.ext
  filter_upwards [
    UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := TensorVal) (k := 3) (p := 2) hc (fun z => T z - U z)
      (UnforcedLeray.HeatCylinder.isCylSmooth_sub hT hU),
    UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := TensorVal) (k := 3) (p := 2) hc T hT,
    UnforcedLeray.Sob.W.value_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := TensorVal) (k := 3) (p := 2) hc U hU,
    Lp.coeFn_sub
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 X)
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 3 2 Y)] with z hDiff hTval hUval hsub
  have hmapz := congrArg (fun f : Lp TensorVal 2
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => (f : Plane → TensorVal) z) hmap
  simp only [Pi.sub_apply] at hsub
  rw [hmapz, hDiff, hsub, hTval, hUval]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.cylinderDerivativeEnergyDistance_eq_norm_ofCylSmooth
#print axioms UnforcedLeray.HeatCylinder.ofCylSmooth_tensor_sub_eq
