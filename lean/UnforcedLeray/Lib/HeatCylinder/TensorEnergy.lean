import UnforcedLeray.Lib.HeatCylinder.SmoothCLM
import UnforcedLeray.Lib.HeatCylinder.H3Completion
import UnforcedLeray.Lib.CylinderB.Space
import UnforcedLeray.Lib.TrainB.TensorBridge

/-!
# Derivative-energy transfer through bounded value-space maps

This generic estimate is the input-side bridge for the train tensor coordinates. It preserves the
actual centered-cell derivative energy and records the operator norm of the value map; it makes no
isometry claim about the product-plane carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Centered-cell derivative energy of a smooth cylinder field difference. -/
noncomputable def cylinderDerivativeEnergyDistance (c : ℝ) (T U : Plane → F) : ℝ :=
  Real.sqrt (∑ α : UnforcedLeray.Sob.Idx 2 3,
    (eLpNorm (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α)
      (fun z => T z - U z)) 2 (UnforcedLeray.Cyl.cellμ c)).toReal ^ 2)

/-- Every derivative word contracts in `L²` under a continuous linear value map, with the
operator norm as the exact real coefficient. -/
theorem eLpNorm_iterD_postcomp_le {μ : Measure Plane} (L : F →L[ℝ] G) {T : Plane → F}
    (hT : ContDiff ℝ ∞ T) (vs : List Plane) :
    eLpNorm (UnforcedLeray.Sob.iterD vs (fun z => L (T z))) 2 μ ≤
      ENNReal.ofReal ‖L‖ * eLpNorm (UnforcedLeray.Sob.iterD vs T) 2 μ := by
  rw [UnforcedLeray.HeatCylinder.iterD_postcomp_clm L hT vs]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun z => ?_) 2
  exact L.le_opNorm _

/-- Smooth cylinder derivative energy is contractive under a value map of operator norm at most
one. -/
theorem cylinderDerivativeEnergyDistance_postcomp_contractive {c : ℝ}
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {T U : Plane → F} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U) (L : F →L[ℝ] G)
    (hL : ‖L‖ ≤ 1) :
    cylinderDerivativeEnergyDistance c (fun z => L (T z)) (fun z => L (U z)) ≤
      cylinderDerivativeEnergyDistance c T U := by
  let hsub : UnforcedLeray.Sob.IsCylSmooth c (fun z => T z - U z) :=
    UnforcedLeray.HeatCylinder.isCylSmooth_sub hT hU
  have hfield : (fun z => L (T z) - L (U z)) = fun z => L (T z - U z) := by
    funext z
    exact (map_sub L (T z) (U z)).symm
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro α hα
  let vs := (UnforcedLeray.Sob.cylinder c).word α
  have hiter : UnforcedLeray.Sob.iterD vs (fun z => L (T z) - L (U z)) =
      fun z => L (UnforcedLeray.Sob.iterD vs (fun z => T z - U z) z) := by
    rw [hfield]
    exact UnforcedLeray.HeatCylinder.iterD_postcomp_clm L hsub.smooth vs
  have hnorm := eLpNorm_iterD_postcomp_le (μ := UnforcedLeray.Cyl.cellμ c)
    L hsub.smooth vs
  rw [UnforcedLeray.HeatCylinder.iterD_postcomp_clm L hsub.smooth vs] at hnorm
  have hnorm' : eLpNorm (UnforcedLeray.Sob.iterD vs
      (fun z => L (T z) - L (U z))) 2 (UnforcedLeray.Cyl.cellμ c) ≤
      eLpNorm (UnforcedLeray.Sob.iterD vs (fun z => T z - U z)) 2
        (UnforcedLeray.Cyl.cellμ c) := by
    rw [hiter]
    calc
      eLpNorm (fun z => L (UnforcedLeray.Sob.iterD vs (fun z => T z - U z) z)) 2
          (UnforcedLeray.Cyl.cellμ c) ≤
        ENNReal.ofReal ‖L‖ * eLpNorm
          (UnforcedLeray.Sob.iterD vs (fun z => T z - U z)) 2
            (UnforcedLeray.Cyl.cellμ c) := hnorm
      _ ≤ ENNReal.ofReal 1 * eLpNorm
          (UnforcedLeray.Sob.iterD vs (fun z => T z - U z)) 2
            (UnforcedLeray.Cyl.cellμ c) :=
        mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hL) (by positivity)
      _ = eLpNorm (UnforcedLeray.Sob.iterD vs (fun z => T z - U z)) 2
          (UnforcedLeray.Cyl.cellμ c) := by simp
  have hmem : MemLp (UnforcedLeray.Sob.iterD vs (fun z => T z - U z)) 2
      (UnforcedLeray.Cyl.cellμ c) := by
    have hmem' := (hsub.iterD vs).memLp (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) 2
    have hμ : UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
      rw [UnforcedLeray.Cyl.wμ_ρwW]
      simp [UnforcedLeray.Cyl.wμ]
    rw [hμ] at hmem'
    exact hmem'
  have hreal :
      (eLpNorm (UnforcedLeray.Sob.iterD vs (fun z => L (T z) - L (U z))) 2
        (UnforcedLeray.Cyl.cellμ c)).toReal ≤
      (eLpNorm (UnforcedLeray.Sob.iterD vs (fun z => T z - U z)) 2
        (UnforcedLeray.Cyl.cellμ c)).toReal :=
    ENNReal.toReal_mono hmem.eLpNorm_ne_top hnorm'
  have hnonout : 0 ≤ (eLpNorm (UnforcedLeray.Sob.iterD vs
      (fun z => L (T z) - L (U z))) 2 (UnforcedLeray.Cyl.cellμ c)).toReal :=
    ENNReal.toReal_nonneg
  have hnonin : 0 ≤ (eLpNorm (UnforcedLeray.Sob.iterD vs
      (fun z => T z - U z)) 2 (UnforcedLeray.Cyl.cellμ c)).toReal :=
    ENNReal.toReal_nonneg
  exact (sq_le_sq₀ hnonout hnonin).2 hreal


/-- The actual Train tensor coordinate equivalence is contractive into the kernel's
`Plane × Plane` carrier, so it decreases the full centered-cell derivative energy. -/
theorem heatTensorH3Distance_tensorToPlane_le {c : ℝ}
    {T U : Plane → UnforcedLeray.TrainB.TensorVal}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hU : UnforcedLeray.Sob.IsCylSmooth c U) :
    UnforcedLeray.HeatCylinder.heatTensorH3Distance c
      (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (T z))
      (fun z => UnforcedLeray.TrainB.tensorToPlaneCLE (U z)) ≤
    cylinderDerivativeEnergyDistance c T U := by
  let L : UnforcedLeray.TrainB.TensorVal →L[ℝ] (Plane × Plane) :=
    UnforcedLeray.TrainB.tensorToPlaneCLE.toContinuousLinearMap
  have hL : ‖L‖ ≤ 1 := by
    simpa [L] using UnforcedLeray.TrainB.norm_tensorToPlaneCLE_le_one
  change cylinderDerivativeEnergyDistance c (fun z => L (T z)) (fun z => L (U z)) ≤
    cylinderDerivativeEnergyDistance c T U
  exact cylinderDerivativeEnergyDistance_postcomp_contractive hT hU L hL

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.eLpNorm_iterD_postcomp_le
#print axioms UnforcedLeray.HeatCylinder.cylinderDerivativeEnergyDistance_postcomp_contractive
#print axioms UnforcedLeray.HeatCylinder.heatTensorH3Distance_tensorToPlane_le
