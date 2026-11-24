import UnforcedLeray.Lib.HeatCylinder.HeatVecH3DerivativeTransport
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeComponents

/-!
# Actual normalized representatives of H³ derivative components

The centered weak derivative is transported to the normalized B0284 cell through its actual
periodic representative. Smooth representatives identify this quotient class with the literal
Gaussian L² class of the corresponding input derivative.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)
open UnforcedLeray.Cyl (cellμ)

private noncomputable def cylinderDerivativeToCellCLM {c : ℝ} :
    Lp Vec 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) →L[ℝ] Lp Vec 2 (cellμ c) := by
  have hμ := heatVecH3_measure_eq_cell_deriv c
  have hle : cellμ c ≤ (1 : ℝ≥0∞) •
      UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) := by
    rw [← hμ]
    simp
  exact Lp.LpToLpOfMeasureLeSMul (μ := cellμ c)
    (ν := UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) (c := 1) (by simp) hle

noncomputable def centeredVecH3DerivativeClass {c : ℝ}
    (α : UnforcedLeray.Sob.Idx 2 3) :
    UnforcedLeray.Cyl.H ℝ Vec c 0 3 →L[ℝ] Lp Vec 2 (cellμ c) :=
  (cylinderDerivativeToCellCLM (c := c)).comp
    (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α)

/-- The normalized derivative component of an arbitrary centered H³ class. -/
noncomputable def vectorH3DerivativeNormalizedValue {c : ℝ} (hc : 0 < c)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    UnforcedLeray.Cyl.H ℝ Vec c 0 3 →L[ℝ] Lp Vec 2 (cellMeasure c) :=
  (centeredVecToNormalizedCLM hc).comp (centeredVecH3DerivativeClass α)

theorem centeredVecH3DerivativeClass_coe_ae {c : ℝ}
    (α : UnforcedLeray.Sob.Idx 2 3)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    centeredVecH3DerivativeClass α x =ᵐ[cellμ c]
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x : Plane → Vec) := by
  change Lp.LpToLpOfMeasureLeSMul (μ := cellμ c) (c := 1)
      (by simp) (by rw [← heatVecH3_measure_eq_cell_deriv c]; simp)
      ((UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α) x) =ᵐ[cellμ c] _
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (μ := cellμ c) (c := 1)
    (by simp) (by rw [← heatVecH3_measure_eq_cell_deriv c]; simp)
    ((UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α) x)

/-- On smooth data, the normalized weak derivative is its actual input-derivative L² class. -/
theorem vectorH3DerivativeNormalizedValue_ofCylSmooth {c : ℝ} (hc : 0 < c)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    vectorH3DerivativeNormalizedValue hc α
      (UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc T hT) =
      (memLp_iterD_vec_cylSmooth_normalized hc hT
        ((UnforcedLeray.Sob.cylinder c).word α)).toLp
        (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T) := by
  let x : UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
    UnforcedLeray.Sob.W.ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
      (F := Vec) (k := 3) (p := 2) hc T hT
  let d := centeredVecH3DerivativeClass α x
  let Tα := UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T
  let hm := memLp_iterD_vec_cylSmooth_normalized hc hT
    ((UnforcedLeray.Sob.cylinder c).word α)
  have hderiv := deriv_ofCylSmooth_ae_cell hc hT α
  have hclass := centeredVecH3DerivativeClass_coe_ae α x
  have hbase : centeredVecL2Rep d =ᵐ[cellμ c] Tα := by
    filter_upwards [centeredVecL2Rep_ae d, hclass, hderiv] with z hr hd ht
    exact hr.trans (hd.trans ht)
  have hperT : UnforcedLeray.B0284.IsQPeriodic c Tα := by
    intro q
    have hcoord : (q.1 + c, q.2) = q + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact (hT.iterD ((UnforcedLeray.Sob.cylinder c).word α)).periodic q
  have hleft := centeredPerLift_congr_ae hc hbase
  have hleftSelf := centeredPerLift_eq_self_of_periodic hc hperT
  have hDvol : centeredVecL2PeriodicRep hc d =ᵐ[volume] Tα := by
    filter_upwards [hleft] with z hz
    exact hz.trans (congrFun hleftSelf z)
  have hcellT : centeredVecL2PeriodicRep hc d =ᵐ[cellMeasure c] Tα := by
    apply ae_iff.mpr
    exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hDvol)
  change centeredVecToNormalizedLinear hc d = hm.toLp Tα
  change (memLp_centeredVecL2PeriodicRep_normalized hc d).toLp
      (centeredVecL2PeriodicRep hc d) = hm.toLp Tα
  exact MemLp.toLp_congr
    (memLp_centeredVecL2PeriodicRep_normalized hc d) hm hcellT

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.vectorH3DerivativeNormalizedValue_ofCylSmooth
