import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.HeatDivDeriv.Defs
import UnforcedLeray.Lib.HeatCylinder.H3SmoothDerivativeBridge

/-!
# Part I, task `PartI:T02/1/2/3/5`: leaf A2 (smooth output)

Source of record: `the November 2 reference manuscript`, lines 261-288.
`bdpHddSmoothOutput_proof : BdpHddSmoothOutput`: every normalized derivative component of the
actual smooth Gaussian output `heatDivH3` is `heatDivVecL2CLM` of the literal input derivative.
The centered derivative class is the actual field `toVec ∘ heatDiv θ (∂^α S)`
(`heatDivH3CenteredDerivativeOrbit_eq_deriv`), which is periodic, so its centered-to-normalized
transport is that field; `heatDivVecL2CLM_apply_to_periodic` gives the same field.  Same pattern
as `vectorH3DerivativeNormalizedValue_heatVecH3`.  No `sorry`, `admit`, `axiom` or
`native_decide`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane cellμ)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

theorem bdpHddSmoothOutput_proof : BdpHddSmoothOutput := by
  intro c θ hc hθ S hS α
  let vs := (Sob.cylinder c).word α
  let Sα := Sob.iterD vs S
  have hSα : Sob.IsCylSmooth c Sα := hS.iterD vs
  have hper : UnforcedLeray.B0284.IsQPeriodic c Sα := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hSα.periodic z
  have hmeas : Measurable Sα := hSα.smooth.continuous.measurable
  have hmem : MemLp Sα 2 (UnforcedLeray.B0284.cellMeasure c) :=
    memLp_tensor_iterD_cylSmooth_normalized hc hS vs
  let F : Plane → Vec := heatDivH3Field (c := c) (θ := θ) S α
  let x := heatDivH3 hc hθ hS
  let d := centeredVecH3DerivativeClass α x
  have hcenter : (heatDivH3CenteredDerivativeOrbit hc hS α θ : Plane → Vec) =ᵐ[cellμ c] F := by
    rw [heatDivH3CenteredDerivativeOrbit, dif_pos hθ]
    simpa only [heatVecH3_measure_eq_cell_deriv c] using
      (memLp_heatDivH3Field hc hθ hS α).coeFn_toLp
  have hderiv : (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x :
      Plane → Vec) =ᵐ[cellμ c] F := by
    rw [← heatDivH3CenteredDerivativeOrbit_eq_deriv hc hθ hS α]
    exact hcenter
  have hclass := centeredVecH3DerivativeClass_coe_ae α x
  have hbase : centeredVecL2Rep d =ᵐ[cellμ c] F := by
    filter_upwards [centeredVecL2Rep_ae d, hclass, hderiv] with z hr hd hF
    exact hr.trans (hd.trans hF)
  have hperiodic : Cyl.IsPeriodic c F := by
    intro z
    exact congrArg Train.toVec (UnforcedLeray.B0296.heatDiv_periodic (θ := θ) hper z)
  have hlift := centeredPerLift_congr_ae hc hbase
  have hself := centeredPerLift_eq_self_of_periodic hc hperiodic
  have hglobal : centeredVecL2PeriodicRep hc d =ᵐ[volume] F := by
    filter_upwards [hlift] with z hz
    exact hz.trans (congrFun hself z)
  have hleft : centeredVecL2PeriodicRep hc d =ᵐ[UnforcedLeray.B0284.cellMeasure c] F := by
    apply ae_iff.mpr
    exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hglobal)
  have hright : (heatDivVecL2CLM hc hθ (hmem.toLp Sα) : Plane → Vec) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] F := by
    rw [heatDivVecL2CLM_apply_to_periodic hc hθ hper hmeas.aestronglyMeasurable hmem]
    exact (periodicHeatDivVecMemLp hc hθ Sα hper hmeas.aestronglyMeasurable hmem).coeFn_toLp
  change centeredVecToNormalizedCLM hc d = heatDivVecL2CLM hc hθ (hmem.toLp Sα)
  apply Lp.ext
  filter_upwards [(memLp_centeredVecL2PeriodicRep_normalized hc d).coeFn_toLp,
    hleft, hright] with z hmap hleft' hright'
  exact hmap.trans (hleft'.trans hright'.symm)

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.bdpHddSmoothOutput_proof
