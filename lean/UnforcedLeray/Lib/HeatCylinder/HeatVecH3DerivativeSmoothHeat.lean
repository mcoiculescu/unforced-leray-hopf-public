import UnforcedLeray.Lib.HeatCylinder.HeatVecH3DerivativeComponents
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeComponents
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator

/-!
# Smooth heat compatibility for every H³ derivative

The normalized weak derivative of the actual smooth Gaussian H³ output is the actual normalized
L² Gaussian heat of the matching input derivative.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.Cyl (cellμ)

/-- The all-word derivative component of the actual smooth H³ heat output agrees with literal
normalized-cell Gaussian heat of the corresponding actual input derivative. -/
theorem vectorH3DerivativeNormalizedValue_heatVecH3 {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    vectorH3DerivativeNormalizedValue hc α (heatVecH3 hc hθ hT) =
      heatVecL2CLM hc θ
        ((memLp_iterD_vec_cylSmooth_normalized hc hT
          ((UnforcedLeray.Sob.cylinder c).word α)).toLp
          (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T)) := by
  let vs := (UnforcedLeray.Sob.cylinder c).word α
  let Tα := UnforcedLeray.Sob.iterD vs T
  let F : Plane → Vec := heatVecH3Field (c := c) (θ := θ) T α
  let x := heatVecH3 hc hθ hT
  let d := centeredVecH3DerivativeClass α x
  let hm := memLp_iterD_vec_cylSmooth_normalized hc hT vs
  have hderiv := deriv_heatVecH3_ae_cell hc hθ hT α
  have hclass := centeredVecH3DerivativeClass_coe_ae α x
  have hbase : centeredVecL2Rep d =ᵐ[cellμ c] F := by
    filter_upwards [centeredVecL2Rep_ae d, hclass, hderiv] with z hr hd hF
    exact hr.trans (hd.trans hF)
  have hperiodic : UnforcedLeray.Cyl.IsPeriodic c F := by
    intro z
    change heatVecConvolution θ Tα (z.1 + c, z.2) = heatVecConvolution θ Tα z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    simpa only [hcoord] using (heatVecConvolution_periodic hc hθ (hT.iterD vs)) z
  have hlift := centeredPerLift_congr_ae hc hbase
  have hself := centeredPerLift_eq_self_of_periodic hc hperiodic
  have hglobal : centeredVecL2PeriodicRep hc d =ᵐ[volume] F := by
    filter_upwards [hlift] with z hz
    exact hz.trans (congrFun hself z)
  have hleft : centeredVecL2PeriodicRep hc d =ᵐ[cellMeasure c]
      heatVecConvolution θ Tα := by
    have hF : F = heatVecConvolution θ Tα := by rfl
    apply ae_iff.mpr
    exact (UnforcedLeray.B0284.cellMeasure_ac c)
      (ae_iff.mp (hglobal.trans (Filter.Eventually.of_forall fun z => congrFun hF z)))
  have hright : (heatVecL2CLM hc θ (hm.toLp Tα) : Plane → Vec) =ᵐ[cellMeasure c]
      heatVecConvolution θ Tα := by
    simpa only [hm, Tα, vs] using
      heatVecL2CLM_value_ae_iterD_cylSmooth hc hθ hT
        ((UnforcedLeray.Sob.cylinder c).word α)
  change centeredVecToNormalizedCLM hc d = heatVecL2CLM hc θ (hm.toLp Tα)
  apply Lp.ext
  filter_upwards [
    (memLp_centeredVecL2PeriodicRep_normalized hc d).coeFn_toLp,
    hleft, hright] with z hmap hleft' hright'
  exact hmap.trans (hleft'.trans hright'.symm)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.vectorH3DerivativeNormalizedValue_heatVecH3
