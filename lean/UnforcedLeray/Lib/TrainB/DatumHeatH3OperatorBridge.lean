import UnforcedLeray.Lib.TrainB.DatumHeatH3
import UnforcedLeray.Lib.TrainB.InitialDatumH3Class
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator
import UnforcedLeray.Lib.HeatCylinder.HeatVecActualContraction
import UnforcedLeray.Lib.HeatCylinder.HeatVecTranslationNorm

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem datumNormalizedMemLp {c : ℝ} (hc : 0 < c) :
    MemLp (Train.datum c) 2 (B0284.cellMeasure c) := by
  have hmemCell : MemLp (Train.datum c) 2 (Cyl.cellμ c) := by
    simpa only [Sob.TestDomain.word_zero, Sob.iterD_nil] using
      memLp_datum_word_derivative hc Sob.Idx.zero
  have hper : B0284.IsQPeriodic c (Train.datum c) := by
    simpa only [B0284.IsQPeriodic, Cyl.IsPeriodic] using Train.datum_periodic c
  exact HeatCylinder.memLp_cellMeasure_of_memLp_cyl hc
    (Train.datum_contDiff hc.ne').continuous.measurable hper hmemCell

/-- The actual initial H³ datum, sent to the normalized-cell value quotient, is the actual
normalized-cell L² class of `Train.datum`. -/
theorem vectorH3NormalizedValue_datumVecH3 {c : ℝ} (hc : 0 < c) :
    HeatCylinder.vectorH3NormalizedValue hc (datumVecH3 hc) =
      (datumNormalizedMemLp hc).toLp (Train.datum c) := by
  have hcenter : HeatCylinder.vectorH3PeriodicValueRep hc (datumVecH3 hc) =ᵐ[
      Cyl.cellμ c] Train.datum c := by
    filter_upwards [HeatCylinder.vectorH3PeriodicValueRep_ae_value hc (datumVecH3 hc),
      datumVecH3_value_ae hc] with z hrep hvalue
    exact hrep.trans hvalue
  have hglobal := HeatCylinder.ae_eq_of_ae_centered_periodic hc
    (HeatCylinder.periodic_vectorH3PeriodicValueRep hc (datumVecH3 hc))
    (by simpa only [B0284.IsQPeriodic, Cyl.IsPeriodic] using Train.datum_periodic c)
    hcenter
  apply Lp.ext
  filter_upwards [HeatCylinder.vectorH3NormalizedValue_coe_ae hc (datumVecH3 hc),
    hglobal, (datumNormalizedMemLp hc).coeFn_toLp] with z hleft hperiodic hright
  exact hleft.trans (hperiodic.trans hright.symm)

private theorem heatVecConvolution_congr_ae {θ : ℝ} {f g : Plane → Vec}
    (hfg : f =ᵐ[volume] g) :
    HeatCylinder.heatVecConvolution θ f = HeatCylinder.heatVecConvolution θ g := by
  funext z
  unfold HeatCylinder.heatVecConvolution
  have hmap : MeasurePreserving (fun w : Plane => -w + z) volume volume :=
    (measurePreserving_add_right volume z).comp (Measure.measurePreserving_neg volume)
  have hshift : (fun w : Plane => f (z - w)) =ᵐ[volume]
      fun w => g (z - w) := by
    have h := hmap.quasiMeasurePreserving.ae hfg
    filter_upwards [h] with w hw
    simpa only [sub_eq_add_neg, add_comm] using hw
  apply integral_congr_ae
  filter_upwards [hshift] with w hw
  simp [hw]

/-- The W.ofFields heat class built directly from the literal Gaussian convolution is the same
H³ class as the completed actual Gaussian heat operator on the actual Train datum. -/
theorem datumHeatVecH3_eq_actualHeatVecH3 {c θ : ℝ} (hc2 : 2 ≤ c) (hθ : 0 < θ) :
    datumHeatVecH3 hc2 hθ =
      HeatCylinder.actualHeatVecH3CLM (by linarith : 0 < c) hθ
        (datumVecH3 (by linarith : 0 < c)) := by
  let hc : 0 < c := by linarith
  let x : Lp Vec 2 (B0284.cellMeasure c) :=
    HeatCylinder.vectorH3NormalizedValue hc (datumVecH3 hc)
  have hinput : x = (datumNormalizedMemLp hc).toLp (Train.datum c) :=
    vectorH3NormalizedValue_datumVecH3 hc
  have hrepCell : HeatCylinder.normalizedVecHeatRep hc x =ᵐ[
      B0284.cellMeasure c] Train.datum c := by
    rw [hinput]
    exact (HeatCylinder.normalizedVecHeatRep_ae hc
      ((datumNormalizedMemLp hc).toLp (Train.datum c))).trans
      (datumNormalizedMemLp hc).coeFn_toLp
  have hperDatum : B0284.IsQPeriodic c (Train.datum c) := by
    simpa only [B0284.IsQPeriodic, Cyl.IsPeriodic] using Train.datum_periodic c
  have hrepVolume : HeatCylinder.normalizedVecHeatRep hc x =ᵐ[volume] Train.datum c := by
    have hlift := HeatCylinder.perLift_congr_ae hc hrepCell
    have hleft := HeatCylinder.perLift_eq_self_of_periodic hc
      (HeatCylinder.normalizedVecHeatRep_periodic hc x)
    have hright := HeatCylinder.perLift_eq_self_of_periodic hc hperDatum
    filter_upwards [hlift] with z hz
    rw [congrFun hleft z, congrFun hright z] at hz
    exact hz
  have hconvDatum := heatVecConvolution_congr_ae (θ := θ) hrepVolume
  have hplaneRep := HeatCylinder.normalizedVecHeatRep_eq_normalizedPlaneVecRep_ae hc x
  have hconvPlane := heatVecConvolution_congr_ae (θ := θ) hplaneRep.symm
  have hOut := HeatCylinder.heatVecL2CLM_value_ae hc hθ x
  have hOutDatum : (HeatCylinder.heatVecL2CLM hc θ x : Plane → Vec) =ᵐ[
      B0284.cellMeasure c] HeatCylinder.heatVecConvolution θ (Train.datum c) := by
    filter_upwards [hOut] with z hz
    calc
      (HeatCylinder.heatVecL2CLM hc θ x : Plane → Vec) z =
          HeatCylinder.heatVecConvolution θ
            (fun q => Train.toVec (HeatCylinder.planeRep hc
              ((Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2
                (B0284.cellMeasure c) x) q)) z := hz
      _ = HeatCylinder.heatVecConvolution θ
          (HeatCylinder.normalizedVecHeatRep hc x) z := congrFun hconvPlane z
      _ = HeatCylinder.heatVecConvolution θ (Train.datum c) z := congrFun hconvDatum z
  have hcenter : HeatCylinder.vectorH3PeriodicValueRep hc
      (datumHeatVecH3 hc2 hθ) =ᵐ[Cyl.cellμ c]
        HeatCylinder.heatVecConvolution θ (Train.datum c) := by
    filter_upwards [HeatCylinder.vectorH3PeriodicValueRep_ae_value hc
        (datumHeatVecH3 hc2 hθ), datumHeatVecH3_value_ae hc2 hθ] with z hrep hval
    exact hrep.trans hval
  have hperiodicOutput := HeatCylinder.ae_eq_of_ae_centered_periodic hc
    (HeatCylinder.periodic_vectorH3PeriodicValueRep hc (datumHeatVecH3 hc2 hθ))
    (by
      apply heatVecConvolution_periodic_of_periodic
      exact Train.datum_periodic c)
    hcenter
  apply HeatCylinder.vectorH3NormalizedValue_injective hc
  rw [HeatCylinder.actualHeatVecH3CLM_apply,
    HeatCylinder.vectorH3NormalizedValue_actualHeatVecH3 hc hθ]
  change HeatCylinder.vectorH3NormalizedValue hc (datumHeatVecH3 hc2 hθ) =
    HeatCylinder.heatVecL2CLM hc θ x
  apply Lp.ext
  filter_upwards [HeatCylinder.vectorH3NormalizedValue_coe_ae hc
      (datumHeatVecH3 hc2 hθ), hOutDatum, hperiodicOutput] with z hleft hright hglobal
  exact hleft.trans (hglobal.trans hright.symm)

#print axioms UnforcedLeray.TrainB.vectorH3NormalizedValue_datumVecH3
#print axioms UnforcedLeray.TrainB.datumHeatVecH3_eq_actualHeatVecH3

end UnforcedLeray.TrainB
