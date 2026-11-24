import UnforcedLeray.Lib.HeatCylinder.HeatL2NormalizedVecBridge

/-!
# Linear continuous normalized-to-centered vector `L²` transport

The periodic extension induces a genuine quotient map. Its norm is exactly the square-root cell
factor already recorded in the bridge leaf.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)
open UnforcedLeray.Cyl (cellμ)

private theorem normalizedVecPeriodicRep_add_ae {c : ℝ} (hc : 0 < c)
    (x y : Lp Vec 2 (cellMeasure c)) :
    normalizedVecPeriodicRep hc (x + y) =ᵐ[volume]
      fun z => normalizedVecPeriodicRep hc x z + normalizedVecPeriodicRep hc y z := by
  have hbase : normalizedVecRep (x + y) =ᵐ[cellMeasure c]
      fun z => normalizedVecRep x z + normalizedVecRep y z := by
    filter_upwards [normalizedVecRep_ae (x + y), normalizedVecRep_ae x,
      normalizedVecRep_ae y, Lp.coeFn_add x y] with z hxy hx hy hadd
    calc
      normalizedVecRep (x + y) z = (x + y : Lp Vec 2 (cellMeasure c)) z := hxy
      _ = x z + y z := hadd
      _ = normalizedVecRep x z + normalizedVecRep y z := by rw [← hx, ← hy]
  have hper := perLift_congr_ae hc hbase
  filter_upwards [hper] with z hz
  calc
    normalizedVecPeriodicRep hc (x + y) z = perLift hc (normalizedVecRep (x + y)) z := rfl
    _ = perLift hc (fun w => normalizedVecRep x w + normalizedVecRep y w) z := hz
    _ = normalizedVecPeriodicRep hc x z + normalizedVecPeriodicRep hc y z := rfl

private theorem normalizedVecPeriodicRep_smul_ae {c : ℝ} (hc : 0 < c)
    (r : ℝ) (x : Lp Vec 2 (cellMeasure c)) :
    normalizedVecPeriodicRep hc (r • x) =ᵐ[volume]
      fun z => r • normalizedVecPeriodicRep hc x z := by
  have hbase : normalizedVecRep (r • x) =ᵐ[cellMeasure c]
      fun z => r • normalizedVecRep x z := by
    filter_upwards [normalizedVecRep_ae (r • x), normalizedVecRep_ae x,
      Lp.coeFn_smul r x] with z hxr hx hsmul
    calc
      normalizedVecRep (r • x) z = (r • x : Lp Vec 2 (cellMeasure c)) z := hxr
      _ = r • x z := hsmul
      _ = r • normalizedVecRep x z := by rw [← hx]
  have hper := perLift_congr_ae hc hbase
  filter_upwards [hper] with z hz
  calc
    normalizedVecPeriodicRep hc (r • x) z = perLift hc (normalizedVecRep (r • x)) z := rfl
    _ = perLift hc (fun w => r • normalizedVecRep x w) z := hz
    _ = r • normalizedVecPeriodicRep hc x z := rfl

/-- The linear map from normalized-cell vector data to the actual centered-cell quotient. -/
noncomputable def normalizedVecToCenteredLinear {c : ℝ} (hc : 0 < c) :
    Lp Vec 2 (cellMeasure c) →ₗ[ℝ] UnforcedLeray.Cyl.L2v c where
  toFun := centeredVecOfNormalizedVec hc
  map_add' x y := by
    apply Lp.ext
    have hrep : normalizedVecPeriodicRep hc (x + y) =ᵐ[cellμ c]
        fun z => normalizedVecPeriodicRep hc x z + normalizedVecPeriodicRep hc y z := by
      change perLift hc (normalizedVecRep (x + y)) =ᵐ[
        volume.restrict (UnforcedLeray.Cyl.cell c)]
        fun z => perLift hc (normalizedVecRep x) z + perLift hc (normalizedVecRep y) z
      exact ae_restrict_of_ae (s := UnforcedLeray.Cyl.cell c)
        (normalizedVecPeriodicRep_add_ae hc x y)
    filter_upwards [centeredVecOfNormalizedVec_coe_ae hc (x + y),
      centeredVecOfNormalizedVec_coe_ae hc x, centeredVecOfNormalizedVec_coe_ae hc y,
      hrep, Lp.coeFn_add
        (centeredVecOfNormalizedVec hc x) (centeredVecOfNormalizedVec hc y)] with z hxy hx hy hrep hadd
    calc
      (centeredVecOfNormalizedVec hc (x + y) : Plane → Vec) z =
          normalizedVecPeriodicRep hc (x + y) z := hxy
      _ = normalizedVecPeriodicRep hc x z + normalizedVecPeriodicRep hc y z := hrep
      _ = ((centeredVecOfNormalizedVec hc x + centeredVecOfNormalizedVec hc y :
          UnforcedLeray.Cyl.L2v c) : Plane → Vec) z := by
        rw [← hx, ← hy]
        exact hadd.symm
  map_smul' r x := by
    apply Lp.ext
    have hrep : normalizedVecPeriodicRep hc (r • x) =ᵐ[cellμ c]
        fun z => r • normalizedVecPeriodicRep hc x z := by
      change perLift hc (normalizedVecRep (r • x)) =ᵐ[
        volume.restrict (UnforcedLeray.Cyl.cell c)]
        fun z => r • perLift hc (normalizedVecRep x) z
      exact ae_restrict_of_ae (s := UnforcedLeray.Cyl.cell c)
        (normalizedVecPeriodicRep_smul_ae hc r x)
    filter_upwards [centeredVecOfNormalizedVec_coe_ae hc (r • x),
      centeredVecOfNormalizedVec_coe_ae hc x,
      hrep,
      Lp.coeFn_smul r (centeredVecOfNormalizedVec hc x)] with z hsm hx hrep hcoe
    calc
      (centeredVecOfNormalizedVec hc (r • x) : Plane → Vec) z =
          normalizedVecPeriodicRep hc (r • x) z := hsm
      _ = r • normalizedVecPeriodicRep hc x z := hrep
      _ = (r • centeredVecOfNormalizedVec hc x : UnforcedLeray.Cyl.L2v c) z := by
        calc
          r • normalizedVecPeriodicRep hc x z = r • (centeredVecOfNormalizedVec hc x : Plane → Vec) z := by
            rw [hx]
          _ = (r • centeredVecOfNormalizedVec hc x : UnforcedLeray.Cyl.L2v c) z := hcoe.symm

/-- Continuous linear normalized-cell to centered-cell vector `L²` transport. -/
noncomputable def normalizedVecToCenteredCLM {c : ℝ} (hc : 0 < c) :
    Lp Vec 2 (cellMeasure c) →L[ℝ] UnforcedLeray.Cyl.L2v c :=
  (normalizedVecToCenteredLinear hc).mkContinuous (Real.sqrt c)
    (by intro x
        change ‖centeredVecOfNormalizedVec hc x‖ ≤ Real.sqrt c * ‖x‖
        have hsq := norm_sq_centeredVecOfNormalizedVec hc x
        have hsqrt : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
        have heqSq : ‖centeredVecOfNormalizedVec hc x‖ ^ 2 =
            (Real.sqrt c * ‖x‖) ^ 2 := by nlinarith [hsqrt]
        rcases (sq_eq_sq_iff_eq_or_eq_neg.mp heqSq) with heq | heq
        · rw [heq]
        · have hp := mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg x)
          nlinarith [norm_nonneg (centeredVecOfNormalizedVec hc x), hp])

/-- Operator norm bound for the normalized-to-centered vector bridge. -/
theorem norm_normalizedVecToCenteredCLM_le {c : ℝ} (hc : 0 < c) :
    ‖normalizedVecToCenteredCLM hc‖ ≤ Real.sqrt c :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) (by
    intro x
    change ‖centeredVecOfNormalizedVec hc x‖ ≤ Real.sqrt c * ‖x‖
    have hsq := norm_sq_centeredVecOfNormalizedVec hc x
    have hsqrt : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
    have heqSq : ‖centeredVecOfNormalizedVec hc x‖ ^ 2 =
        (Real.sqrt c * ‖x‖) ^ 2 := by nlinarith [hsqrt]
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp heqSq) with heq | heq
    · rw [heq]
    · have hp := mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg x)
      nlinarith [norm_nonneg (centeredVecOfNormalizedVec hc x), hp])

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.normalizedVecToCenteredLinear
#print axioms UnforcedLeray.HeatCylinder.normalizedVecToCenteredCLM
#print axioms UnforcedLeray.HeatCylinder.norm_normalizedVecToCenteredCLM_le
