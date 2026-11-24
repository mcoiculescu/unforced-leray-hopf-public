import UnforcedLeray.Lib.HeatCylinder.HeatVecTranslationBridge
import UnforcedLeray.Lib.HeatCylinder.CellBridge

/-!
# Normalized-cell norm of translated vector increments

The normalized and centered representatives are related by the actual periodic lift. This leaf
transfers strong translation continuity from Train's centered-cell vector `L²` to the normalized
cell used by the Gaussian convolution.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.Cyl (cellμ)

theorem normalizedVecHeatRep_eq_normalizedPlaneVecRep_ae {c : ℝ}
    (hc : 0 < c) (x : Lp Vec 2 (cellMeasure c)) :
    normalizedVecHeatRep hc x =ᵐ[volume]
      normalizedPlaneVecRep hc
        ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
          2 (cellMeasure c) x) := by
  let xP : Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c) x
  have hcell :
      AEStronglyMeasurable.mk (x : Plane → Vec) (Lp.aestronglyMeasurable x) =ᵐ[cellMeasure c]
        normalizedPlaneVecRep hc xP := by
    have hmkx :
        AEStronglyMeasurable.mk (x : Plane → Vec) (Lp.aestronglyMeasurable x) =ᵐ[cellMeasure c]
          (x : Plane → Vec) := (Lp.aestronglyMeasurable x).ae_eq_mk.symm
    have hsymm := ContinuousLinearMap.coeFn_compLpL
      (L := (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane))
      (p := (2 : ℝ≥0∞)) (μ := cellMeasure c) x
    have hplane := (planeRep_spec hc xP).2.2
    filter_upwards [hmkx, hsymm, hplane] with z h1 h2 h3
    change (AEStronglyMeasurable.mk (x : Plane → Vec)
      (Lp.aestronglyMeasurable x)) z = normalizedPlaneVecRep hc xP z
    calc
      _ = x z := h1
      _ = UnforcedLeray.Train.toVec (UnforcedLeray.Train.toVecL.symm (x z)) :=
        (UnforcedLeray.Train.toVecL.apply_symm_apply (x z)).symm
      _ = UnforcedLeray.Train.toVec (xP z) := congrArg UnforcedLeray.Train.toVec h2.symm
      _ = UnforcedLeray.Train.toVec (planeRep hc xP z) :=
        congrArg UnforcedLeray.Train.toVec h3.symm
      _ = normalizedPlaneVecRep hc xP z := rfl
  have hperLift := perLift_congr_ae hc hcell
  exact hperLift.trans (ae_of_all _ fun z =>
    congrFun (perLift_eq_self_of_periodic hc (normalizedPlaneVecRep_periodic hc xP)) z)

private theorem ae_heatVecTranslationIncrement_centered {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) :
    (fun z => normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z) =ᵐ[cellμ c]
      (fun z =>
        ((planeShiftL2 hc w (centeredVecOfNormalizedPlane hc
          ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
            2 (cellMeasure c) x)) : Plane → Vec) z) -
        ((centeredVecOfNormalizedPlane hc
          ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
            2 (cellMeasure c) x) : Plane → Vec) z)) := by
  let xP : Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c) x
  let xC := centeredVecOfNormalizedPlane hc xP
  have hshift := planeShiftL2_centeredVecOfNormalizedPlane_ae hc x w
  have hrep := normalizedVecHeatRep_eq_normalizedPlaneVecRep_ae hc x
  have hbase := centeredVecOfNormalizedPlane_coe_ae hc xP
  have hrep0 := ae_restrict_of_ae (s := UnforcedLeray.Cyl.cell c) hrep
  have hshiftRep : (fun z => normalizedVecHeatRep hc x (z - w)) =ᵐ[cellμ c]
      fun z => normalizedPlaneVecRep hc xP (z - w) := by
    have htranslated := (measurePreserving_add_right volume (-w)).quasiMeasurePreserving.ae hrep
    filter_upwards [ae_restrict_of_ae (s := UnforcedLeray.Cyl.cell c) htranslated] with z hz
    simpa [sub_eq_add_neg] using hz
  filter_upwards [hshift, hshiftRep, hbase, hrep0] with z hs hr hb h0
  calc
    normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z =
        normalizedPlaneVecRep hc xP (z - w) - normalizedPlaneVecRep hc xP z := by
      rw [hr, h0]
    _ = (planeShiftL2 hc w xC : Plane → Vec) z - (xC : Plane → Vec) z := by
      have hx : (xC : Plane → Vec) z = normalizedVecHeatRep hc x z := by
        calc
          (xC : Plane → Vec) z = normalizedPlaneVecRep hc xP z := hb
          _ = normalizedVecHeatRep hc x z := h0.symm
      calc
        _ = normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z := by
          rw [← hr, ← h0]
        _ = _ := by rw [hs, hx]
    _ = (planeShiftL2 hc w xC : Plane → Vec) z - (xC : Plane → Vec) z := rfl

private theorem memLp_heatVecTranslationIncrement_centered {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) :
    MemLp (fun z => normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z)
      2 (cellμ c) := by
  let xP : Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c) x
  let xC := centeredVecOfNormalizedPlane hc xP
  have hmemShift : MemLp (fun z => (planeShiftL2 hc w xC : Plane → Vec) z -
      (xC : Plane → Vec) z) 2 (cellμ c) :=
    (Lp.memLp (planeShiftL2 hc w xC)).sub (Lp.memLp xC)
  exact (memLp_congr_ae (ae_heatVecTranslationIncrement_centered hc x w)).mpr hmemShift

private theorem heatVecTranslationIncrement_periodic {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) :
    IsQPeriodic c
      (fun z => normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z) := by
  intro z
  have hper := normalizedVecHeatRep_periodic hc x
  have hleft : (z.1 + c, z.2) - w = (z - w) + ((c, 0) : Plane) := by
    ext <;> simp <;> ring
  calc
    normalizedVecHeatRep hc x ((z.1 + c, z.2) - w) -
        normalizedVecHeatRep hc x (z.1 + c, z.2) =
        normalizedVecHeatRep hc x ((z - w) + ((c, 0) : Plane)) -
          normalizedVecHeatRep hc x z := by rw [hleft, hper z]
    _ = normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z := by
          have h := hper (z - w)
          have h' : normalizedVecHeatRep hc x ((z - w) + ((c, 0) : Plane)) =
              normalizedVecHeatRep hc x (z - w) := by
            have harg : (z - w) + ((c, 0) : Plane) = ((z - w).1 + c, (z - w).2) := by
              ext <;> simp
            rw [harg]
            exact h
          rw [h']

theorem memLp_heatVecTranslationIncrement_normalized {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) :
    MemLp (fun z => normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z)
      2 (cellMeasure c) := by
  let d : Plane → Vec := fun z => normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z
  have hdmeas : Measurable d := by
    exact (normalizedVecHeatRep_measurable hc x).comp
      (measurable_id.sub_const w) |>.sub (normalizedVecHeatRep_measurable hc x)
  have hdper : IsQPeriodic c d := heatVecTranslationIncrement_periodic hc x w
  exact memLp_cellMeasure_of_memLp_cyl hc hdmeas hdper
    (memLp_heatVecTranslationIncrement_centered hc x w)

/-- The normalized-cell `L²` translation increment of an actual periodic representative is
controlled by the centered-cell translation increment, with the exact factor `c⁻¹` on squares. -/
theorem eLpNorm_sq_heatVecTranslationIncrement {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) :
    (ENNReal.toReal (eLpNorm
      (fun z => normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z)
      2 (cellMeasure c))) ^ 2 =
      c⁻¹ * ‖planeShiftL2 hc w
        (centeredVecOfNormalizedPlane hc
          ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
            2 (cellMeasure c) x)) -
        centeredVecOfNormalizedPlane hc
          ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
            2 (cellMeasure c) x)‖ ^ 2 := by
  let d : Plane → Vec := fun z => normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z
  let xP : Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c) x
  let xC := centeredVecOfNormalizedPlane hc xP
  have hdmeas : Measurable d := by
    exact (normalizedVecHeatRep_measurable hc x).comp
      (measurable_id.sub_const w) |>.sub (normalizedVecHeatRep_measurable hc x)
  have hdper : IsQPeriodic c d := heatVecTranslationIncrement_periodic hc x w
  have hscale := eLpNorm_sq_cellMeasure_eq_cyl hc hdmeas hdper
  have hfiniteN := (memLp_heatVecTranslationIncrement_normalized hc x w).eLpNorm_ne_top
  have hfiniteC := (memLp_heatVecTranslationIncrement_centered hc x w).eLpNorm_ne_top
  have hreal := congrArg ENNReal.toReal hscale
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (le_of_lt hc), ENNReal.toReal_pow] at hreal
  let u : Lp Vec 2 (cellμ c) := planeShiftL2 hc w xC - xC
  have hcenter : ENNReal.toReal (eLpNorm d 2 (cellμ c)) = ‖u‖ := by
    have hrep := ae_heatVecTranslationIncrement_centered hc x w
    have hsub := Lp.coeFn_sub (planeShiftL2 hc w xC) xC
    have hclass : d =ᵐ[cellμ c] (u : Plane → Vec) := by
      filter_upwards [hrep, hsub] with z hz hs
      simpa only [d, u, xC, xP, Pi.sub_apply] using hz.trans hs.symm
    calc
      _ = (eLpNorm (u : Plane → Vec) 2 (cellμ c)).toReal :=
        congrArg ENNReal.toReal (eLpNorm_congr_ae hclass)
      _ = ‖u‖ := (Lp.norm_def u).symm
  have hreal' : (ENNReal.toReal (eLpNorm d 2 (cellMeasure c))) ^ 2 =
      c⁻¹ * ‖planeShiftL2 hc w xC - xC‖ ^ 2 := by
    simpa [u, d] using hreal.trans (congrArg (fun r => c⁻¹ * r ^ 2) hcenter)
  simpa [d, xC, xP] using hreal'

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.eLpNorm_sq_heatVecTranslationIncrement
