import UnforcedLeray.Lib.HeatCylinder.HeatVecApproxIdentity
import UnforcedLeray.Lib.HeatCylinder.HeatL2PlaneCenteredBridge
import UnforcedLeray.Lib.HeatCylinder.HeatL2PlaneTranslation

/-!
# Periodic translation bridge for normalized vector heat

The normalized B0284 quotient and Train's centered-cell Hilbert quotient use different base cells.
This leaf records the representative identities needed to move translation continuity between
those two actual carriers.
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

/-- The normalized canonical periodic lift fixes a periodic field pointwise. -/
theorem perLift_eq_self_of_periodic {c : ℝ} (hc : 0 < c) {E : Type*}
    {f : Plane → E} (hper : IsQPeriodic c f) : perLift hc f = f := by
  funext z
  change f (toIcoMod hc 0 z.1, z.2) = f z
  let m := toIcoDiv hc 0 z.1
  have hm : toIcoMod hc 0 z.1 + (m : ℝ) * c = z.1 := by
    have h := toIcoMod_add_toIcoDiv_zsmul hc 0 z.1
    simpa [m, zsmul_eq_mul] using h
  have hper' : UnforcedLeray.B0284.IsQPeriodic c f := hper
  calc
    f (toIcoMod hc 0 z.1, z.2) =
        f ((toIcoMod hc 0 z.1) + (m : ℝ) * c, z.2) :=
      (UnforcedLeray.B0289.IsQPeriodic.add_int_mul hper' m
        (toIcoMod hc 0 z.1, z.2)).symm
    _ = f z := by rw [hm]

/-- A measurable representative of a normalized-cell vector class, extended periodically to the
plane. -/
noncomputable def normalizedVecHeatRep {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : Plane → Vec :=
  perLift hc (AEStronglyMeasurable.mk (x : Plane → Vec) (Lp.aestronglyMeasurable x))

theorem normalizedVecHeatRep_measurable {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : Measurable (normalizedVecHeatRep hc x) := by
  exact measurable_perLift hc (Lp.aestronglyMeasurable x).measurable_mk

theorem normalizedVecHeatRep_periodic {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : IsQPeriodic c (normalizedVecHeatRep hc x) :=
  perLift_periodic hc _

theorem normalizedVecHeatRep_ae {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    normalizedVecHeatRep hc x =ᵐ[cellMeasure c] (x : Plane → Vec) := by
  exact (perLift_ae_eq_cell hc _).trans (Lp.aestronglyMeasurable x).ae_eq_mk.symm

/-- The centered Train translation of a normalized vector heat input is represented by the
literal Euclidean shift of its canonical periodic representative. -/
theorem planeShiftL2_centeredVecOfNormalizedPlane_ae {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) :
    (planeShiftL2 hc w
      (centeredVecOfNormalizedPlane hc
        ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
          2 (cellMeasure c) x)) : Plane → Vec) =ᵐ[cellμ c]
      fun z => normalizedVecHeatRep hc x (z - w) := by
  let xP : Lp Plane 2 (cellMeasure c) :=
    (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c) x
  let g : Plane → Vec := normalizedPlaneVecRep hc xP
  let xC : UnforcedLeray.Cyl.L2v c := centeredVecOfNormalizedPlane hc xP
  have hgper : UnforcedLeray.Cyl.IsPeriodic c g := normalizedPlaneVecRep_periodic hc xP
  have hclass : (xC : Plane → Vec) =ᵐ[cellμ c] g :=
    centeredVecOfNormalizedPlane_coe_ae hc xP
  have hη := UnforcedLeray.TrainB.etaShiftL2_ae (c := c) (a := -w.2) xC
  have hηshift :
      (UnforcedLeray.TrainB.etaShiftL2 c (-w.2) xC : Plane → Vec) =ᵐ[cellμ c]
        fun z => g (z + ((0 : ℝ), -w.2)) := by
    filter_upwards [hη,
      (UnforcedLeray.TrainB.measurePreserving_etaShift c (-w.2)).quasiMeasurePreserving.ae
        hclass] with z h1 h2
    exact h1.trans h2
  let ηx := UnforcedLeray.TrainB.etaShiftL2 c (-w.2) xC
  have hηrep :
      UnforcedLeray.TrainB.measurableL2Rep ηx =ᵐ[cellμ c]
        fun z => g (z + ((0 : ℝ), -w.2)) :=
    (UnforcedLeray.TrainB.measurableL2Rep_ae ηx).trans hηshift
  have hηperiodic : UnforcedLeray.Cyl.IsPeriodic c
      (fun z => g (z + ((0 : ℝ), -w.2))) := by
    intro z
    change g ((z.1 + c, z.2) + ((0 : ℝ), -w.2)) =
      g (z + ((0 : ℝ), -w.2))
    have hleft : (z.1 + c, z.2) + ((0 : ℝ), -w.2) =
        (z.1 + c, z.2 - w.2) := by ext <;> simp [sub_eq_add_neg]
    have hright : z + ((0 : ℝ), -w.2) = (z.1, z.2 - w.2) := by
      ext <;> simp [sub_eq_add_neg]
    rw [hleft, hright]
    exact hgper (z.1, z.2 - w.2)
  have hq := UnforcedLeray.TrainB.qShiftL2_ae_periodic (a := -w.1) hc ηx
    hηperiodic hηshift
  have hcellRep :
      (AEStronglyMeasurable.mk (x : Plane → Vec) (Lp.aestronglyMeasurable x)) =ᵐ[cellMeasure c] g := by
    have hmkx :
        AEStronglyMeasurable.mk (x : Plane → Vec) (Lp.aestronglyMeasurable x) =ᵐ[cellMeasure c]
          (x : Plane → Vec) := (Lp.aestronglyMeasurable x).ae_eq_mk.symm
    have hsymm := ContinuousLinearMap.coeFn_compLpL
      (L := (UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane))
      (p := (2 : ℝ≥0∞)) (μ := cellMeasure c) x
    have hplane := (planeRep_spec hc xP).2.2
    filter_upwards [hmkx, hsymm, hplane] with z h1 h2 h3
    change (AEStronglyMeasurable.mk (x : Plane → Vec)
      (Lp.aestronglyMeasurable x)) z = g z
    calc
      _ = x z := h1
      _ = UnforcedLeray.Train.toVec (UnforcedLeray.Train.toVecL.symm (x z)) :=
        (UnforcedLeray.Train.toVecL.apply_symm_apply (x z)).symm
      _ = UnforcedLeray.Train.toVec (xP z) := congrArg UnforcedLeray.Train.toVec h2.symm
      _ = UnforcedLeray.Train.toVec (planeRep hc xP z) :=
        congrArg UnforcedLeray.Train.toVec h3.symm
      _ = g z := rfl
  have hperiodicRep : normalizedVecHeatRep hc x =ᵐ[volume] g := by
    have h := perLift_congr_ae hc hcellRep
    exact h.trans (ae_of_all _ (fun z => congrFun (perLift_eq_self_of_periodic hc
      (normalizedPlaneVecRep_periodic hc xP)) z))
  have hperiodicRepShift :=
    (measurePreserving_add_right volume (-w)).quasiMeasurePreserving.ae hperiodicRep
  have hperiodicRepShiftCell :
      (fun z => normalizedVecHeatRep hc x (z - w)) =ᵐ[cellμ c]
        fun z => g (z - w) := by
    filter_upwards [ae_restrict_of_ae hperiodicRepShift] with z hz
    simpa [sub_eq_add_neg] using hz
  filter_upwards [hq, hperiodicRepShiftCell] with z hzq hrep
  change (UnforcedLeray.TrainB.qShiftL2 hc (-w.1) ηx : Plane → Vec) z = _
  calc
    _ = UnforcedLeray.TrainB.qShiftField (-w.1)
          (fun z => g (z + ((0 : ℝ), -w.2))) z := hzq
    _ = g (z + ((-w.1, 0) : Plane) + ((0 : ℝ), -w.2)) := rfl
    _ = normalizedVecHeatRep hc x (z - w) := by
      have hz : z + ((-w.1, 0) : Plane) + ((0 : ℝ), -w.2) = z - w := by
        ext <;> simp [sub_eq_add_neg] <;> ring
      rw [hz]
      exact hrep.symm

/-- The centered canonical periodic lift fixes a centered-cell periodic field pointwise. -/
theorem centeredPerLift_eq_self_of_periodic {c : ℝ} (hc : 0 < c) {E : Type*}
    [NormedAddCommGroup E] {f : Plane → E}
    (hper : UnforcedLeray.Cyl.IsPeriodic c f) : centeredPerLift hc f = f := by
  funext z
  change f (toIcoMod hc (-(c / 2)) z.1, z.2) = f z
  let m := toIcoDiv hc (-(c / 2)) z.1
  have hm : toIcoMod hc (-(c / 2)) z.1 + (m : ℝ) * c = z.1 := by
    have h := toIcoMod_add_toIcoDiv_zsmul hc (-(c / 2)) z.1
    simpa [m, zsmul_eq_mul] using h
  have hper' : UnforcedLeray.B0284.IsQPeriodic c f := by
    intro x
    exact hper x
  calc
    f (toIcoMod hc (-(c / 2)) z.1, z.2) =
        f ((toIcoMod hc (-(c / 2)) z.1) + (m : ℝ) * c, z.2) :=
      (UnforcedLeray.B0289.IsQPeriodic.add_int_mul hper' m
        (toIcoMod hc (-(c / 2)) z.1, z.2)).symm
    _ = f z := by rw [hm]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.planeShiftL2_centeredVecOfNormalizedPlane_ae
