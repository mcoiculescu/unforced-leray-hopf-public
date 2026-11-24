import UnforcedLeray.Lib.TrainB.P0Translation
import UnforcedLeray.Lib.HeatCylinder.PeriodicLift
import UnforcedLeray.Lib.CylinderB.Periodize

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- Horizontal translation of a cylinder field representative. -/
def qShiftField (a : ℝ) (f : UnforcedLeray.GaussianVortex.Plane → Vec2) : UnforcedLeray.GaussianVortex.Plane → Vec2 :=
  fun z => f (z + ((a, 0) : UnforcedLeray.GaussianVortex.Plane))

/-- A periodic field has the same centered-cell `L²` norm after horizontal translation. -/
theorem eLpNorm_qShiftField_eq {c a : ℝ} (hc : 0 < c) {f : UnforcedLeray.GaussianVortex.Plane → Vec2}
    (hper : IsPeriodic c f) :
    eLpNorm (qShiftField a f) 2 (cellμ c) = eLpNorm f 2 (cellμ c) := by
  have hperB : UnforcedLeray.B0284.IsQPeriodic c f := by
    intro z
    exact hper z
  have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have hpTop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h := UnforcedLeray.Cyl.eLpNorm_cell_comp_sub hc hperB (p := (2 : ℝ≥0∞)) hp0 hpTop ((-a, 0) : UnforcedLeray.GaussianVortex.Plane)
  calc
    eLpNorm (qShiftField a f) 2 (cellμ c) =
        eLpNorm (fun z => f (z - ((-a, 0) : UnforcedLeray.GaussianVortex.Plane)))
          2 (cellμ c) := by
            congr 1
            funext z
            change f (z + ((a, 0) : UnforcedLeray.GaussianVortex.Plane)) =
              f (z - ((-a, 0) : UnforcedLeray.GaussianVortex.Plane))
            congr 1
            have hz : z + ((a, 0) : UnforcedLeray.GaussianVortex.Plane) =
                z - ((-a, 0) : UnforcedLeray.GaussianVortex.Plane) := by
              ext <;> simp
            rw [hz]
    _ = eLpNorm f 2 (cellμ c) := h

/-- The centered periodic lift converts a cylinder `L²` representative into a periodic field. -/
noncomputable def centeredLiftL2 {c : ℝ} (hc : 0 < c) (u : L2v c) : UnforcedLeray.GaussianVortex.Plane → Vec2 :=
  UnforcedLeray.HeatCylinder.centeredPerLift hc (u : UnforcedLeray.GaussianVortex.Plane → Vec2)

theorem centeredLiftL2_periodic {c : ℝ} (hc : 0 < c) (u : L2v c) :
    IsPeriodic c (centeredLiftL2 hc u) :=
  UnforcedLeray.HeatCylinder.centeredPerLift_periodic hc (u : UnforcedLeray.GaussianVortex.Plane → Vec2)

theorem centeredLiftL2_ae {c : ℝ} (hc : 0 < c) (u : L2v c) :
    centeredLiftL2 hc u =ᵐ[cellμ c] (u : UnforcedLeray.GaussianVortex.Plane → Vec2) := by
  filter_upwards [ae_restrict_mem (measurableSet_cell c)] with z hz
  exact UnforcedLeray.HeatCylinder.centeredPerLift_eq_on_cell hc (u : UnforcedLeray.GaussianVortex.Plane → Vec2) hz

/-- The horizontal shift preserves the norm of a centered-cell periodic lift. -/
theorem eLpNorm_qShift_centeredLift_eq {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    eLpNorm (qShiftField a (centeredLiftL2 hc u)) 2 (cellμ c) = eLpNorm (u : UnforcedLeray.GaussianVortex.Plane → Vec2) 2 (cellμ c) := by
  rw [eLpNorm_qShiftField_eq hc (centeredLiftL2_periodic hc u),
    eLpNorm_congr_ae (centeredLiftL2_ae hc u)]


/-- A measurable representative of a cylinder L² class. -/
noncomputable def measurableL2Rep {c : ℝ} (u : L2v c) : Plane → Vec2 :=
  (Lp.aestronglyMeasurable u).mk (u : Plane → Vec2)

theorem measurableL2Rep_measurable {c : ℝ} (u : L2v c) :
    Measurable (measurableL2Rep u) :=
  (Lp.aestronglyMeasurable u).measurable_mk

theorem measurableL2Rep_ae {c : ℝ} (u : L2v c) :
    measurableL2Rep u =ᵐ[cellμ c] (u : Plane → Vec2) :=
  (Lp.aestronglyMeasurable u).ae_eq_mk.symm

/-- The horizontal shift of an L² class, represented by shifting its canonical centered periodic
extension. -/
noncomputable def qShiftL2Rep {c : ℝ} (hc : 0 < c) (a : ℝ) (u : L2v c) : Plane → Vec2 :=
  qShiftField a (UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u))

theorem qShiftL2Rep_measurable {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    Measurable (qShiftL2Rep hc a u) := by
  apply (UnforcedLeray.HeatCylinder.measurable_centeredPerLift hc
    (measurableL2Rep_measurable u)).comp
  exact (measurable_id.add_const ((a, 0) : Plane))

theorem qShiftL2Rep_periodic {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    IsPeriodic c (qShiftL2Rep hc a u) := by
  intro z
  simp only [qShiftL2Rep, qShiftField]
  change UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u)
      ((z.1 + c, z.2) + ((a, 0) : Plane)) =
    UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u)
      (z + ((a, 0) : Plane))
  have hz : (z.1 + c, z.2) + ((a, 0) : Plane) =
      (z + ((a, 0) : Plane)) + ((c, 0) : Plane) := by
    ext <;> simp <;> ring
  rw [hz]
  rw [show (z + ((a, 0) : Plane)) + ((c, 0) : Plane) =
      (((z + ((a, 0) : Plane)).1 + c), (z + ((a, 0) : Plane)).2) by
        ext <;> simp]
  exact UnforcedLeray.HeatCylinder.centeredPerLift_periodic hc (measurableL2Rep u)
    (z + ((a, 0) : Plane))

theorem qShiftL2Rep_memLp {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    MemLp (qShiftL2Rep hc a u) 2 (cellμ c) := by
  refine ⟨(qShiftL2Rep_measurable hc u).aestronglyMeasurable, ?_⟩
  have hliftVol : UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u) =ᵐ[volume]
      centeredLiftL2 hc u :=
    UnforcedLeray.HeatCylinder.centeredPerLift_congr_ae hc (measurableL2Rep_ae u)
  have hlift : UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u) =ᵐ[cellμ c]
      centeredLiftL2 hc u := by
    exact (ae_restrict_of_ae hliftVol)
  have hnorm : eLpNorm (qShiftL2Rep hc a u) 2 (cellμ c) = eLpNorm (u : Plane → Vec2) 2 (cellμ c) := by
    calc
      eLpNorm (qShiftL2Rep hc a u) 2 (cellμ c) =
          eLpNorm (qShiftField a (centeredLiftL2 hc u)) 2 (cellμ c) := by
            exact eLpNorm_congr_ae (by
              have hshift := (measurePreserving_add_right volume ((a, 0) : Plane)).quasiMeasurePreserving.ae
                hliftVol
              have hshiftCell :
                  qShiftField a (UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u)) =ᵐ[cellμ c]
                    qShiftField a (centeredLiftL2 hc u) := by
                exact ae_restrict_of_ae hshift
              filter_upwards [hshiftCell] with z hz
              exact hz)
      _ = eLpNorm (u : Plane → Vec2) 2 (cellμ c) := eLpNorm_qShift_centeredLift_eq hc u
  rw [hnorm]
  exact (Lp.eLpNorm_lt_top u)

/-- The actual horizontal q-shift on the cylinder L² quotient. -/
noncomputable def qShiftL2 {c : ℝ} (hc : 0 < c) (a : ℝ) (u : L2v c) : L2v c :=
  (qShiftL2Rep_memLp hc u).toLp (qShiftL2Rep hc a u)

theorem qShiftL2_ae {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    (qShiftL2 hc a u : Plane → Vec2) =ᵐ[cellμ c] qShiftL2Rep hc a u :=
  (qShiftL2Rep_memLp hc u).coeFn_toLp


theorem centeredPerLift_add {c : ℝ} (hc : 0 < c) (f g : Plane → Vec2) (z : Plane) :
    UnforcedLeray.HeatCylinder.centeredPerLift hc (f + g) z =
      UnforcedLeray.HeatCylinder.centeredPerLift hc f z +
        UnforcedLeray.HeatCylinder.centeredPerLift hc g z := by
  rfl

private theorem measurableL2Rep_add_ae {c : ℝ} (u v : L2v c) :
    measurableL2Rep (u + v) =ᵐ[cellμ c] fun z => measurableL2Rep u z + measurableL2Rep v z := by
  filter_upwards [measurableL2Rep_ae (u + v), measurableL2Rep_ae u, measurableL2Rep_ae v,
    Lp.coeFn_add u v] with z huv hu hv hadd
  change measurableL2Rep (u + v) z = _
  rw [huv, hu, hv]
  exact hadd

private theorem qShiftL2Rep_add_ae {c a : ℝ} (hc : 0 < c) (u v : L2v c) :
    qShiftL2Rep hc a (u + v) =ᵐ[cellμ c]
      fun z => qShiftL2Rep hc a u z + qShiftL2Rep hc a v z := by
  have hbase := UnforcedLeray.HeatCylinder.centeredPerLift_congr_ae hc
    (measurableL2Rep_add_ae u v)
  have hbase' :
      UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep (u + v)) =ᵐ[volume]
        fun z => UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u) z +
          UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep v) z := by
    filter_upwards [hbase] with z hz
    rw [hz]
    exact centeredPerLift_add hc (measurableL2Rep u) (measurableL2Rep v) z
  have hshift := (measurePreserving_add_right volume ((a, 0) : Plane)).quasiMeasurePreserving.ae hbase'
  have hcell :
      (fun z => UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep (u + v))
        (z + ((a, 0) : Plane))) =ᵐ[cellμ c]
        fun z => UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u)
          (z + ((a, 0) : Plane)) +
          UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep v)
            (z + ((a, 0) : Plane)) := by
    exact ae_restrict_of_ae (s := cell c) hshift
  change qShiftL2Rep hc a (u + v) =ᵐ[cellμ c]
    fun z => qShiftL2Rep hc a u z + qShiftL2Rep hc a v z
  exact hcell

theorem qShiftL2_add {c a : ℝ} (hc : 0 < c) (u v : L2v c) :
    qShiftL2 hc a (u + v) = qShiftL2 hc a u + qShiftL2 hc a v := by
  apply Lp.ext
  have hrep := qShiftL2Rep_add_ae (a := a) hc u v
  filter_upwards [qShiftL2_ae (a := a) hc (u + v), qShiftL2_ae (a := a) hc u,
    qShiftL2_ae (a := a) hc v, hrep,
    Lp.coeFn_add (qShiftL2 hc a u) (qShiftL2 hc a v)] with z huv hu hv hrep hadd
  calc
    (qShiftL2 hc a (u + v) : Plane → Vec2) z = qShiftL2Rep hc a (u + v) z := huv
    _ = qShiftL2Rep hc a u z + qShiftL2Rep hc a v z := hrep
    _ = ((qShiftL2 hc a u + qShiftL2 hc a v : L2v c) : Plane → Vec2) z := by
      rw [← hu, ← hv]
      exact hadd.symm


private theorem measurableL2Rep_smul_ae {c : ℝ} (r : ℝ) (u : L2v c) :
    measurableL2Rep (r • u) =ᵐ[cellμ c] fun z => r • measurableL2Rep u z := by
  filter_upwards [measurableL2Rep_ae (r • u), measurableL2Rep_ae u, Lp.coeFn_smul r u]
    with z hru hu hsmul
  rw [hru, hu]
  exact hsmul

private theorem qShiftL2Rep_smul_ae {c a : ℝ} (hc : 0 < c) (r : ℝ) (u : L2v c) :
    qShiftL2Rep hc a (r • u) =ᵐ[cellμ c]
      fun z => r • qShiftL2Rep hc a u z := by
  have hbase := UnforcedLeray.HeatCylinder.centeredPerLift_congr_ae hc
    (measurableL2Rep_smul_ae r u)
  have hbase' :
      UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep (r • u)) =ᵐ[volume]
        fun z => r • UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u) z := by
    filter_upwards [hbase] with z hz
    rw [hz]
    rfl
  have hshift := (measurePreserving_add_right volume ((a, 0) : Plane)).quasiMeasurePreserving.ae hbase'
  change _ =ᵐ[cellμ c] _
  exact ae_restrict_of_ae (s := cell c) hshift

theorem qShiftL2_smul {c a : ℝ} (hc : 0 < c) (r : ℝ) (u : L2v c) :
    qShiftL2 hc a (r • u) = r • qShiftL2 hc a u := by
  apply Lp.ext
  filter_upwards [qShiftL2_ae (a := a) hc (r • u), qShiftL2_ae (a := a) hc u,
    qShiftL2Rep_smul_ae (a := a) hc r u, Lp.coeFn_smul r (qShiftL2 hc a u)] with
    z hru hu hrep hsmul
  calc
    (qShiftL2 hc a (r • u) : Plane → Vec2) z = qShiftL2Rep hc a (r • u) z := hru
    _ = r • qShiftL2Rep hc a u z := hrep
    _ = (r • (qShiftL2 hc a u : Plane → Vec2)) z := by
      rw [← hu]
      rfl
    _ = (((r • qShiftL2 hc a u : L2v c) : Plane → Vec2) z) := hsmul.symm

/-- The horizontal shift packaged as a linear map on the actual cylinder L² quotient. -/
noncomputable def qShiftL2Linear {c : ℝ} (hc : 0 < c) (a : ℝ) :
    L2v c →ₗ[ℝ] L2v c where
  toFun := qShiftL2 hc a
  map_add' := qShiftL2_add (hc := hc) (a := a)
  map_smul' := qShiftL2_smul (hc := hc) (a := a)

theorem eLpNorm_qShiftL2_eq {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    eLpNorm (qShiftL2 hc a u : Plane → Vec2) 2 (cellμ c) =
      eLpNorm (u : Plane → Vec2) 2 (cellμ c) := by
  rw [eLpNorm_congr_ae (qShiftL2_ae (a := a) hc u)]
  have h := qShiftL2Rep_memLp hc (a := a) u
  have hbase : eLpNorm (qShiftL2Rep hc a u) 2 (cellμ c) =
      eLpNorm (qShiftField a (centeredLiftL2 hc u)) 2 (cellμ c) := by
    have hliftVol := UnforcedLeray.HeatCylinder.centeredPerLift_congr_ae hc
      (measurableL2Rep_ae u)
    have hshift := (measurePreserving_add_right volume ((a, 0) : Plane)).quasiMeasurePreserving.ae hliftVol
    have hcell := ae_restrict_of_ae (s := cell c) hshift
    exact eLpNorm_congr_ae hcell
  rw [hbase, eLpNorm_qShift_centeredLift_eq hc u]

/-- The horizontal shift is an actual linear isometry on periodic cylinder L². -/
noncomputable def qShiftL2Isometry {c : ℝ} (hc : 0 < c) (a : ℝ) :
    L2v c →ₗᵢ[ℝ] L2v c where
  toLinearMap := qShiftL2Linear hc a
  norm_map' := by
    intro u
    change ‖qShiftL2 hc a u‖ = ‖u‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_qShiftL2_eq (a := a) hc u]


theorem centeredPerLift_ae_eq_periodic {c : ℝ} (hc : 0 < c) {f : Plane → Vec2}
    (hper : IsPeriodic c f) :
    UnforcedLeray.HeatCylinder.centeredPerLift hc f =ᵐ[volume] f := by
  let S : Set Plane := {z | UnforcedLeray.HeatCylinder.centeredPerLift hc f z ≠ f z}
  have hSper : UnforcedLeray.B0284.IsQPeriodic c (· ∈ S) := by
    intro z
    change (UnforcedLeray.HeatCylinder.centeredPerLift hc f (z.1 + c, z.2) ≠ f (z.1 + c, z.2)) =
      (UnforcedLeray.HeatCylinder.centeredPerLift hc f z ≠ f z)
    rw [UnforcedLeray.HeatCylinder.centeredPerLift_periodic hc f z, hper z]
  have hcell : volume (S ∩ cell c) = 0 := by
    have hEq : ∀ᵐ z ∂cellμ c, UnforcedLeray.HeatCylinder.centeredPerLift hc f z = f z := by
      filter_upwards [ae_restrict_mem (measurableSet_cell c)] with z hz
      exact UnforcedLeray.HeatCylinder.centeredPerLift_eq_on_cell hc f hz
    have hzero : volume.restrict (cell c) S = 0 := by
      have hz := ae_iff.mp hEq
      simpa [S, Cyl.cellμ] using hz
    rw [Measure.restrict_apply' (measurableSet_cell c)] at hzero
    simpa [S, Set.inter_comm] using hzero
  have hnull := (isAddFundamentalDomain_cell hc).measure_zero_of_invariant S ?_ hcell
  · exact ae_iff.mpr (by simpa [S] using hnull)
  · rintro ⟨v, hv⟩
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hv
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have heq : (-(⟨m • ((c, 0) : Plane), hv⟩ : AddSubgroup.zmultiples ((c, 0) : Plane)) +ᵥ z : Plane) =
        (z.1 + ((-m : ℤ) : ℝ) * c, z.2) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add]
      ext <;> simp <;> ring
    rw [heq]
    exact iff_of_eq (UnforcedLeray.B0289.IsQPeriodic.add_int_mul hSper (-m) z)

private theorem qShiftL2Rep_neg_comp_ae {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    qShiftL2Rep hc (-a) (qShiftL2 hc a u) =ᵐ[cellμ c] (u : Plane → Vec2) := by
  have hout : measurableL2Rep (qShiftL2 hc a u) =ᵐ[cellμ c] qShiftL2Rep hc a u := by
    exact (measurableL2Rep_ae (qShiftL2 hc a u)).trans (qShiftL2_ae (a := a) hc u)
  have hlift := UnforcedLeray.HeatCylinder.centeredPerLift_congr_ae hc hout
  have hshift := (measurePreserving_add_right volume ((-a, 0) : Plane)).quasiMeasurePreserving.ae hlift
  have hcell := ae_restrict_of_ae (s := cell c) hshift
  have hperiodic := centeredPerLift_ae_eq_periodic hc (qShiftL2Rep_periodic (a := a) hc u)
  have hperiodicShift := (measurePreserving_add_right volume ((-a, 0) : Plane)).quasiMeasurePreserving.ae hperiodic
  have hperiodicCell := ae_restrict_of_ae (s := cell c) hperiodicShift
  have hcancel : qShiftField (-a) (qShiftL2Rep hc a u) =
      UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u) := by
    funext z
    simp only [qShiftL2Rep, qShiftField]
    congr 1
    ext <;> simp <;> ring
  have hbase : UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u) =ᵐ[cellμ c]
      (u : Plane → Vec2) := by
    filter_upwards [ae_restrict_mem (measurableSet_cell c), measurableL2Rep_ae u] with z hz hu
    rw [UnforcedLeray.HeatCylinder.centeredPerLift_eq_on_cell hc (measurableL2Rep u) hz]
    exact hu
  filter_upwards [hcell, hperiodicCell, hbase] with z hout hper hbase
  change qShiftL2Rep hc (-a) (qShiftL2 hc a u) z = _ at hout
  change qShiftField (-a) (UnforcedLeray.HeatCylinder.centeredPerLift hc
    (qShiftL2Rep hc a u)) z = _ at hper
  calc
    qShiftL2Rep hc (-a) (qShiftL2 hc a u) z =
        UnforcedLeray.HeatCylinder.centeredPerLift hc
          (qShiftL2Rep hc a u) (z + ((-a, 0) : Plane)) := hout
    _ = qShiftL2Rep hc a u (z + ((-a, 0) : Plane)) := hper
    _ = qShiftField (-a) (qShiftL2Rep hc a u) z := rfl
    _ = UnforcedLeray.HeatCylinder.centeredPerLift hc (measurableL2Rep u) z := by
      exact congrFun hcancel z
    _ = (u : Plane → Vec2) z := hbase

theorem qShiftL2_neg_comp {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    qShiftL2 hc (-a) (qShiftL2 hc a u) = u := by
  apply Lp.ext
  filter_upwards [qShiftL2_ae (a := -a) hc (qShiftL2 hc a u), qShiftL2Rep_neg_comp_ae hc u]
    with z hout hrep
  exact hout.trans hrep

theorem qShiftL2_surjective {c a : ℝ} (hc : 0 < c) : Function.Surjective (qShiftL2 hc a) := by
  intro u
  refine ⟨qShiftL2 hc (-a) u, ?_⟩
  simpa [neg_neg] using qShiftL2_neg_comp (a := -a) hc u


theorem qShiftL2_ae_centeredLift {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    (qShiftL2 hc a u : Plane → Vec2) =ᵐ[cellμ c]
      qShiftField a (centeredLiftL2 hc u) := by
  have hlift := UnforcedLeray.HeatCylinder.centeredPerLift_congr_ae hc (measurableL2Rep_ae u)
  have hshift := (measurePreserving_add_right volume ((a, 0) : Plane)).quasiMeasurePreserving.ae hlift
  have hcell := ae_restrict_of_ae (s := cell c) hshift
  filter_upwards [qShiftL2_ae (a := a) hc u, hcell] with z hclass hrep
  exact hclass.trans hrep

theorem qShiftL2_ae_periodic {c a : ℝ} (hc : 0 < c) (u : L2v c) {f : Plane → Vec2}
    (hper : IsPeriodic c f) (huf : (u : Plane → Vec2) =ᵐ[cellμ c] f) :
    (qShiftL2 hc a u : Plane → Vec2) =ᵐ[cellμ c] qShiftField a f := by
  have hlift := UnforcedLeray.HeatCylinder.centeredPerLift_congr_ae hc huf
  have hperVol := centeredPerLift_ae_eq_periodic hc hper
  have hglobal : centeredLiftL2 hc u =ᵐ[volume] f := hlift.trans hperVol
  have hshift := (measurePreserving_add_right volume ((a, 0) : Plane)).quasiMeasurePreserving.ae hglobal
  have hcell := ae_restrict_of_ae (s := cell c) hshift
  filter_upwards [qShiftL2_ae_centeredLift (a := a) hc u, hcell] with z hclass hrep
  exact hclass.trans hrep


/-- Translate a periodic test in the horizontal cylinder coordinate. -/
def qShiftTest (a : ℝ) (φ : Plane → ℝ) : Plane → ℝ :=
  fun z => φ (z + ((a, 0) : Plane))

theorem isCylTest_qShiftTest {c a : ℝ} {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) : Sob.IsCylTest c (qShiftTest a φ) := by
  obtain ⟨R, hR⟩ := hφ.bounded
  refine ⟨hφ.smooth.comp (contDiff_id.add contDiff_const), ?_, ⟨R, ?_⟩⟩
  · intro z
    change φ ((z + ((c, 0) : Plane)) + ((a, 0) : Plane)) = φ (z + ((a, 0) : Plane))
    have hz : (z + ((c, 0) : Plane)) + ((a, 0) : Plane) =
        (z + ((a, 0) : Plane)) + ((c, 0) : Plane) := by
      ext <;> simp <;> ring
    rw [hz]
    exact hφ.periodic (z + ((a, 0) : Plane))
  · intro z hz
    have hz' : R < |(z + ((a, 0) : Plane)).2| := by simpa using hz
    exact hR (z + ((a, 0) : Plane)) hz' 

theorem qShiftTest_partialQ {c a : ℝ} {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) (z : Plane) :
    Cyl.partialQ (qShiftTest a φ) z = Cyl.partialQ φ (z + ((a, 0) : Plane)) := by
  rw [Cyl.partialQ_eq_fderiv (isCylTest_qShiftTest (a := a) hφ).differentiable,
    Cyl.partialQ_eq_fderiv hφ.differentiable]
  have hcomp := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := z) ((a, 0) : Plane)
  have h := congrArg (fun D => D ((1 : ℝ), (0 : ℝ))) hcomp
  change fderiv ℝ (fun x => φ (x + ((a, 0) : Plane))) z ((1 : ℝ), (0 : ℝ)) =
    fderiv ℝ φ (z + ((a, 0) : Plane)) ((1 : ℝ), (0 : ℝ))
  exact h

theorem qShiftTest_partialEta {c a : ℝ} {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) (z : Plane) :
    Cyl.partialEta (qShiftTest a φ) z = Cyl.partialEta φ (z + ((a, 0) : Plane)) := by
  rw [Cyl.partialEta_eq_fderiv (isCylTest_qShiftTest (a := a) hφ).differentiable,
    Cyl.partialEta_eq_fderiv hφ.differentiable]
  have hcomp := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := z) ((a, 0) : Plane)
  have h := congrArg (fun D => D ((0 : ℝ), (1 : ℝ))) hcomp
  change fderiv ℝ (fun x => φ (x + ((a, 0) : Plane))) z ((0 : ℝ), (1 : ℝ)) =
    fderiv ℝ φ (z + ((a, 0) : Plane)) ((0 : ℝ), (1 : ℝ))
  exact h

theorem gradT_periodic {c : ℝ} {φ : Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    IsPeriodic c (Cyl.gradT φ) := by
  have hper : IsPeriodic c φ := by
    intro z
    have hz : z + ((c, 0) : Plane) = (z.1 + c, z.2) := by ext <;> simp
    rw [← hz]
    exact hφ.periodic z
  have hq : IsPeriodic c (Cyl.partialQ φ) :=
    Cyl.IsPeriodic.partialQ (c := c) (f := φ) hper
  have hη : IsPeriodic c (Cyl.partialEta φ) :=
    Cyl.IsPeriodic.partialEta (c := c) (f := φ) hper
  intro z
  ext i
  fin_cases i <;> simp [Cyl.gradT, Cyl.vec, hq z, hη z]

theorem qShiftL2_gradL {c a : ℝ} (hc : 0 < c) {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) :
    qShiftL2 hc a (Cyl.gradL hφ) = Cyl.gradL (isCylTest_qShiftTest (a := a) hφ) := by
  apply Lp.ext
  have hclass : (Cyl.gradL hφ : Plane → Vec2) =ᵐ[cellμ c] Cyl.gradT φ :=
    (Cyl.memLp_gradT hφ).coeFn_toLp
  have hshift := qShiftL2_ae_periodic (a := a) hc (Cyl.gradL hφ) (gradT_periodic hφ) hclass
  have hout : (Cyl.gradL (isCylTest_qShiftTest (a := a) hφ) : Plane → Vec2) =ᵐ[cellμ c]
      Cyl.gradT (qShiftTest a φ) :=
    (Cyl.memLp_gradT (isCylTest_qShiftTest (a := a) hφ)).coeFn_toLp
  filter_upwards [hshift, hout] with z hshift hout
  calc
    (qShiftL2 hc a (Cyl.gradL hφ) : Plane → Vec2) z = qShiftField a (Cyl.gradT φ) z := hshift
    _ = Cyl.gradT (qShiftTest a φ) z := by
      ext i
      fin_cases i <;> simp [qShiftField, Cyl.gradT, qShiftTest_partialQ (a := a) hφ z,
        qShiftTest_partialEta (a := a) hφ z]
    _ = (Cyl.gradL (isCylTest_qShiftTest (a := a) hφ) : Plane → Vec2) z := hout.symm


theorem qShiftL2_mem_divFree {c a : ℝ} (hc : 0 < c) {u : L2v c}
    (hu : u ∈ Cyl.divFree c) : qShiftL2 hc a u ∈ Cyl.divFree c := by
  rw [Cyl.mem_divFree] at hu ⊢
  intro φ hφ
  let hψ := isCylTest_qShiftTest (a := -a) hφ
  calc
    inner ℝ (Cyl.gradL hφ) (qShiftL2 hc a u) =
        inner ℝ (qShiftL2 hc (-a) (Cyl.gradL hφ))
          (qShiftL2 hc (-a) (qShiftL2 hc a u)) := by
            symm
            exact (qShiftL2Isometry hc (-a)).inner_map_map
              (Cyl.gradL hφ) (qShiftL2 hc a u)
    _ = inner ℝ (Cyl.gradL hψ) u := by
          rw [qShiftL2_gradL hc (a := -a), qShiftL2_neg_comp hc (a := a)]
    _ = 0 := hu _ hψ

theorem qShiftL2_map_divFree_eq {c a : ℝ} (hc : 0 < c) :
    Submodule.map (qShiftL2Linear hc a) (Cyl.divFree c) = Cyl.divFree c := by
  apply le_antisymm
  · intro u hu
    rcases Submodule.mem_map.1 hu with ⟨v, hv, hvu⟩
    rw [← hvu]
    exact qShiftL2_mem_divFree hc (a := a) hv
  · intro u hu
    refine Submodule.mem_map.2 ⟨qShiftL2 hc (-a) u,
      qShiftL2_mem_divFree hc (a := -a) hu, ?_⟩
    simpa [qShiftL2Linear, neg_neg] using
      qShiftL2_neg_comp (a := -a) hc u

theorem qShiftL2_P0_comm {c a : ℝ} (hc : 0 < c) (u : L2v c) :
    qShiftL2 hc a (Cyl.P0 c u) = Cyl.P0 c (qShiftL2 hc a u) := by
  apply (Cyl.P0_eq_of_orthogonal
    (qShiftL2_mem_divFree hc (a := a) (Cyl.P0_mem u)) ?_).symm
  have hsub : qShiftL2 hc a u - qShiftL2 hc a (Cyl.P0 c u) =
      qShiftL2 hc a (u - Cyl.P0 c u) := (qShiftL2Linear hc a).map_sub _ _ |>.symm
  rw [hsub]
  intro w hw
  have hshiftw : qShiftL2 hc (-a) w ∈ Cyl.divFree c :=
    qShiftL2_mem_divFree hc (a := -a) hw
  have hinv : qShiftL2 hc a (qShiftL2 hc (-a) w) = w := by
    simpa [neg_neg] using (qShiftL2_neg_comp (a := -a) hc w)
  have horth := Cyl.sub_P0_mem_orthogonal u (qShiftL2 hc (-a) w) hshiftw
  have hinner := (qShiftL2Isometry hc a).inner_map_map
    (qShiftL2 hc (-a) w) (u - Cyl.P0 c u)
  calc
    inner ℝ w (qShiftL2 hc a (u - Cyl.P0 c u)) =
        inner ℝ (qShiftL2 hc a (qShiftL2 hc (-a) w))
          (qShiftL2 hc a (u - Cyl.P0 c u)) := by rw [hinv]
    _ = inner ℝ (qShiftL2 hc (-a) w) (u - Cyl.P0 c u) := hinner
    _ = 0 := horth



end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.eLpNorm_qShiftField_eq
#print axioms UnforcedLeray.TrainB.centeredLiftL2_ae
#print axioms UnforcedLeray.TrainB.eLpNorm_qShift_centeredLift_eq
#print axioms UnforcedLeray.TrainB.qShiftL2Isometry
#print axioms UnforcedLeray.TrainB.qShiftL2_surjective
#print axioms UnforcedLeray.TrainB.qShiftL2_gradL
#print axioms UnforcedLeray.TrainB.qShiftL2_mem_divFree
#print axioms UnforcedLeray.TrainB.qShiftL2_P0_comm
