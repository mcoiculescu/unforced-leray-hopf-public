import UnforcedLeray.Lib.HeatCylinder.HeatVecCoordinateShiftsCommute
import UnforcedLeray.Lib.HeatCylinder.HeatL2PlaneTranslation
import UnforcedLeray.Lib.TrainB.P0Horizontal
import UnforcedLeray.Lib.TrainB.P0Translation

/-!
# The actual centered planar translation group on vector `L²`

These composition laws make the already strongly continuous translation orbit continuous at every
shift, which is needed for the Gaussian Bochner average.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Cyl (L2v cellμ Vec2)

theorem qShiftL2_add_comp {c a b : ℝ} (hc : 0 < c) (x : L2v c) :
    UnforcedLeray.TrainB.qShiftL2 hc a (UnforcedLeray.TrainB.qShiftL2 hc b x) =
      UnforcedLeray.TrainB.qShiftL2 hc (a + b) x := by
  let g : Plane → Vec2 := centeredPerLift hc (UnforcedLeray.TrainB.measurableL2Rep x)
  have hgper : UnforcedLeray.Cyl.IsPeriodic c g := centeredPerLift_periodic hc _
  have hgcell : g =ᵐ[cellμ c] (x : Plane → Vec2) := by
    filter_upwards [UnforcedLeray.TrainB.measurableL2Rep_ae x,
      ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with z hz hcell
    change centeredPerLift hc (UnforcedLeray.TrainB.measurableL2Rep x) z = x z
    rw [centeredPerLift_eq_on_cell hc _ hcell]
    exact hz
  have hgb : (UnforcedLeray.TrainB.qShiftL2 hc b x : Plane → Vec2) =ᵐ[cellμ c]
      UnforcedLeray.TrainB.qShiftField b g :=
    UnforcedLeray.TrainB.qShiftL2_ae_periodic (a := b) hc x hgper hgcell.symm
  have hgbper : UnforcedLeray.Cyl.IsPeriodic c (UnforcedLeray.TrainB.qShiftField b g) := by
    intro z
    change g ((z.1 + c, z.2) + ((b, 0) : Plane)) = g (z + ((b, 0) : Plane))
    rw [show (z.1 + c, z.2) + ((b, 0) : Plane) =
      (z + ((b, 0) : Plane)) + ((c, 0) : Plane) by ext <;> simp <;> ring]
    rw [show (z + ((b, 0) : Plane)) + ((c, 0) : Plane) =
      ((z + ((b, 0) : Plane)).1 + c, (z + ((b, 0) : Plane)).2) by ext <;> simp]
    exact hgper (z + ((b, 0) : Plane))
  have hab : (UnforcedLeray.TrainB.qShiftL2 hc a
      (UnforcedLeray.TrainB.qShiftL2 hc b x) : Plane → Vec2) =ᵐ[cellμ c]
      UnforcedLeray.TrainB.qShiftField a (UnforcedLeray.TrainB.qShiftField b g) :=
    UnforcedLeray.TrainB.qShiftL2_ae_periodic (a := a) hc
      (UnforcedLeray.TrainB.qShiftL2 hc b x) hgbper hgb
  have hasum : (UnforcedLeray.TrainB.qShiftL2 hc (a + b) x : Plane → Vec2) =ᵐ[cellμ c]
      UnforcedLeray.TrainB.qShiftField (a + b) g :=
    UnforcedLeray.TrainB.qShiftL2_ae_periodic (a := a + b) hc x hgper hgcell.symm
  apply Lp.ext
  filter_upwards [hab, hasum] with z hab hsum
  calc
    (UnforcedLeray.TrainB.qShiftL2 hc a
      (UnforcedLeray.TrainB.qShiftL2 hc b x) : Plane → Vec2) z =
        UnforcedLeray.TrainB.qShiftField a
          (UnforcedLeray.TrainB.qShiftField b g) z := hab
    _ = UnforcedLeray.TrainB.qShiftField (a + b) g z := by
      simp only [UnforcedLeray.TrainB.qShiftField]
      congr 1
      ext <;> simp <;> ring
    _ = (UnforcedLeray.TrainB.qShiftL2 hc (a + b) x : Plane → Vec2) z := hsum.symm

theorem etaShiftL2_add_comp {c a b : ℝ} (x : L2v c) :
    UnforcedLeray.TrainB.etaShiftL2 c a (UnforcedLeray.TrainB.etaShiftL2 c b x) =
      UnforcedLeray.TrainB.etaShiftL2 c (a + b) x := by
  have hab := UnforcedLeray.TrainB.etaShiftL2_ae (c := c) (a := a)
    (UnforcedLeray.TrainB.etaShiftL2 c b x)
  have hb := UnforcedLeray.TrainB.etaShiftL2_ae (c := c) (a := b) x
  have hbshift := (UnforcedLeray.TrainB.measurePreserving_etaShift c a).quasiMeasurePreserving.ae hb
  have hsum := UnforcedLeray.TrainB.etaShiftL2_ae (c := c) (a := a + b) x
  apply Lp.ext
  filter_upwards [hab, hbshift, hsum] with z hab hb hsum
  calc
    (UnforcedLeray.TrainB.etaShiftL2 c a
      (UnforcedLeray.TrainB.etaShiftL2 c b x) : Plane → Vec2) z =
        (UnforcedLeray.TrainB.etaShiftL2 c b x : Plane → Vec2)
          (z + ((0 : ℝ), a)) := hab
    _ = x ((z + ((0 : ℝ), a)) + ((0 : ℝ), b)) := hb
    _ = x (z + ((0 : ℝ), a + b)) := by congr 1 <;> ext <;> simp <;> ring
    _ = (UnforcedLeray.TrainB.etaShiftL2 c (a + b) x : Plane → Vec2) z := hsum.symm

theorem planeShiftL2_add_comp {c : ℝ} (hc : 0 < c) (w v : Plane) (x : L2v c) :
    planeShiftL2 hc w (planeShiftL2 hc v x) = planeShiftL2 hc (w + v) x := by
  change UnforcedLeray.TrainB.qShiftL2 hc (-w.1)
      (UnforcedLeray.TrainB.etaShiftL2 c (-w.2)
        (UnforcedLeray.TrainB.qShiftL2 hc (-v.1)
          (UnforcedLeray.TrainB.etaShiftL2 c (-v.2) x))) = _
  rw [← qShiftL2_etaShiftL2_comm hc (a := -v.1) (b := -w.2)]
  rw [qShiftL2_add_comp hc, etaShiftL2_add_comp]
  simp only [planeShiftL2]
  simp only [Prod.fst_add, Prod.snd_add]
  congr 2 <;> ring

#print axioms UnforcedLeray.HeatCylinder.qShiftL2_add_comp
#print axioms UnforcedLeray.HeatCylinder.etaShiftL2_add_comp
#print axioms UnforcedLeray.HeatCylinder.planeShiftL2_add_comp

end UnforcedLeray.HeatCylinder
