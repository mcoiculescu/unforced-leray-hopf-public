import UnforcedLeray.Lib.TrainB.P0Horizontal
import UnforcedLeray.Lib.TrainB.P0Translation
import UnforcedLeray.Lib.HeatCylinder.PeriodicLift

/-!
# Commutation of the actual centered cylinder coordinate shifts

Horizontal periodic shifts and vertical Euclidean shifts act on independent coordinates. Their
commutation is recorded on the actual centered-cell `L²` quotient using periodic representatives.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Cyl (L2v cellμ Vec2)

theorem qShiftL2_etaShiftL2_comm {c a b : ℝ} (hc : 0 < c) (x : L2v c) :
    UnforcedLeray.TrainB.qShiftL2 hc a (UnforcedLeray.TrainB.etaShiftL2 c b x) =
      UnforcedLeray.TrainB.etaShiftL2 c b (UnforcedLeray.TrainB.qShiftL2 hc a x) := by
  let g : Plane → Vec2 :=
    centeredPerLift hc (UnforcedLeray.TrainB.measurableL2Rep x)
  have hgper : UnforcedLeray.Cyl.IsPeriodic c g := centeredPerLift_periodic hc _
  have hgcell : g =ᵐ[cellμ c] (x : Plane → Vec2) := by
    filter_upwards [UnforcedLeray.TrainB.measurableL2Rep_ae x,
      ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with z hz hcell
    change centeredPerLift hc (UnforcedLeray.TrainB.measurableL2Rep x) z = x z
    rw [centeredPerLift_eq_on_cell hc _ hcell]
    exact hz
  have hperShift : UnforcedLeray.Cyl.IsPeriodic c
      (fun z : Plane => g (z + ((0 : ℝ), b))) := by
    intro z
    change g ((z.1 + c, z.2) + ((0 : ℝ), b)) = g (z + ((0 : ℝ), b))
    have hz : (z.1 + c, z.2) + ((0 : ℝ), b) =
        (z + ((0 : ℝ), b)) + ((c, 0) : Plane) := by
      ext <;> simp <;> ring
    rw [hz]
    rw [show (z + ((0 : ℝ), b)) + ((c, 0) : Plane) =
        ((z + ((0 : ℝ), b)).1 + c, (z + ((0 : ℝ), b)).2) by ext <;> simp]
    exact hgper (z + ((0 : ℝ), b))
  have heta : (UnforcedLeray.TrainB.etaShiftL2 c b x : Plane → Vec2) =ᵐ[
      cellμ c] fun z => g (z + ((0 : ℝ), b)) := by
    filter_upwards [UnforcedLeray.TrainB.etaShiftL2_ae (c := c) (a := b) x,
      (UnforcedLeray.TrainB.measurePreserving_etaShift c b).quasiMeasurePreserving.ae hgcell]
      with z hshift hrep
    exact hshift.trans hrep.symm
  have hleft := UnforcedLeray.TrainB.qShiftL2_ae_periodic (a := a) hc
    (UnforcedLeray.TrainB.etaShiftL2 c b x) hperShift heta
  have hqx := UnforcedLeray.TrainB.qShiftL2_ae_periodic (a := a) hc x hgper hgcell.symm
  have hright' : (fun z : Plane =>
      (UnforcedLeray.TrainB.qShiftL2 hc a x : Plane → Vec2)
        (z + ((0 : ℝ), b))) =ᵐ[cellμ c]
      fun z => UnforcedLeray.TrainB.qShiftField a g (z + ((0 : ℝ), b)) := by
    exact (UnforcedLeray.TrainB.measurePreserving_etaShift c b).quasiMeasurePreserving.ae hqx
  have hetaOut := UnforcedLeray.TrainB.etaShiftL2_ae (c := c) (a := b)
    (UnforcedLeray.TrainB.qShiftL2 hc a x)
  apply Lp.ext
  filter_upwards [hleft, hright', hetaOut] with z hleft hright heta
  calc
    (UnforcedLeray.TrainB.qShiftL2 hc a
      (UnforcedLeray.TrainB.etaShiftL2 c b x) : Plane → Vec2) z =
        UnforcedLeray.TrainB.qShiftField a
          (fun y => g (y + ((0 : ℝ), b))) z := hleft
    _ = UnforcedLeray.TrainB.qShiftField a g (z + ((0 : ℝ), b)) := by
      simp only [UnforcedLeray.TrainB.qShiftField]
      congr 1
      ext <;> simp <;> ring
    _ = (UnforcedLeray.TrainB.qShiftL2 hc a x : Plane → Vec2)
        (z + ((0 : ℝ), b)) := hright.symm
    _ = (UnforcedLeray.TrainB.etaShiftL2 c b
        (UnforcedLeray.TrainB.qShiftL2 hc a x) : Plane → Vec2) z := heta.symm

#print axioms UnforcedLeray.HeatCylinder.qShiftL2_etaShiftL2_comm

end UnforcedLeray.HeatCylinder
