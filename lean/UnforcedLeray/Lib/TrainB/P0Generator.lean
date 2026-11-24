import UnforcedLeray.Lib.TrainB.P0Horizontal

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB


theorem qShiftField_periodic {c a : ℝ} {f : UnforcedLeray.GaussianVortex.Plane → Vec2} (hper : IsPeriodic c f) :
    IsPeriodic c (qShiftField a f) := by
  intro z
  change f ((z.1 + c, z.2) + ((a, 0) : UnforcedLeray.GaussianVortex.Plane)) = f (z + ((a, 0) : UnforcedLeray.GaussianVortex.Plane))
  have hz : (z.1 + c, z.2) + ((a, 0) : UnforcedLeray.GaussianVortex.Plane) =
      (z + ((a, 0) : UnforcedLeray.GaussianVortex.Plane)) + ((c, 0) : UnforcedLeray.GaussianVortex.Plane) := by
    ext <;> simp <;> ring
  rw [hz]
  have hcoord : z + ((a, 0) : UnforcedLeray.GaussianVortex.Plane) + ((c, 0) : UnforcedLeray.GaussianVortex.Plane) =
      ((z + ((a, 0) : UnforcedLeray.GaussianVortex.Plane)).1 + c,
        (z + ((a, 0) : UnforcedLeray.GaussianVortex.Plane)).2) := by
    ext <;> simp <;> ring
  rw [hcoord]
  exact hper (z + ((a, 0) : UnforcedLeray.GaussianVortex.Plane))

/-- Horizontal translations form a genuine group action on the centered cylinder L² quotient. -/
theorem qShiftL2_comp_add {c a b : ℝ} (hc : 0 < c) (u : L2v c) :
    qShiftL2 hc a (qShiftL2 hc b u) = qShiftL2 hc (a + b) u := by
  apply Lp.ext
  have hper : IsPeriodic c (qShiftField b (centeredLiftL2 hc u)) :=
    qShiftField_periodic (centeredLiftL2_periodic hc u)
  have hbase : (u : UnforcedLeray.GaussianVortex.Plane → Vec2) =ᵐ[cellμ c] centeredLiftL2 hc u :=
    (centeredLiftL2_ae hc u).symm
  have hb := qShiftL2_ae_periodic (a := b) hc u (centeredLiftL2_periodic hc u) hbase
  have ha := qShiftL2_ae_periodic (a := a) hc (qShiftL2 hc b u) hper hb
  have hab := qShiftL2_ae_periodic (a := a + b) hc u
    (centeredLiftL2_periodic hc u) hbase
  filter_upwards [ha, hab] with z ha hab
  calc
    (qShiftL2 hc a (qShiftL2 hc b u) : UnforcedLeray.GaussianVortex.Plane → Vec2) z =
        qShiftField a (qShiftField b (centeredLiftL2 hc u)) z := ha
    _ = qShiftField (a + b) (centeredLiftL2 hc u) z := by
      simp only [qShiftField]
      congr 1
      ext <;> simp <;> ring
    _ = (qShiftL2 hc (a + b) u : UnforcedLeray.GaussianVortex.Plane → Vec2) z := hab.symm

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.qShiftField_periodic
#print axioms UnforcedLeray.TrainB.qShiftL2_comp_add
