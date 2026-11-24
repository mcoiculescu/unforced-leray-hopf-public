import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianCellFubini
import UnforcedLeray.Lib.TrainB.P0Translation
import UnforcedLeray.Lib.TrainB.P0Horizontal

/-!
# Pairings of actual cylinder translations

For a smooth periodic field, the existing quotient translation has the literal translated field
as its centered-cell representative. This connects the Gaussian average's CLM pairing to the
shift-side integrand in the cell Fubini theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (L2v cellμ)

/-- A planar quotient translation of a smooth periodic field is represented on the centered cell
by its literal value at `z-w`. -/
theorem planeShiftL2_ae_sub_of_cylSmooth {c : ℝ} (hc : 0 < c)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hTm : MemLp T 2 (cellμ c)) (w : Plane) :
    (planeShiftL2 hc w (hTm.toLp T) : Plane → Vec) =ᵐ[cellμ c]
      fun z => T (z - w) := by
  let x : L2v c := hTm.toLp T
  let y : L2v c := UnforcedLeray.TrainB.etaShiftL2 c (-w.2) x
  let Tη : Plane → Vec := fun z => T (z + ((0 : ℝ), -w.2))
  have hTηper : UnforcedLeray.Cyl.IsPeriodic c Tη := by
    intro z
    dsimp [Tη]
    simpa only [Prod.add_def, add_zero, sub_eq_add_neg] using
      hT.periodic (z.1, z.2 - w.2)
  have hsource :
      (fun z => x (z + ((0 : ℝ), -w.2))) =ᵐ[cellμ c] Tη := by
    have hshift :=
      (UnforcedLeray.TrainB.measurePreserving_etaShift c (-w.2)).quasiMeasurePreserving.ae
        hTm.coeFn_toLp
    filter_upwards [hshift] with z hz
    exact hz
  have hη : (y : Plane → Vec) =ᵐ[cellμ c] Tη := by
    have hclass := UnforcedLeray.TrainB.etaShiftL2_ae (c := c) (a := -w.2) x
    exact hclass.trans hsource
  have hq := UnforcedLeray.TrainB.qShiftL2_ae_periodic (a := -w.1) hc y
    hTηper hη
  have hpoint : (fun z : Plane =>
      UnforcedLeray.TrainB.qShiftField (-w.1) Tη z) = fun z => T (z - w) := by
    funext z
    change T (z + ((-w.1, 0) : Plane) + ((0 : ℝ), -w.2)) = T (z - w)
    congr 1
    ext <;> simp [sub_eq_add_neg]
  change (UnforcedLeray.TrainB.qShiftL2 hc (-w.1) y : Plane → Vec) =ᵐ[cellμ c]
    fun z => T (z - w)
  exact hq.trans (Filter.Eventually.of_forall (congrFun hpoint))

/-- The real L² pairing of a shifted smooth field is the integral of the corresponding literal
cell pairing. -/
theorem inner_planeShiftL2_smooth_eq_integral {c : ℝ} (hc : 0 < c)
    {T U : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (hTm : MemLp T 2 (cellμ c)) (hUm : MemLp U 2 (cellμ c)) (w : Plane) :
    ⟪planeShiftL2 hc w (hTm.toLp T), hUm.toLp U⟫_ℝ =
      ∫ z in UnforcedLeray.Cyl.cell c, ⟪T (z - w), U z⟫_ℝ := by
  have hF : MemLp (planeShiftL2 hc w (hTm.toLp T) : Plane → Vec) 2 (cellμ c) :=
    Lp.memLp (planeShiftL2 hc w (hTm.toLp T))
  rw [← Lp.toLp_coeFn (planeShiftL2 hc w (hTm.toLp T)) hF]
  rw [UnforcedLeray.Cyl.inner_toLp_eq hF hUm]
  apply integral_congr_ae
  filter_upwards [planeShiftL2_ae_sub_of_cylSmooth hc hT hTm w] with z hz
  rw [hz]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.planeShiftL2_ae_sub_of_cylSmooth
#print axioms UnforcedLeray.HeatCylinder.inner_planeShiftL2_smooth_eq_integral
