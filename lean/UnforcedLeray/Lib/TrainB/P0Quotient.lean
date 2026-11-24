import UnforcedLeray.Lib.TrainB.P0Generator
import UnforcedLeray.Lib.SobolevC.CylSmooth
import UnforcedLeray.Lib.Cylinder.IBP

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB


/-- Axial translation of a smooth cylinder field representative. -/
def etaShiftField (a : ℝ) (f : Plane → Vec2) : Plane → Vec2 :=
  fun z => f (z + ((0, a) : Plane))

/-- The horizontal difference quotient of a smooth periodic field is controlled in cell `L²`
by its horizontal derivative. This is the cylinder version of the FTC/Minkowski translation
modulus; periodicity is used only to preserve the centered-cell derivative norm under shifts. -/
theorem eLpNorm_qShift_sub_le_of_cylSmooth {c h : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    eLpNorm (fun z => qShiftField h u z - u z) 2 (cellμ c) ≤
      ENNReal.ofReal |h| * eLpNorm (Cyl.partialQ u) 2 (cellμ c) := by
  let v : Plane := (h, 0)
  have hdc : Continuous (fun p : Plane × ℝ => fderiv ℝ u (p.1 + p.2 • v) v) := by
    exact ((hu.smooth.continuous_fderiv (by simp)).comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hftc : ∀ y, u (y + v) - u y =
      ∫ t, fderiv ℝ u (y + t • v) v ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro y
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (f := fun t : ℝ => u (y + t • v))
      (f' := fun t => fderiv ℝ u (y + t • v) v)
      (fun t _ => by
        have hline : HasDerivAt (fun t : ℝ => y + t • v) v t := by
          simpa using ((hasDerivAt_id t).smul_const v).const_add y
        exact ((hu.smooth.differentiable (by simp)) (y + t • v)).hasFDerivAt.comp_hasDerivAt t hline)
      ((hdc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le zero_le_one] at h
    simpa [v, qShiftField] using h.symm
  have hrep : (fun y => qShiftField h u y - u y) =
      fun y => ∫ t, fderiv ℝ u (y + t • v) v ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    funext y
    simpa [v, qShiftField] using hftc y
  rw [hrep]
  have hjoint : AEStronglyMeasurable
      (Function.uncurry (fun (y : Plane) (t : ℝ) => fderiv ℝ u (y + t • v) v))
      ((cellμ c).prod (volume.restrict (Ioc (0 : ℝ) 1))) := hdc.aestronglyMeasurable
  have hm := NonUniqueEuler.Conv.eLpNorm_integral_le (μ := cellμ c)
    (ν := volume.restrict (Ioc (0 : ℝ) 1)) hjoint
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  refine hm.trans ?_
  have hperD : IsPeriodic c (fun y => fderiv ℝ u y v) := by
    intro y
    have hfun : (fun x => u (x + ((c, 0) : Plane))) = u := funext hu.periodic
    have hcomp := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := y) ((c, 0) : Plane)
    have heq := congrArg (fun D => D v) hcomp
    rw [hfun] at heq
    have hcoord : (y.1 + c, y.2) = y + ((c, 0) : Plane) := by
      ext <;> simp
    rw [hcoord]
    exact heq.symm
  have hshiftNorm (t : ℝ) :
      eLpNorm (fun y => fderiv ℝ u (y + t • v) v) 2 (cellμ c) =
        eLpNorm (fun y => fderiv ℝ u y v) 2 (cellμ c) := by
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hpTop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h := Cyl.eLpNorm_cell_comp_sub hc hperD hp0 hpTop (-t • v)
    have harg : (fun y => fderiv ℝ u (y + t • v) v) =
        (fun y => fderiv ℝ u (y - (-t • v)) v) := by
      funext y
      apply congrArg (fun w : Plane => fderiv ℝ u w v)
      congr 1
      ext <;> simp <;> ring
    rw [harg]
    exact h
  have hdir : (fun y => fderiv ℝ u y v) = h • Cyl.partialQ u := by
    funext y
    change fderiv ℝ u y (h, 0) = h • Cyl.partialQ u y
    rw [Cyl.partialQ_eq_fderiv (hu.smooth.differentiable (by simp))]
    have hv : (h, (0 : ℝ)) = h • ((1 : ℝ), (0 : ℝ)) := by ext <;> simp
    rw [hv, map_smul]
  simp_rw [hshiftNorm, hdir, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]


/-- The axial difference quotient of a smooth periodic field is controlled in cell `L²`
by its axial derivative. This is the cylinder version of the FTC/Minkowski translation
modulus; periodicity is used only to preserve the centered-cell derivative norm under shifts. -/
theorem eLpNorm_etaShift_sub_le_of_cylSmooth {c h : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    eLpNorm (fun z => etaShiftField h u z - u z) 2 (cellμ c) ≤
      ENNReal.ofReal |h| * eLpNorm (Cyl.partialEta u) 2 (cellμ c) := by
  let v : Plane := (0, h)
  have hdc : Continuous (fun p : Plane × ℝ => fderiv ℝ u (p.1 + p.2 • v) v) := by
    exact ((hu.smooth.continuous_fderiv (by simp)).comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hftc : ∀ y, u (y + v) - u y =
      ∫ t, fderiv ℝ u (y + t • v) v ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro y
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (f := fun t : ℝ => u (y + t • v))
      (f' := fun t => fderiv ℝ u (y + t • v) v)
      (fun t _ => by
        have hline : HasDerivAt (fun t : ℝ => y + t • v) v t := by
          simpa using ((hasDerivAt_id t).smul_const v).const_add y
        exact ((hu.smooth.differentiable (by simp)) (y + t • v)).hasFDerivAt.comp_hasDerivAt t hline)
      ((hdc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le zero_le_one] at h
    simpa [v, etaShiftField] using h.symm
  have hrep : (fun y => etaShiftField h u y - u y) =
      fun y => ∫ t, fderiv ℝ u (y + t • v) v ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
    funext y
    simpa [v, etaShiftField] using hftc y
  rw [hrep]
  have hjoint : AEStronglyMeasurable
      (Function.uncurry (fun (y : Plane) (t : ℝ) => fderiv ℝ u (y + t • v) v))
      ((cellμ c).prod (volume.restrict (Ioc (0 : ℝ) 1))) := hdc.aestronglyMeasurable
  have hm := NonUniqueEuler.Conv.eLpNorm_integral_le (μ := cellμ c)
    (ν := volume.restrict (Ioc (0 : ℝ) 1)) hjoint
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  refine hm.trans ?_
  have hperD : IsPeriodic c (fun y => fderiv ℝ u y v) := by
    intro y
    have hfun : (fun x => u (x + ((c, 0) : Plane))) = u := funext hu.periodic
    have hcomp := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := y) ((c, 0) : Plane)
    have heq := congrArg (fun D => D v) hcomp
    rw [hfun] at heq
    have hcoord : (y.1 + c, y.2) = y + ((c, 0) : Plane) := by
      ext <;> simp
    rw [hcoord]
    exact heq.symm
  have hshiftNorm (t : ℝ) :
      eLpNorm (fun y => fderiv ℝ u (y + t • v) v) 2 (cellμ c) =
        eLpNorm (fun y => fderiv ℝ u y v) 2 (cellμ c) := by
    have hp0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have hpTop : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h := Cyl.eLpNorm_cell_comp_sub hc hperD hp0 hpTop (-t • v)
    have harg : (fun y => fderiv ℝ u (y + t • v) v) =
        (fun y => fderiv ℝ u (y - (-t • v)) v) := by
      funext y
      apply congrArg (fun w : Plane => fderiv ℝ u w v)
      congr 1
      ext <;> simp <;> ring
    rw [harg]
    exact h
  have hdir : (fun y => fderiv ℝ u y v) = h • Cyl.partialEta u := by
    funext y
    change fderiv ℝ u y (0, h) = h • Cyl.partialEta u y
    rw [Cyl.partialEta_eq_fderiv (hu.smooth.differentiable (by simp))]
    have hv : ((0 : ℝ), h) = h • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [hv, map_smul]
  simp_rw [hshiftNorm, hdir, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.eLpNorm_qShift_sub_le_of_cylSmooth
#print axioms UnforcedLeray.TrainB.eLpNorm_etaShift_sub_le_of_cylSmooth
