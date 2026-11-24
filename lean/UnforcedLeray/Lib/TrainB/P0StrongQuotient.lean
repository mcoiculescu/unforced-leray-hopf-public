import UnforcedLeray.Lib.TrainB.P0Quotient
import UnforcedLeray.Lib.TrainB.P0W1

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open scoped Topology
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- The horizontal translation quotient of a smooth cylinder field converges strongly to its
classical derivative, with a quantitative error controlled by the next derivative. The estimate
is on the centered cell and uses only periodic cell translation bounds. -/
theorem eLpNorm_qDifferenceQuotient_error_le_of_cylSmooth {c h : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) (hh : h ≠ 0) :
    eLpNorm (fun z => h⁻¹ • (qShiftField h u z - u z) - Cyl.partialQ u z)
      2 (cellμ c) ≤ ENNReal.ofReal |h| *
        eLpNorm (Cyl.partialQ (Cyl.partialQ u)) 2 (cellμ c) := by
  let v : Plane := (h, 0)
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  have hdc : Continuous (fun p : Plane × ℝ =>
      fderiv ℝ u (p.1 + p.2 • v) v) := by
    exact ((hu.smooth.continuous_fderiv (by simp)).comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hftc : ∀ y, u (y + v) - u y =
      ∫ t, fderiv ℝ u (y + t • v) v ∂ν := by
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
    simpa [ν] using h.symm
  have hderiv : ∀ z, fderiv ℝ u z v = h • Cyl.partialQ u z := by
    intro z
    change fderiv ℝ u z (h, 0) = h • Cyl.partialQ u z
    rw [Cyl.partialQ_eq_fderiv (hu.smooth.differentiable (by simp))]
    have hv : (h, (0 : ℝ)) = h • ((1 : ℝ), (0 : ℝ)) := by ext <;> simp
    rw [hv, map_smul]
  have hpart : Sob.IsCylSmooth c (Cyl.partialQ u) := by
    have hdir := hu.dir ((1 : ℝ), (0 : ℝ))
    have heq : Cyl.partialQ u = fun z => fderiv ℝ u z ((1 : ℝ), (0 : ℝ)) := by
      funext z
      exact Cyl.partialQ_eq_fderiv (hu.smooth.differentiable (by simp)) z
    simpa only [heq] using hdir
  have hpartCont : Continuous (Cyl.partialQ u) := hpart.smooth.continuous
  have hrep : (fun z => h⁻¹ • (qShiftField h u z - u z) - Cyl.partialQ u z) =
      fun z => ∫ t, (Cyl.partialQ u (z + t • v) - Cyl.partialQ u z) ∂ν := by
    funext z
    rw [show qShiftField h u z = u (z + v) by rfl, hftc z]
    rw [show (fun t : ℝ => fderiv ℝ u (z + t • v) v) =
      fun t => h • Cyl.partialQ u (z + t • v) by funext t; exact hderiv _]
    have hcont1 : Continuous (fun t : ℝ => Cyl.partialQ u (z + t • v)) :=
      hpartCont.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hInt : Integrable (fun t : ℝ => Cyl.partialQ u (z + t • v)) ν := by
      change IntegrableOn (fun t : ℝ => Cyl.partialQ u (z + t • v)) (Ioc 0 1) volume
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (hcont1.intervalIntegrable 0 1)
    have hIntConst : Integrable (fun _ : ℝ => Cyl.partialQ u z) ν := integrable_const _
    rw [integral_smul]
    have hν : ν Set.univ = 1 := by
      simp [ν, Measure.restrict_apply, MeasurableSet.univ, Real.volume_Ioc]
    have hνreal : ν.real Set.univ = 1 := by simp [Measure.real, hν]
    rw [integral_sub hInt hIntConst, integral_const, hνreal]
    simp [smul_smul, hh]
  rw [hrep]
  have hjoint : AEStronglyMeasurable
      (Function.uncurry (fun (z : Plane) (t : ℝ) =>
        Cyl.partialQ u (z + t • v) - Cyl.partialQ u z))
      ((cellμ c).prod ν) := by
    have hmap : Continuous (fun p : Plane × ℝ => p.1 + p.2 • v) :=
      continuous_fst.add (continuous_snd.smul continuous_const)
    exact ((hpartCont.comp hmap).sub
      (hpartCont.comp continuous_fst)).aestronglyMeasurable
  have hm := NonUniqueEuler.Conv.eLpNorm_integral_le (μ := cellμ c)
    (ν := ν) hjoint (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  refine hm.trans ?_
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      eLpNorm (fun z => Cyl.partialQ u (z + t • v) - Cyl.partialQ u z)
        2 (cellμ c) ≤ ENNReal.ofReal |h| *
          eLpNorm (Cyl.partialQ (Cyl.partialQ u)) 2 (cellμ c) := by
    intro t ht
    have ht' : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1.le]
      exact ht.2
    have hq := eLpNorm_qShift_sub_le_of_cylSmooth (c := c) (h := h * t) hc
      (u := Cyl.partialQ u) hpart
    have harg : (fun z => Cyl.partialQ u (z + t • v) - Cyl.partialQ u z) =
        fun z => qShiftField (h * t) (Cyl.partialQ u) z - Cyl.partialQ u z := by
      funext z
      simp [qShiftField, v]
      congr 1 <;> ext <;> simp <;> ring
    rw [harg]
    have habs : |h * t| ≤ |h| := by
      rw [abs_mul]
      nlinarith [abs_nonneg h, abs_nonneg t]
    exact hq.trans (mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal habs) (by positivity))
  have hconst : ∫⁻ t, ENNReal.ofReal |h| *
      eLpNorm (Cyl.partialQ (Cyl.partialQ u)) 2 (cellμ c) ∂ν =
      ENNReal.ofReal |h| * eLpNorm (Cyl.partialQ (Cyl.partialQ u)) 2 (cellμ c) := by
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  refine (lintegral_mono_ae ?_).trans_eq hconst
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hbound t ht

/-- The axial version of the strong difference-quotient error estimate on the centered cell. -/
theorem eLpNorm_etaDifferenceQuotient_error_le_of_cylSmooth {c h : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) (hh : h ≠ 0) :
    eLpNorm (fun z => h⁻¹ • (etaShiftField h u z - u z) - Cyl.partialEta u z)
      2 (cellμ c) ≤ ENNReal.ofReal |h| *
        eLpNorm (Cyl.partialEta (Cyl.partialEta u)) 2 (cellμ c) := by
  let v : Plane := (0, h)
  let ν := volume.restrict (Ioc (0 : ℝ) 1)
  have hdc : Continuous (fun p : Plane × ℝ =>
      fderiv ℝ u (p.1 + p.2 • v) v) := by
    exact ((hu.smooth.continuous_fderiv (by simp)).comp
      (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hftc : ∀ y, u (y + v) - u y =
      ∫ t, fderiv ℝ u (y + t • v) v ∂ν := by
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
    simpa [ν] using h.symm
  have hderiv : ∀ z, fderiv ℝ u z v = h • Cyl.partialEta u z := by
    intro z
    change fderiv ℝ u z (0, h) = h • Cyl.partialEta u z
    rw [Cyl.partialEta_eq_fderiv (hu.smooth.differentiable (by simp))]
    have hv : ((0 : ℝ), h) = h • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [hv, map_smul]
  have hpart : Sob.IsCylSmooth c (Cyl.partialEta u) := by
    have hdir := hu.dir ((0 : ℝ), (1 : ℝ))
    have heq : Cyl.partialEta u = fun z => fderiv ℝ u z ((0 : ℝ), (1 : ℝ)) := by
      funext z
      exact Cyl.partialEta_eq_fderiv (hu.smooth.differentiable (by simp)) z
    simpa only [heq] using hdir
  have hpartCont : Continuous (Cyl.partialEta u) := hpart.smooth.continuous
  have hrep : (fun z => h⁻¹ • (etaShiftField h u z - u z) - Cyl.partialEta u z) =
      fun z => ∫ t, (Cyl.partialEta u (z + t • v) - Cyl.partialEta u z) ∂ν := by
    funext z
    rw [show etaShiftField h u z = u (z + v) by rfl, hftc z]
    rw [show (fun t : ℝ => fderiv ℝ u (z + t • v) v) =
      fun t => h • Cyl.partialEta u (z + t • v) by funext t; exact hderiv _]
    have hcont1 : Continuous (fun t : ℝ => Cyl.partialEta u (z + t • v)) :=
      hpartCont.comp (continuous_const.add (continuous_id.smul continuous_const))
    have hInt : Integrable (fun t : ℝ => Cyl.partialEta u (z + t • v)) ν := by
      change IntegrableOn (fun t : ℝ => Cyl.partialEta u (z + t • v)) (Ioc 0 1) volume
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (hcont1.intervalIntegrable 0 1)
    have hIntConst : Integrable (fun _ : ℝ => Cyl.partialEta u z) ν := integrable_const _
    rw [integral_smul]
    have hν : ν Set.univ = 1 := by
      simp [ν, Measure.restrict_apply, MeasurableSet.univ, Real.volume_Ioc]
    have hνreal : ν.real Set.univ = 1 := by simp [Measure.real, hν]
    rw [integral_sub hInt hIntConst, integral_const, hνreal]
    simp [smul_smul, hh]
  rw [hrep]
  have hjoint : AEStronglyMeasurable
      (Function.uncurry (fun (z : Plane) (t : ℝ) =>
        Cyl.partialEta u (z + t • v) - Cyl.partialEta u z))
      ((cellμ c).prod ν) := by
    have hmap : Continuous (fun p : Plane × ℝ => p.1 + p.2 • v) :=
      continuous_fst.add (continuous_snd.smul continuous_const)
    exact ((hpartCont.comp hmap).sub
      (hpartCont.comp continuous_fst)).aestronglyMeasurable
  have hm := NonUniqueEuler.Conv.eLpNorm_integral_le (μ := cellμ c)
    (ν := ν) hjoint (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  refine hm.trans ?_
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      eLpNorm (fun z => Cyl.partialEta u (z + t • v) - Cyl.partialEta u z)
        2 (cellμ c) ≤ ENNReal.ofReal |h| *
          eLpNorm (Cyl.partialEta (Cyl.partialEta u)) 2 (cellμ c) := by
    intro t ht
    have ht' : |t| ≤ 1 := by
      rw [abs_of_nonneg ht.1.le]
      exact ht.2
    have hq := eLpNorm_etaShift_sub_le_of_cylSmooth (c := c) (h := h * t) hc
      (u := Cyl.partialEta u) hpart
    have harg : (fun z => Cyl.partialEta u (z + t • v) - Cyl.partialEta u z) =
        fun z => etaShiftField (h * t) (Cyl.partialEta u) z - Cyl.partialEta u z := by
      funext z
      simp [etaShiftField, v]
      congr 1 <;> ext <;> simp <;> ring
    rw [harg]
    have habs : |h * t| ≤ |h| := by
      rw [abs_mul]
      nlinarith [abs_nonneg h, abs_nonneg t]
    exact hq.trans (mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal habs) (by positivity))
  have hconst : ∫⁻ t, ENNReal.ofReal |h| *
      eLpNorm (Cyl.partialEta (Cyl.partialEta u)) 2 (cellμ c) ∂ν =
      ENNReal.ofReal |h| * eLpNorm (Cyl.partialEta (Cyl.partialEta u)) 2 (cellμ c) := by
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  refine (lintegral_mono_ae ?_).trans_eq hconst
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hbound t ht

/-- The horizontal smooth translation quotient converges in centered-cell L² to the classical
derivative. The second derivative is finite because the representative is smooth and vanishes
outside a bounded axial strip. -/
theorem tendsto_eLpNorm_qDifferenceQuotient_error_zero {c : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    Tendsto (fun h : ℝ => eLpNorm
      (fun z => h⁻¹ • (qShiftField h u z - u z) - Cyl.partialQ u z)
      2 (cellμ c)) (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) := by
  have hpart : Sob.IsCylSmooth c (Cyl.partialQ u) := by
    have hdir := hu.dir ((1 : ℝ), (0 : ℝ))
    have heq : Cyl.partialQ u = fun z => fderiv ℝ u z ((1 : ℝ), (0 : ℝ)) := by
      funext z
      exact Cyl.partialQ_eq_fderiv (hu.smooth.differentiable (by simp)) z
    simpa only [heq] using hdir
  have hpart2 : Sob.IsCylSmooth c (Cyl.partialQ (Cyl.partialQ u)) := by
    have hdir := hpart.dir ((1 : ℝ), (0 : ℝ))
    have heq : Cyl.partialQ (Cyl.partialQ u) =
        fun z => fderiv ℝ (Cyl.partialQ u) z ((1 : ℝ), (0 : ℝ)) := by
      funext z
      exact Cyl.partialQ_eq_fderiv (hpart.smooth.differentiable (by simp)) z
    simpa only [heq] using hdir
  have hmem : MemLp (Cyl.partialQ (Cyl.partialQ u)) 2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    exact hpart2.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hfinite : eLpNorm (Cyl.partialQ (Cyl.partialQ u)) 2 (cellμ c) ≠ ⊤ := hmem.2.ne
  have habs : Tendsto (fun h : ℝ => |h|)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) :=
    by simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmul' := ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_ofReal habs) (Or.inr hfinite)
  have hmul : Tendsto (fun h : ℝ => ENNReal.ofReal |h| *
      eLpNorm (Cyl.partialQ (Cyl.partialQ u)) 2 (cellμ c))
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) :=
    by simpa using hmul'
  have hlower : (fun _ : ℝ => (0 : ℝ≥0∞)) ≤ᶠ[nhdsWithin 0 {h : ℝ | h ≠ 0}]
      (fun h => eLpNorm
        (fun z => h⁻¹ • (qShiftField h u z - u z) - Cyl.partialQ u z) 2 (cellμ c)) := by
    filter_upwards [] with h
    exact zero_le
  have hupper : (fun h => eLpNorm
      (fun z => h⁻¹ • (qShiftField h u z - u z) - Cyl.partialQ u z) 2 (cellμ c)) ≤ᶠ[
      nhdsWithin 0 {h : ℝ | h ≠ 0}]
      (fun h => ENNReal.ofReal |h| *
        eLpNorm (Cyl.partialQ (Cyl.partialQ u)) 2 (cellμ c)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact eLpNorm_qDifferenceQuotient_error_le_of_cylSmooth hc hu hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hmul hlower hupper

/-- The axial smooth translation quotient converges in centered-cell L² to the classical
derivative. -/
theorem tendsto_eLpNorm_etaDifferenceQuotient_error_zero {c : ℝ} (hc : 0 < c)
    {u : Plane → Vec2} (hu : Sob.IsCylSmooth c u) :
    Tendsto (fun h : ℝ => eLpNorm
      (fun z => h⁻¹ • (etaShiftField h u z - u z) - Cyl.partialEta u z)
      2 (cellμ c)) (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) := by
  have hpart : Sob.IsCylSmooth c (Cyl.partialEta u) := by
    have hdir := hu.dir ((0 : ℝ), (1 : ℝ))
    have heq : Cyl.partialEta u = fun z => fderiv ℝ u z ((0 : ℝ), (1 : ℝ)) := by
      funext z
      exact Cyl.partialEta_eq_fderiv (hu.smooth.differentiable (by simp)) z
    simpa only [heq] using hdir
  have hpart2 : Sob.IsCylSmooth c (Cyl.partialEta (Cyl.partialEta u)) := by
    have hdir := hpart.dir ((0 : ℝ), (1 : ℝ))
    have heq : Cyl.partialEta (Cyl.partialEta u) =
        fun z => fderiv ℝ (Cyl.partialEta u) z ((0 : ℝ), (1 : ℝ)) := by
      funext z
      exact Cyl.partialEta_eq_fderiv (hpart.smooth.differentiable (by simp)) z
    simpa only [heq] using hdir
  have hmem : MemLp (Cyl.partialEta (Cyl.partialEta u)) 2 (cellμ c) := by
    rw [← vecH1_measure_eq_cell c]
    exact hpart2.memLp (Cyl.ρwW c ^ (0 : ℝ)) 2
  have hfinite : eLpNorm (Cyl.partialEta (Cyl.partialEta u)) 2 (cellμ c) ≠ ⊤ := hmem.2.ne
  have habs : Tendsto (fun h : ℝ => |h|)
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) :=
    by simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmul' := ENNReal.Tendsto.mul_const
      (ENNReal.tendsto_ofReal habs) (Or.inr hfinite)
  have hmul : Tendsto (fun h : ℝ => ENNReal.ofReal |h| *
      eLpNorm (Cyl.partialEta (Cyl.partialEta u)) 2 (cellμ c))
      (nhdsWithin 0 {h : ℝ | h ≠ 0}) (𝓝 0) :=
    by simpa using hmul'
  have hlower : (fun _ : ℝ => (0 : ℝ≥0∞)) ≤ᶠ[nhdsWithin 0 {h : ℝ | h ≠ 0}]
      (fun h => eLpNorm
        (fun z => h⁻¹ • (etaShiftField h u z - u z) - Cyl.partialEta u z) 2 (cellμ c)) := by
    filter_upwards [] with h
    exact zero_le
  have hupper : (fun h => eLpNorm
      (fun z => h⁻¹ • (etaShiftField h u z - u z) - Cyl.partialEta u z) 2 (cellμ c)) ≤ᶠ[
      nhdsWithin 0 {h : ℝ | h ≠ 0}]
      (fun h => ENNReal.ofReal |h| *
        eLpNorm (Cyl.partialEta (Cyl.partialEta u)) 2 (cellμ c)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact eLpNorm_etaDifferenceQuotient_error_le_of_cylSmooth hc hu hh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hmul hlower hupper

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.eLpNorm_qDifferenceQuotient_error_le_of_cylSmooth
#print axioms UnforcedLeray.TrainB.eLpNorm_etaDifferenceQuotient_error_le_of_cylSmooth
#print axioms UnforcedLeray.TrainB.tendsto_eLpNorm_qDifferenceQuotient_error_zero
#print axioms UnforcedLeray.TrainB.tendsto_eLpNorm_etaDifferenceQuotient_error_zero
