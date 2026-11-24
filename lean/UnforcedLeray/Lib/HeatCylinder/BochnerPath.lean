import UnforcedLeray.Lib.HeatCylinder.Gradient
import UnforcedLeray.Lib.BochnerTime.Slices
import UnforcedLeray.Units.B0431
import UnforcedLeray.Lib.ParabolicCylinder.KernelIntegral

/-!
# Bochner measurability of cylinder heat paths

Joint almost-everywhere strong measurability on time times one cell gives an almost-everywhere
strongly measurable path into the cell `L²` space. This is the product-to-Bochner slice theorem
applied to the actual Gaussian `heatDiv` output.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open Set
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

/-- Concrete Gaussian-gradient constant in the cylinder `L²` estimate. -/
def heatDivL2Coeff (θ : ℝ) : ℝ :=
  4 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹

/-- At positive viscosity and heat age, the Gaussian coefficient is exactly the standard
`(2/√π) ν^(-1/2) age^(-1/2)` singular kernel. -/
theorem heatDivL2Coeff_eq_singular {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) :
    heatDivL2Coeff (ν * τ) = (2 / Real.sqrt Real.pi) *
      (ν ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 / 2 : ℝ))) := by
  have hsqrt : Real.sqrt (4 * Real.pi * 1 * (ν * τ)) =
      2 * Real.sqrt Real.pi * Real.sqrt ν * Real.sqrt τ := by
    rw [show 4 * Real.pi * 1 * (ν * τ) = (4 * Real.pi) * (ν * τ) by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 4 * Real.pi),
      Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)),
      Real.sqrt_mul hν.le]
    have h4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
    rw [h4]
    ring
  rw [heatDivL2Coeff, hsqrt,
    UnforcedLeray.B0431.rpow_neg_half_eq hν,
    UnforcedLeray.B0431.rpow_neg_half_eq hτ]
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hνs : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.2 hν).ne'
  have hτs : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.2 hτ).ne'
  field_simp [hπ, hνs, hτs]
  <;> ring

/-- The Gaussian coefficient has the exact square-root integral on an open time interval. -/
theorem integral_heatDivL2Coeff_Ioo {ν a s : ℝ} (hν : 0 < ν) (has : a < s) :
    ∫ r in Ioo a s, heatDivL2Coeff (ν * (s - r)) =
      (4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) * (s - a) ^ (1 / 2 : ℝ) := by
  calc
    ∫ r in Ioo a s, heatDivL2Coeff (ν * (s - r)) =
        ∫ r in Ioo a s,
        (2 / Real.sqrt Real.pi) *
            (ν ^ (-(1 / 2 : ℝ)) * (s - r) ^ (-(1 / 2 : ℝ))) := by
      refine setIntegral_congr_ae measurableSet_Ioo ?_
      have hEqRest : (fun r : ℝ => heatDivL2Coeff (ν * (s - r))) =ᵐ[
          volume.restrict (Ioo a s)] (fun r => (2 / Real.sqrt Real.pi) *
            (ν ^ (-(1 / 2 : ℝ)) * (s - r) ^ (-(1 / 2 : ℝ)))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        rw [heatDivL2Coeff_eq_singular hν (sub_pos.mpr hr.2)]
      have hEqVol := (ae_restrict_iff' measurableSet_Ioo).1 hEqRest
      filter_upwards [hEqVol] with r hr hmem
      exact hr hmem
    _ = ∫ r in a..s,
        (2 / Real.sqrt Real.pi) *
          (ν ^ (-(1 / 2 : ℝ)) * (s - r) ^ (-(1 / 2 : ℝ))) :=
      by rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le has.le]
    _ = (4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) *
        (s - a) ^ (1 / 2 : ℝ) :=
      UnforcedLeray.ParabolicCylinder.integral_heatDiv_smoothing_factor hν

/-- Integrability of the actual Gaussian smoothing coefficient on every finite age interval. -/
theorem integrable_heatDivL2Coeff_Ioo {ν a s : ℝ} (hν : 0 < ν) (has : a < s) :
    Integrable (fun r : ℝ => heatDivL2Coeff (ν * (s - r)))
      (volume.restrict (Ioo a s)) := by
  have hker := UnforcedLeray.Infra.VolterraEvolution.intervalIntegrable_kernel s a s
  have hprof : IntervalIntegrable
      (fun r : ℝ => (2 / Real.sqrt Real.pi) *
        (ν ^ (-(1 / 2 : ℝ)) * (s - r) ^ (-(1 / 2 : ℝ)))) volume a s := by
    convert hker.const_mul ((2 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ))) using 1 <;>
      ext r <;> ring
  have hprofOn : Integrable (fun r : ℝ => (2 / Real.sqrt Real.pi) *
      (ν ^ (-(1 / 2 : ℝ)) * (s - r) ^ (-(1 / 2 : ℝ))))
      (volume.restrict (Ioo a s)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le has.le).1 hprof
  have hEq : (fun r : ℝ => heatDivL2Coeff (ν * (s - r))) =ᵐ[
      volume.restrict (Ioo a s)]
      (fun r => (2 / Real.sqrt Real.pi) *
        (ν ^ (-(1 / 2 : ℝ)) * (s - r) ^ (-(1 / 2 : ℝ)))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    rw [heatDivL2Coeff_eq_singular hν (sub_pos.mpr hr.2)]
  exact hprofOn.congr hEq.symm

/-- Joint AEStronglyMeasurable output on time times a cylinder cell induces an AEStronglyMeasurable
path of slice classes in `L²(cellMeasure c)`. The actual Lp-valued path can be represented using
`BochnerTime.toPathLq`. -/
theorem aestronglyMeasurable_toPathL2_of_joint
    {c : ℝ} {E : Type*} [NormedAddCommGroup E] [TopologicalSpace.SeparableSpace E]
    {f : ℝ × Plane → E}
    (hf : AEStronglyMeasurable f ((volume : Measure ℝ).prod (cellMeasure c))) :
    AEStronglyMeasurable
      (UnforcedLeray.BochnerTime.toPathLq 2 (cellMeasure c) f) (volume : Measure ℝ) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  rcases hf with ⟨g, hg, hfg⟩
  have hpath := UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq
    (τ := ℝ) (α := Plane) (F := E) (q := 2) (μ := cellMeasure c)
    hg
  have hslices : ∀ᵐ t : ℝ ∂volume,
      (fun z => f (t, z)) =ᵐ[cellMeasure c] fun z => g (t, z) :=
    Measure.ae_ae_of_ae_prod hfg
  have hcongr : UnforcedLeray.BochnerTime.toPathLq 2 (cellMeasure c) f =ᵐ[volume]
      UnforcedLeray.BochnerTime.toPathLq 2 (cellMeasure c) g := by
    filter_upwards [hslices] with t ht
    exact UnforcedLeray.BochnerTime.toPathLq_congr_ae ht
  exact hpath.aestronglyMeasurable.congr hcongr.symm

/-- If every time slice of a jointly AEStronglyMeasurable field is in cell `L²`, the path formed
by those slice `Lp` classes is AEStronglyMeasurable. -/
theorem aestronglyMeasurable_toLpPath_of_joint
    {c : ℝ} {E : Type*} [NormedAddCommGroup E] [TopologicalSpace.SeparableSpace E]
    {f : ℝ × Plane → E}
    (hf : AEStronglyMeasurable f ((volume : Measure ℝ).prod (cellMeasure c)))
    (hmem : ∀ t : ℝ, MemLp (fun z => f (t, z)) 2 (cellMeasure c)) :
    AEStronglyMeasurable
      (fun t : ℝ => (hmem t).toLp (fun z => f (t, z))) (volume : Measure ℝ) := by
  have hpath := aestronglyMeasurable_toPathL2_of_joint hf
  have heq : (fun t : ℝ => (hmem t).toLp (fun z => f (t, z))) =
      UnforcedLeray.BochnerTime.toPathLq 2 (cellMeasure c) f := by
    funext t
    exact (UnforcedLeray.BochnerTime.toPathLq_of_memLp (hmem t)).symm
  rw [heq]
  exact hpath

/-- A uniformly bounded cell-`L²` tensor path automatically satisfies the weighted integrability
condition for its actual Gaussian heatDiv path. -/
theorem integrable_heatDivL2_majorant_of_uniform_bound {c ν s a M : ℝ} (hc : 0 < c)
    (hν : 0 < ν) (has : a < s)
    {T : ℝ × Plane → Plane × Plane} (hTmeas : Measurable T)
    (hTmem : ∀ t : ℝ, MemLp (fun z => T (t, z)) 2 (cellMeasure c))
    (hUbound : ∀ r ∈ Ioo a s,
      ‖(hTmem r).toLp (fun z => T (r, z))‖ ≤ M) :
    Integrable
      (fun r : ℝ => heatDivL2Coeff (ν * (s - r)) *
        ‖(hTmem r).toLp (fun z => T (r, z))‖)
      (volume.restrict (Ioo a s)) := by
  have hcoeff := integrable_heatDivL2Coeff_Ioo hν has
  have hTjoint : AEStronglyMeasurable T
      ((volume : Measure ℝ).prod (cellMeasure c)) :=
    hTmeas.aestronglyMeasurable.mono_ac
      (Measure.AbsolutelyContinuous.rfl.prod (UnforcedLeray.B0284.cellMeasure_ac c))
  have hU : AEStronglyMeasurable
      (fun r : ℝ => (hTmem r).toLp (fun z => T (r, z))) (volume : Measure ℝ) :=
    aestronglyMeasurable_toLpPath_of_joint hTjoint hTmem
  have hU' : AEStronglyMeasurable
      (fun r : ℝ => (hTmem r).toLp (fun z => T (r, z)))
      (volume.restrict (Ioo a s)) := hU.mono_ac Measure.absolutelyContinuous_restrict
  have htarget : AEStronglyMeasurable
      (fun r : ℝ => heatDivL2Coeff (ν * (s - r)) *
        ‖(hTmem r).toLp (fun z => T (r, z))‖)
      (volume.restrict (Ioo a s)) := hcoeff.aestronglyMeasurable.mul hU'.norm
  refine (hcoeff.const_mul M).mono' htarget ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hcoeffNonneg : 0 ≤ heatDivL2Coeff (ν * (s - r)) := by
    unfold heatDivL2Coeff
    exact mul_nonneg (by norm_num) (inv_nonneg.2 (Real.sqrt_nonneg _))
  calc
    ‖heatDivL2Coeff (ν * (s - r)) *
        ‖(hTmem r).toLp (fun z => T (r, z))‖‖ =
      heatDivL2Coeff (ν * (s - r)) *
        ‖(hTmem r).toLp (fun z => T (r, z))‖ :=
          Real.norm_of_nonneg (mul_nonneg hcoeffNonneg (norm_nonneg _))
    _ ≤ heatDivL2Coeff (ν * (s - r)) * M :=
      mul_le_mul_of_nonneg_left (hUbound r hr) hcoeffNonneg
    _ = M * heatDivL2Coeff (ν * (s - r)) := by ring

/-- Slice `L²` membership of the actual heatDiv output, including the zero branch for
nonpositive heat ages. -/
theorem memLp_heatDiv_timePath {c ν s : ℝ} (hc : 0 < c)
    {T : ℝ × Plane → Plane × Plane} (hTmeas : Measurable T)
    (hTper : ∀ t : ℝ, IsQPeriodic c (fun z => T (t, z)))
    (hTmem : ∀ t : ℝ, MemLp (fun z => T (t, z)) 2 (cellMeasure c)) (t : ℝ) :
    MemLp (fun z => UnforcedLeray.B0296.heatDiv (ν * (s - t)) (fun y => T (t, y)) z)
      2 (cellMeasure c) := by
  by_cases hθ : 0 < ν * (s - t)
  · exact UnforcedLeray.B0296.memLp_heatDiv hc hθ (hTper t)
      (hTmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top (hTmem t).eLpNorm_ne_top
  · simp [UnforcedLeray.B0296.heatDiv, hθ]

/-- The actual slice heatDiv operator has the Gaussian-gradient norm bound as an estimate between
the cell `L²` classes. This is the real-norm form needed to dominate the Bochner path. -/
theorem norm_heatDivL2_slice_le {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hper : IsQPeriodic c T)
    (hTmeas : AEStronglyMeasurable T volume) (hTmem : MemLp T 2 (cellMeasure c))
    (hOut : MemLp (UnforcedLeray.B0296.heatDiv θ T) 2 (cellMeasure c)) :
    ‖hOut.toLp (UnforcedLeray.B0296.heatDiv θ T)‖ ≤
      heatDivL2Coeff θ * ‖hTmem.toLp T‖ := by
  have hbound := heatDiv_L2_smoothing hc hθ hper hTmeas
  have hfinite : (ENNReal.ofReal (heatDivL2Coeff θ) *
      eLpNorm T 2 (cellMeasure c)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTmem.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite hbound
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by unfold heatDivL2Coeff; positivity)] at hreal
  change (eLpNorm (UnforcedLeray.B0296.heatDiv θ T) 2 (cellMeasure c)).toReal ≤
    heatDivL2Coeff θ * (eLpNorm T 2 (cellMeasure c)).toReal at hreal
  rw [Lp.norm_toLp]
  calc
    (eLpNorm (UnforcedLeray.B0296.heatDiv θ T) 2 (cellMeasure c)).toReal ≤
        heatDivL2Coeff θ *
          (eLpNorm T 2 (cellMeasure c)).toReal := hreal
    _ = heatDivL2Coeff θ * ‖hTmem.toLp T‖ := by
      rw [Lp.norm_toLp]

/-- The actual time-dependent cylinder `heatDiv` output is a strongly measurable `L²`-valued
path whenever the tensor path is jointly measurable, periodic at every time, and has finite
cell-`L²` slices. Positive heat ages use the Gaussian smoothing theorem; nonpositive ages give
the definitionally zero output. -/
theorem aestronglyMeasurable_heatDivL2_path {c ν s : ℝ} (hc : 0 < c)
    {T : ℝ × Plane → Plane × Plane} (hTmeas : Measurable T)
    (hTper : ∀ t : ℝ, IsQPeriodic c (fun z => T (t, z)))
    (hTmem : ∀ t : ℝ, MemLp (fun z => T (t, z)) 2 (cellMeasure c)) :
    AEStronglyMeasurable
      (fun t : ℝ => (memLp_heatDiv_timePath hc hTmeas hTper hTmem t).toLp
          (fun z => UnforcedLeray.B0296.heatDiv (ν * (s - t)) (fun y => T (t, y)) z))
      (volume : Measure ℝ) := by
  apply aestronglyMeasurable_toLpPath_of_joint
    (aestronglyMeasurable_heatDiv_timePath hTmeas)

/-- Bochner integrability of the concrete heatDiv `L²` path on an open time interval, under the
explicit Gaussian singular-kernel majorant. This is the integrability condition required for the
Duhamel integral; no semigroup-valued integrand is assumed. -/
theorem integrable_heatDivL2_path_of_weighted {c ν s a : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {T : ℝ × Plane → Plane × Plane} (hTmeas : Measurable T)
    (hTper : ∀ t : ℝ, IsQPeriodic c (fun z => T (t, z)))
    (hTmem : ∀ t : ℝ, MemLp (fun z => T (t, z)) 2 (cellMeasure c))
    (hdom : Integrable
      (fun r : ℝ =>
        heatDivL2Coeff (ν * (s - r)) *
          ‖(hTmem r).toLp (fun z => T (r, z))‖)
      (volume.restrict (Ioo a s))) :
    Integrable
      (fun r : ℝ => (memLp_heatDiv_timePath hc hTmeas hTper hTmem r).toLp
        (fun z => UnforcedLeray.B0296.heatDiv (ν * (s - r))
          (fun y => T (r, y)) z))
      (volume.restrict (Ioo a s)) := by
  let U : ℝ → Lp (Plane × Plane) 2 (cellMeasure c) :=
    fun r => (hTmem r).toLp (fun z => T (r, z))
  let H : ℝ → Lp Plane 2 (cellMeasure c) :=
    fun r => (memLp_heatDiv_timePath hc hTmeas hTper hTmem r).toLp
      (UnforcedLeray.B0296.heatDiv (ν * (s - r)) (fun y => T (r, y)))
  have hHm : AEStronglyMeasurable H (volume.restrict (Ioo a s)) := by
    exact (aestronglyMeasurable_heatDivL2_path hc hTmeas hTper hTmem).mono_ac
      Measure.absolutelyContinuous_restrict
  have hbound : ∀ᵐ r ∂(volume.restrict (Ioo a s)), ‖H r‖ ≤
      heatDivL2Coeff (ν * (s - r)) * ‖U r‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hθ : 0 < ν * (s - r) := mul_pos hν (sub_pos.mpr hr.2)
    have hsliceMeas : AEStronglyMeasurable (fun z => T (r, z)) volume :=
      (hTmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hmemOut := UnforcedLeray.B0296.memLp_heatDiv hc hθ (hTper r) hsliceMeas
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top (hTmem r).eLpNorm_ne_top
    have hslice := norm_heatDivL2_slice_le hc hθ (hTper r) hsliceMeas (hTmem r) hmemOut
    have hOutEq : H r = hmemOut.toLp
        (UnforcedLeray.B0296.heatDiv (ν * (s - r)) (fun z => T (r, z))) := by
      apply Lp.ext
      filter_upwards [] with z
      rfl
    rw [hOutEq]
    change ‖hmemOut.toLp
        (UnforcedLeray.B0296.heatDiv (ν * (s - r)) (fun z => T (r, z)))‖ ≤
      heatDivL2Coeff (ν * (s - r)) * ‖(hTmem r).toLp (fun z => T (r, z))‖
    exact hslice
  have hnorm : Integrable (fun r => ‖H r‖) (volume.restrict (Ioo a s)) := by
    refine hdom.mono' hHm.norm ?_
    filter_upwards [hbound] with r hr
    calc
      ‖‖H r‖‖ = ‖H r‖ := by simp
      _ ≤ heatDivL2Coeff (ν * (s - r)) * ‖U r‖ := hr
      _ = heatDivL2Coeff (ν * (s - r)) *
          ‖(hTmem r).toLp (fun z => T (r, z))‖ := by rfl
  exact (integrable_norm_iff hHm).1 hnorm

/-- Norm of the actual Gaussian heatDiv Duhamel integral, bounded by its explicit singular-time
majorant. The output is the Bochner integral in the cylinder `L²` space. -/
theorem norm_integral_heatDivL2_path_le {c ν s a : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {T : ℝ × Plane → Plane × Plane} (hTmeas : Measurable T)
    (hTper : ∀ t : ℝ, IsQPeriodic c (fun z => T (t, z)))
    (hTmem : ∀ t : ℝ, MemLp (fun z => T (t, z)) 2 (cellMeasure c))
    (hdom : Integrable
      (fun r : ℝ => heatDivL2Coeff (ν * (s - r)) *
          ‖(hTmem r).toLp (fun z => T (r, z))‖)
      (volume.restrict (Ioo a s))) :
    ‖∫ r, (memLp_heatDiv_timePath hc hTmeas hTper hTmem r).toLp
        (fun z => UnforcedLeray.B0296.heatDiv (ν * (s - r)) (fun y => T (r, y)) z)
        ∂(volume.restrict (Ioo a s))‖ ≤
      ∫ r, heatDivL2Coeff (ν * (s - r)) *
        ‖(hTmem r).toLp (fun z => T (r, z))‖ ∂(volume.restrict (Ioo a s)) := by
  have _hInt := integrable_heatDivL2_path_of_weighted hc hν hTmeas hTper hTmem hdom
  have hbound : ∀ᵐ r ∂(volume.restrict (Ioo a s)),
      ‖(memLp_heatDiv_timePath hc hTmeas hTper hTmem r).toLp
          (fun z => UnforcedLeray.B0296.heatDiv (ν * (s - r))
            (fun y => T (r, y)) z)‖ ≤
        heatDivL2Coeff (ν * (s - r)) * ‖(hTmem r).toLp (fun z => T (r, z))‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hθ : 0 < ν * (s - r) := mul_pos hν (sub_pos.mpr hr.2)
    have hsliceMeas : AEStronglyMeasurable (fun z => T (r, z)) volume :=
      (hTmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    have hmemOut := UnforcedLeray.B0296.memLp_heatDiv hc hθ (hTper r) hsliceMeas
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top (hTmem r).eLpNorm_ne_top
    have hslice := norm_heatDivL2_slice_le hc hθ (hTper r) hsliceMeas (hTmem r) hmemOut
    exact hslice
  exact norm_integral_le_of_norm_le hdom hbound

/-- Constant-input-norm form of the concrete Gaussian Duhamel bound. The exact time integral
turns the singular kernel into `4 / √π · √((s-a)/ν)`. -/
theorem norm_integral_heatDivL2_path_le_of_bound {c ν s a M : ℝ} (hc : 0 < c)
    (hν : 0 < ν) (has : a < s)
    {T : ℝ × Plane → Plane × Plane} (hTmeas : Measurable T)
    (hTper : ∀ t : ℝ, IsQPeriodic c (fun z => T (t, z)))
    (hTmem : ∀ t : ℝ, MemLp (fun z => T (t, z)) 2 (cellMeasure c))
    (hUbound : ∀ r ∈ Ioo a s,
      ‖(hTmem r).toLp (fun z => T (r, z))‖ ≤ M) :
    ‖∫ r, (memLp_heatDiv_timePath hc hTmeas hTper hTmem r).toLp
        (fun z => UnforcedLeray.B0296.heatDiv (ν * (s - r)) (fun y => T (r, y)) z)
        ∂(volume.restrict (Ioo a s))‖ ≤
      (4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) *
        (s - a) ^ (1 / 2 : ℝ) * M := by
  have hdom := integrable_heatDivL2_majorant_of_uniform_bound hc hν has
    hTmeas hTmem hUbound
  have _hIntH := integrable_heatDivL2_path_of_weighted hc hν hTmeas hTper hTmem hdom
  have hIntCoeff := integrable_heatDivL2Coeff_Ioo hν has
  have hupper : Integrable (fun r : ℝ => M * heatDivL2Coeff (ν * (s - r)))
      (volume.restrict (Ioo a s)) := hIntCoeff.const_mul M
  have hpoint : (fun r : ℝ => heatDivL2Coeff (ν * (s - r)) *
      ‖(hTmem r).toLp (fun z => T (r, z))‖) ≤ᵐ[volume.restrict (Ioo a s)]
      fun r => M * heatDivL2Coeff (ν * (s - r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hcoeff : 0 ≤ heatDivL2Coeff (ν * (s - r)) := by
      unfold heatDivL2Coeff
      exact mul_nonneg (by norm_num)
        (inv_nonneg.2 (Real.sqrt_nonneg _))
    calc
      heatDivL2Coeff (ν * (s - r)) *
          ‖(hTmem r).toLp (fun z => T (r, z))‖ ≤
        heatDivL2Coeff (ν * (s - r)) * M :=
          mul_le_mul_of_nonneg_left (hUbound r hr) hcoeff
      _ = M * heatDivL2Coeff (ν * (s - r)) := by ring
  have hmono := integral_mono_ae hdom hupper hpoint
  calc
    ‖∫ r, (memLp_heatDiv_timePath hc hTmeas hTper hTmem r).toLp
        (fun z => UnforcedLeray.B0296.heatDiv (ν * (s - r))
          (fun y => T (r, y)) z) ∂(volume.restrict (Ioo a s))‖ ≤
      ∫ r, heatDivL2Coeff (ν * (s - r)) *
        ‖(hTmem r).toLp (fun z => T (r, z))‖ ∂(volume.restrict (Ioo a s)) :=
        norm_integral_heatDivL2_path_le hc hν hTmeas hTper hTmem hdom
    _ ≤ ∫ r, M * heatDivL2Coeff (ν * (s - r)) ∂(volume.restrict (Ioo a s)) := hmono
    _ = M * ∫ r, heatDivL2Coeff (ν * (s - r)) ∂(volume.restrict (Ioo a s)) := by
      rw [integral_const_mul]
    _ = M * ((4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) *
        (s - a) ^ (1 / 2 : ℝ)) := by
      rw [integral_heatDivL2Coeff_Ioo hν has]
    _ = (4 / Real.sqrt Real.pi) * ν ^ (-(1 / 2 : ℝ)) *
        (s - a) ^ (1 / 2 : ℝ) * M := by ring

end UnforcedLeray.HeatCylinder
