import UnforcedLeray.Short.PartIIb.Sub.T12
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzExists.Pair

/-!
# Truncation of a periodic `L^r` field

`truncF n F` retracts the values of `F` onto the closed ball of radius `n` (radial retraction
`rhoCut`) and cuts off to the strip `|η| ≤ n`. The result is `c`-periodic whenever `F` is, is
bounded by `n`, is supported in a strip of finite `avgμ c`-measure, hence lies in every `L^p`,
and converges to `F` in `L^r(avgμ c)` by dominated convergence.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Radial retraction of `CMerid` onto the closed ball of radius `n`. -/
def rhoCut (n : ℝ) (v : CMerid) : CMerid := min 1 (n / ‖v‖) • v

theorem rhoCut_norm_le_norm {n : ℝ} (hn : 0 ≤ n) (v : CMerid) : ‖rhoCut n v‖ ≤ ‖v‖ := by
  unfold rhoCut
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_min zero_le_one (div_nonneg hn (norm_nonneg _)))]
  exact mul_le_of_le_one_left (norm_nonneg _) (min_le_left _ _)

theorem rhoCut_norm_le {n : ℝ} (hn : 0 ≤ n) (v : CMerid) : ‖rhoCut n v‖ ≤ n := by
  unfold rhoCut
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_min zero_le_one (div_nonneg hn (norm_nonneg _)))]
  rcases eq_or_ne ‖v‖ 0 with h | h
  · rw [h, mul_zero]
    exact hn
  · calc min 1 (n / ‖v‖) * ‖v‖ ≤ (n / ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ = n := div_mul_cancel₀ n h

theorem rhoCut_eq_of_norm_le {n : ℝ} {v : CMerid} (h : ‖v‖ ≤ n) : rhoCut n v = v := by
  unfold rhoCut
  rcases eq_or_ne ‖v‖ 0 with h0 | h0
  · have hv : v = 0 := norm_eq_zero.mp h0
    simp [hv]
  · have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h1 : 1 ≤ n / ‖v‖ := (one_le_div hpos).2 h
    rw [min_eq_left h1, one_smul]

theorem measurable_rhoCut (n : ℝ) : Measurable (rhoCut n) := by
  unfold rhoCut
  fun_prop

/-- The strip `|η| ≤ n` of the plane. -/
def strip (n : ℕ) : Set (ℝ × ℝ) := univ ×ˢ Icc (-(n : ℝ)) (n : ℝ)

theorem measurableSet_strip (n : ℕ) : MeasurableSet (strip n) :=
  MeasurableSet.univ.prod measurableSet_Icc

theorem mem_strip {n : ℕ} {z : ℝ × ℝ} : z ∈ strip n ↔ |z.2| ≤ (n : ℝ) := by
  simp [strip, abs_le]

/-- The truncation `F_n` of `F`. -/
def truncF (n : ℕ) (F : ℝ × ℝ → CMerid) : ℝ × ℝ → CMerid :=
  (strip n).indicator (fun z => rhoCut (n : ℝ) (F z))

theorem truncF_periodic {c : ℝ} {F : ℝ × ℝ → CMerid} (hF : ∀ z : ℝ × ℝ, F (z.1 + c, z.2) = F z)
    (n : ℕ) : ∀ z : ℝ × ℝ, truncF n F (z.1 + c, z.2) = truncF n F z := by
  classical
  intro z
  simp only [truncF, Set.indicator_apply, mem_strip, hF z]

theorem norm_truncF_le (n : ℕ) (F : ℝ × ℝ → CMerid) (z : ℝ × ℝ) :
    ‖truncF n F z‖ ≤ ‖F z‖ := by
  classical
  unfold truncF
  rw [Set.indicator_apply]
  split_ifs
  · exact rhoCut_norm_le_norm (Nat.cast_nonneg n) _
  · simp

theorem norm_truncF_le_const (n : ℕ) (F : ℝ × ℝ → CMerid) (z : ℝ × ℝ) :
    ‖truncF n F z‖ ≤ (n : ℝ) := by
  classical
  unfold truncF
  rw [Set.indicator_apply]
  split_ifs
  · exact rhoCut_norm_le (Nat.cast_nonneg n) _
  · simp

theorem truncF_eq_of_le {n : ℕ} {F : ℝ × ℝ → CMerid} {z : ℝ × ℝ}
    (h : ‖F z‖ + |z.2| ≤ (n : ℝ)) : truncF n F z = F z := by
  unfold truncF
  have hmem : z ∈ strip n := mem_strip.2 (by linarith [norm_nonneg (F z)])
  rw [Set.indicator_of_mem hmem]
  exact rhoCut_eq_of_norm_le (by linarith [abs_nonneg z.2])

theorem tendsto_truncF_pointwise (F : ℝ × ℝ → CMerid) (z : ℝ × ℝ) :
    Tendsto (fun n : ℕ => truncF n F z) atTop (𝓝 (F z)) := by
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖F z‖ + |z.2|⌉₊) (fun n hn => ?_)
  apply truncF_eq_of_le
  have h1 := Nat.le_ceil (‖F z‖ + |z.2|)
  have h2 : ((⌈‖F z‖ + |z.2|⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

theorem memLp_truncF {c : ℝ} (hc : 0 < c) (n : ℕ) {F : ℝ × ℝ → CMerid}
    (hF : AEStronglyMeasurable F (UnforcedLeray.Cyl.avgμ c)) (p : ℝ≥0∞) :
    MemLp (truncF n F) p (UnforcedLeray.Cyl.avgμ c) := by
  have hmeas : AEStronglyMeasurable (fun z => rhoCut (n : ℝ) (F z))
      (UnforcedLeray.Cyl.avgμ c) :=
    ((measurable_rhoCut (n : ℝ)).comp_aemeasurable hF.aemeasurable).aestronglyMeasurable
  unfold truncF
  refine (memLp_indicator_iff_restrict (measurableSet_strip n)).2 ?_
  haveI : IsFiniteMeasure ((UnforcedLeray.Cyl.avgμ c).restrict (strip n)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact avgμ_strip_lt_top (L := (n : ℝ)) hc⟩
  refine MemLp.of_bound hmeas.restrict (n : ℝ) (Filter.Eventually.of_forall fun z => ?_)
  exact rhoCut_norm_le (Nat.cast_nonneg n) (F z)

theorem aestronglyMeasurable_truncF (n : ℕ) {F : ℝ × ℝ → CMerid} {μ : Measure (ℝ × ℝ)}
    (hF : AEStronglyMeasurable F μ) : AEStronglyMeasurable (truncF n F) μ := by
  unfold truncF
  exact (((measurable_rhoCut (n : ℝ)).comp_aemeasurable hF.aemeasurable).aestronglyMeasurable).indicator
    (measurableSet_strip n)

/-- `F_n → F` in `L^r(avgμ c)` by dominated convergence. -/
theorem tendsto_truncF_Lr {c r : ℝ} (hc : 0 < c) (hr : 1 < r) {F : ℝ × ℝ → CMerid}
    (hF : MemLp F (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c)) :
    Tendsto (fun n : ℕ => eLpNorm (truncF n F - F) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c))
      atTop (𝓝 0) := by
  have hr0 : 0 < r := by linarith
  set μ := UnforcedLeray.Cyl.avgμ c with hμ
  have hfin : ∫⁻ z, ‖F z‖ₑ ^ r ∂μ < ⊤ := by
    have := hF.integrable_enorm_rpow (ENNReal.ofReal_pos.2 hr0).ne' ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hr0.le] at this
    exact this.2
  have hpt : ∀ (n : ℕ) (z : ℝ × ℝ), ‖truncF n F z - F z‖ₑ ≤ 2 * ‖F z‖ₑ := by
    intro n z
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    have h1 : ‖truncF n F z - F z‖ ≤ 2 * ‖F z‖ := by
      have := norm_sub_le (truncF n F z) (F z)
      have := norm_truncF_le n F z
      linarith
    calc ENNReal.ofReal ‖truncF n F z - F z‖ ≤ ENNReal.ofReal (2 * ‖F z‖) :=
          ENNReal.ofReal_le_ofReal h1
      _ = 2 * ENNReal.ofReal ‖F z‖ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hbound_fin : ∫⁻ z, (2 * ‖F z‖ₑ) ^ r ∂μ < ⊤ := by
    have : ∀ z, (2 * ‖F z‖ₑ) ^ r = (2 : ℝ≥0∞) ^ r * ‖F z‖ₑ ^ r := fun z =>
      ENNReal.mul_rpow_of_nonneg _ _ hr0.le
    simp_rw [this]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr0.le ENNReal.ofNat_ne_top)]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hr0.le ENNReal.ofNat_ne_top) hfin
  have hmeasF : ∀ n, AEMeasurable (fun z => ‖truncF n F z - F z‖ₑ ^ r) μ := by
    intro n
    exact ((((aestronglyMeasurable_truncF n hF.1).sub hF.1)).enorm).pow_const r
  have hlim : ∀ z, Tendsto (fun n : ℕ => ‖truncF n F z - F z‖ₑ ^ r) atTop (𝓝 0) := by
    intro z
    have h1 : Tendsto (fun n : ℕ => ‖truncF n F z - F z‖ₑ) atTop (𝓝 ‖(0 : CMerid)‖ₑ) :=
      (continuous_enorm.tendsto 0).comp (tendsto_sub_nhds_zero_iff.2 (tendsto_truncF_pointwise F z))
    rw [enorm_zero] at h1
    have h2 : Tendsto (fun n : ℕ => ‖truncF n F z - F z‖ₑ ^ r) atTop (𝓝 ((0 : ℝ≥0∞) ^ r)) :=
      ((ENNReal.continuous_rpow_const (y := r)).tendsto 0).comp h1
    rwa [ENNReal.zero_rpow_of_pos hr0] at h2
  have key : Tendsto (fun n : ℕ => ∫⁻ z, ‖truncF n F z - F z‖ₑ ^ r ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun (n : ℕ) (z : ℝ × ℝ) => ‖truncF n F z - F z‖ₑ ^ r)
      (f := fun _ => (0 : ℝ≥0∞)) (bound := fun z => (2 * ‖F z‖ₑ) ^ r)
      hmeasF
      (fun n => Filter.Eventually.of_forall fun z =>
        ENNReal.rpow_le_rpow (hpt n z) hr0.le)
      hbound_fin.ne
      (Filter.Eventually.of_forall hlim)
    simpa using this
  have hrt : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hr0).ne'
    ENNReal.ofReal_ne_top, hrt, Pi.sub_apply]
  have h3 := ((ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0).comp key
  rwa [ENNReal.zero_rpow_of_pos (one_div_pos.2 hr0)] at h3

end UnforcedLeray.Short.IIb
